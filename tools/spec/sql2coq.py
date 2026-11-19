#!/usr/bin/env python3
"""Spec-driven conformance tests.

Replays the SQL statements of a test script together with the expected results recorded by
a real database (the `.result` files of the OceanBase `mysql_test` suite), translates the
SELECT statements which are in the fragment formalised in `SqlFull.v` to Coq, and writes a
Coq file which checks that the formal semantics, under a given dialect, gives the recorded
results.

A statement which is not in the supported fragment is skipped. When it modifies a table (DDL,
INSERT ... SELECT, UPDATE, DELETE, ...) the table is marked as unreliable, and the queries
which read it are skipped, so that a skipped statement never makes a case wrong.

Usage: sql2coq.py RESULT_FILE... > Cases.v
"""
import re
import sys
import json

# ----------------------------------------------------------------------------------------
# Lexer
# ----------------------------------------------------------------------------------------

KEYWORDS = set("""select from where group by having order limit offset distinct all as and or not xor is
null true false unknown in like between case when then else end union intersect except minus join inner
left right full outer cross on using natural asc desc div mod cast signed unsigned char decimal binary
escape exists interval over partition rows range""".split())


class Skip(Exception):
    pass


def tokenize(s):
    toks = []
    i = 0
    n = len(s)
    while i < n:
        c = s[i]
        if c.isspace():
            i += 1
        elif c == '-' and s.startswith('--', i) and (i + 2 >= n or s[i + 2] in ' \t'):
            while i < n and s[i] != '\n':
                i += 1
        elif s.startswith('/*', i):
            j = s.find('*/', i + 2)
            if j < 0:
                raise Skip('comment')
            i = j + 2
        elif c in "'\"":
            q = c
            j = i + 1
            buf = []
            while True:
                if j >= n:
                    raise Skip('unterminated string')
                if s[j] == '\\' and j + 1 < n:
                    e = s[j + 1]
                    m = {'n': '\n', 't': '\t', '0': '\0', '\\': '\\', "'": "'", '"': '"', 'r': '\r', 'b': '\b', '%': '\\%', '_': '\\_'}
                    buf.append(m.get(e, e))
                    j += 2
                elif s[j] == q:
                    if j + 1 < n and s[j + 1] == q:
                        buf.append(q)
                        j += 2
                    else:
                        break
                else:
                    buf.append(s[j])
                    j += 1
            toks.append(('str', ''.join(buf)))
            i = j + 1
        elif c == '`':
            j = s.find('`', i + 1)
            toks.append(('id', s[i + 1:j]))
            i = j + 1
        elif c.isdigit() or (c == '.' and i + 1 < n and s[i + 1].isdigit()):
            m = re.match(r'(\d+\.?\d*|\.\d+)([eE][+-]?\d+)?', s[i:])
            txt = m.group(0)
            if m.group(2):
                raise Skip('exponent literal')
            if i + len(txt) < n and (s[i + len(txt)].isalpha() or s[i + len(txt)] == '_'):
                raise Skip('identifier starting with digits')
            toks.append(('num', txt))
            i += len(txt)
        elif c.isalpha() or c == '_' or c == '$':
            m = re.match(r'[A-Za-z_$][A-Za-z_0-9$]*', s[i:])
            w = m.group(0)
            toks.append(('kw' if w.lower() in KEYWORDS else 'id', w))
            i += len(w)
        elif s.startswith(('<=>', ), i):
            toks.append(('op', '<=>'))
            i += 3
        elif s[i:i + 2] in ('<=', '>=', '<>', '!=', '||', '&&', ':='):
            toks.append(('op', s[i:i + 2]))
            i += 2
        elif c in '+-*/%=<>(),.;@':
            toks.append(('op', c))
            i += 1
        else:
            raise Skip('char %r' % c)
    return toks


# ----------------------------------------------------------------------------------------
# Parser
# ----------------------------------------------------------------------------------------

class P:
    def __init__(self, toks):
        self.t = toks
        self.i = 0

    def peek(self, k=0):
        return self.t[self.i + k] if self.i + k < len(self.t) else ('eof', '')

    def kw(self, *ws):
        t = self.peek()
        return t[0] in ('kw', 'id') and t[1].lower() in ws

    def eat_kw(self, *ws):
        if self.kw(*ws):
            self.i += 1
            return True
        return False

    def need_kw(self, w):
        if not self.eat_kw(w):
            raise Skip('expected ' + w)

    def op(self, o):
        t = self.peek()
        return t == ('op', o)

    def eat_op(self, o):
        if self.op(o):
            self.i += 1
            return True
        return False

    def need_op(self, o):
        if not self.eat_op(o):
            raise Skip('expected ' + o)

    # ---- queries
    def query(self):
        q = self.select_or_paren()
        while self.kw('union', 'intersect', 'except', 'minus'):
            op = self.peek()[1].lower()
            self.i += 1
            allq = self.eat_kw('all')
            if not allq:
                self.eat_kw('distinct')
            r = self.select_or_paren()
            q = ('setop', op, allq, q, r)
        order = None
        if self.kw('order'):
            order = self.order_by()
        limit = None
        if self.kw('limit'):
            limit = self.limit()
        if order is not None or limit is not None:
            q = ('orderq', q, order or [], limit)
        return q

    def select_or_paren(self):
        if self.eat_op('('):
            q = self.query()
            self.need_op(')')
            return q
        return self.select()

    def limit(self):
        self.need_kw('limit')
        a = self.int_lit()
        off = 0
        if self.eat_op(','):
            off = a
            a = self.int_lit()
        elif self.eat_kw('offset'):
            off = self.int_lit()
        return (off, a)

    def int_lit(self):
        t = self.peek()
        if t[0] != 'num' or '.' in t[1]:
            raise Skip('limit')
        self.i += 1
        return int(t[1])

    def order_by(self):
        self.need_kw('order')
        self.need_kw('by')
        items = []
        while True:
            e = self.expr()
            d = 'asc'
            if self.eat_kw('desc'):
                d = 'desc'
            else:
                self.eat_kw('asc')
            if self.kw('nulls'):
                raise Skip('nulls clause')
            items.append((e, d))
            if not self.eat_op(','):
                break
        return items

    def select(self):
        self.need_kw('select')
        distinct = False
        if self.eat_kw('distinct'):
            distinct = True
        elif self.eat_kw('all'):
            pass
        items = []
        while True:
            if self.eat_op('*'):
                items.append(('star', None))
            else:
                e = self.expr()
                alias = None
                if self.eat_kw('as'):
                    alias = self.ident()
                elif self.peek()[0] == 'id' and not self.kw('from', 'where', 'group', 'order', 'limit', 'having', 'union', 'intersect', 'except', 'minus'):
                    alias = self.ident()
                elif self.peek()[0] == 'str':
                    raise Skip('string alias')
                items.append(('item', e, alias))
            if not self.eat_op(','):
                break
        frm = []
        if self.eat_kw('from'):
            frm = self.from_clause()
        where = self.expr() if self.eat_kw('where') else None
        group = None
        if self.kw('group'):
            self.i += 1
            self.need_kw('by')
            group = []
            while True:
                group.append(self.expr())
                if not self.eat_op(','):
                    break
            if self.kw('with'):
                raise Skip('with rollup')
        having = self.expr() if self.eat_kw('having') else None
        if self.kw('window', 'for', 'lock', 'into', 'procedure'):
            raise Skip('clause')
        return ('select', distinct, items, frm, where, group, having)

    def ident(self):
        t = self.peek()
        if t[0] in ('id', 'kw'):
            self.i += 1
            return t[1]
        raise Skip('identifier')

    def from_clause(self):
        item = self.table_ref()
        while True:
            if self.eat_op(','):
                item = ('join', 'cross', item, self.table_ref(), None)
                continue
            jt = None
            if self.kw('natural'):
                raise Skip('natural join')
            if self.eat_kw('cross'):
                self.need_kw('join')
                jt = 'cross'
            elif self.eat_kw('inner'):
                self.need_kw('join')
                jt = 'inner'
            elif self.kw('left', 'right', 'full'):
                jt = self.peek()[1].lower()
                self.i += 1
                self.eat_kw('outer')
                self.need_kw('join')
            elif self.eat_kw('join'):
                jt = 'inner'
            else:
                break
            r = self.table_ref()
            cond = None
            if self.eat_kw('on'):
                cond = self.expr()
            elif self.kw('using'):
                raise Skip('using')
            item = ('join', jt, item, r, cond)
        return item

    def table_ref(self):
        if self.op('('):
            save = self.i
            self.i += 1
            if not self.kw('select'):
                self.i = save
                raise Skip('parenthesised table reference')
            q = self.query()
            self.need_op(')')
            self.eat_kw('as')
            alias = self.ident()
            cols = None
            if self.eat_op('('):
                cols = []
                while True:
                    cols.append(self.ident())
                    if not self.eat_op(','):
                        break
                self.need_op(')')
            return ('derived', q, alias, cols)
        name = self.ident()
        if self.op('.'):
            raise Skip('qualified table')
        alias = name
        if self.eat_kw('as'):
            alias = self.ident()
        elif self.peek()[0] == 'id' and not self.kw('join', 'inner', 'left', 'right', 'full', 'cross', 'natural', 'on', 'where', 'group', 'order', 'limit', 'having', 'union', 'intersect', 'except', 'minus', 'using', 'use', 'force', 'ignore', 'partition'):
            alias = self.ident()
        if self.kw('use', 'force', 'ignore', 'partition'):
            raise Skip('index hint')
        return ('table', name, alias)

    # ---- expressions (precedence climbing)
    def expr(self):
        return self.e_or()

    def e_or(self):
        l = self.e_xor()
        while self.eat_kw('or') or self.eat_op('||'):
            l = ('bin', 'or' if self.t[self.i - 1][1] in ('or', 'OR', 'Or') or self.t[self.i - 1][1].lower() == 'or' else '||', l, self.e_xor())
        return l

    def e_xor(self):
        l = self.e_and()
        while self.eat_kw('xor'):
            l = ('bin', 'xor', l, self.e_and())
        return l

    def e_and(self):
        l = self.e_not()
        while self.eat_kw('and') or self.eat_op('&&'):
            l = ('bin', 'and', l, self.e_not())
        return l

    def e_not(self):
        if self.eat_kw('not'):
            return ('not', self.e_not())
        return self.e_pred()

    def e_pred(self):
        l = self.e_add()
        while True:
            neg = False
            save = self.i
            if self.kw('not') and self.peek(1)[1].lower() in ('in', 'like', 'between', 'regexp', 'rlike'):
                self.i += 1
                neg = True
            if self.eat_kw('is'):
                n = self.eat_kw('not')
                if self.eat_kw('null'):
                    l = ('is', 'null', n, l)
                elif self.eat_kw('true'):
                    l = ('is', 'true', n, l)
                elif self.eat_kw('false'):
                    l = ('is', 'false', n, l)
                elif self.eat_kw('unknown'):
                    l = ('is', 'unknown', n, l)
                else:
                    raise Skip('is')
            elif self.eat_kw('in'):
                self.need_op('(')
                if self.kw('select'):
                    q = self.query()
                    self.need_op(')')
                    l = ('insub', neg, [l] if l[0] != 'row' else l[1], q)
                    continue
                items = [self.expr()]
                while self.eat_op(','):
                    items.append(self.expr())
                self.need_op(')')
                l = ('in', neg, l, items)
            elif self.eat_kw('like'):
                r = self.e_add()
                if self.kw('escape'):
                    raise Skip('escape')
                if self.kw('binary'):
                    raise Skip('like binary')
                l = ('like', neg, l, r)
            elif self.eat_kw('between'):
                lo = self.e_add()
                self.need_kw('and')
                hi = self.e_add()
                l = ('between', neg, l, lo, hi)
            elif self.kw('regexp', 'rlike'):
                raise Skip('regexp')
            else:
                if neg:
                    self.i = save
                    break
                t = self.peek()
                if t[0] == 'op' and t[1] in ('=', '<>', '!=', '<', '<=', '>', '>=', '<=>'):
                    self.i += 1
                    if self.kw('any', 'some', 'all'):
                        quant = 'all' if self.peek()[1].lower() == 'all' else 'any'
                        self.i += 1
                        self.need_op('(')
                        if not self.kw('select'):
                            raise Skip('quantified list')
                        q = self.query()
                        self.need_op(')')
                        l = ('quant', t[1], quant, [l] if l[0] != 'row' else l[1], q)
                        continue
                    l = ('cmp', t[1], l, self.e_add())
                else:
                    break
        return l

    def e_add(self):
        l = self.e_mul()
        while True:
            t = self.peek()
            if t[0] == 'op' and t[1] in ('+', '-'):
                self.i += 1
                l = ('bin', t[1], l, self.e_mul())
            else:
                return l

    def e_mul(self):
        l = self.e_unary()
        while True:
            t = self.peek()
            if t[0] == 'op' and t[1] in ('*', '/', '%'):
                self.i += 1
                l = ('bin', t[1], l, self.e_unary())
            elif self.kw('div', 'mod'):
                w = t[1].lower()
                self.i += 1
                l = ('bin', w, l, self.e_unary())
            else:
                return l

    def e_unary(self):
        if self.eat_op('-'):
            e = self.e_unary()
            if e[0] == 'num':
                return ('num', '-' + e[1]) if not e[1].startswith('-') else ('num', e[1][1:])
            return ('neg', e)
        if self.eat_op('+'):
            return self.e_unary()
        if self.eat_kw('not'):
            return ('not', self.e_unary())
        return self.e_primary()

    def e_primary(self):
        t = self.peek()
        if t[0] == 'num':
            self.i += 1
            return ('num', t[1])
        if t[0] == 'str':
            self.i += 1
            if self.peek()[0] == 'str':
                raise Skip('adjacent strings')
            return ('str', t[1])
        if self.eat_op('('):
            if self.kw('select'):
                q = self.query()
                self.need_op(')')
                return ('subq', q)
            e = self.expr()
            if self.op(','):
                items = [e]
                while self.eat_op(','):
                    items.append(self.expr())
                self.need_op(')')
                return ('row', items)
            self.need_op(')')
            return e
        if self.eat_kw('null'):
            return ('null',)
        if self.eat_kw('true'):
            return ('num', '1')
        if self.eat_kw('false'):
            return ('num', '0')
        if self.kw('case'):
            return self.case()
        if self.kw('cast'):
            self.i += 1
            self.need_op('(')
            e = self.expr()
            self.need_kw('as')
            ty = self.peek()[1].lower()
            self.i += 1
            if self.op('('):
                while not self.eat_op(')'):
                    self.i += 1
            if ty == 'unsigned' or ty == 'signed':
                self.eat_kw('integer') or self.eat_kw('int')
            self.need_op(')')
            return ('cast', ty, e)
        if self.kw('exists') and self.peek(1) == ('op', '('):
            self.i += 2
            q = self.query()
            self.need_op(')')
            return ('exists', q)
        if self.kw('interval', 'binary'):
            raise Skip('construct')
        if t[0] in ('id', 'kw'):
            name = t[1]
            self.i += 1
            if self.op('('):
                self.i += 1
                lname = name.lower()
                if self.eat_op('*'):
                    self.need_op(')')
                    if self.kw('over'):
                        raise Skip('window')
                    return ('call', lname, [], True, False)
                distinct = self.eat_kw('distinct')
                if not distinct:
                    self.eat_kw('all')
                args = []
                if not self.op(')'):
                    args.append(self.expr())
                    while self.eat_op(','):
                        args.append(self.expr())
                if self.kw('separator', 'order'):
                    raise Skip('aggregate clause')
                self.need_op(')')
                if self.kw('over'):
                    raise Skip('window')
                return ('call', lname, args, False, distinct)
            if self.eat_op('.'):
                if self.op('*'):
                    raise Skip('qualified star')
                col = self.ident()
                if self.op('.'):
                    raise Skip('db.table.col')
                return ('col', name, col)
            return ('col', None, name)
        raise Skip('primary %r' % (t,))

    def case(self):
        self.need_kw('case')
        subj = None
        if not self.kw('when'):
            subj = self.expr()
        whens = []
        while self.eat_kw('when'):
            c = self.expr()
            self.need_kw('then')
            v = self.expr()
            whens.append((c, v))
        els = ('null',)
        if self.eat_kw('else'):
            els = self.expr()
        self.need_kw('end')
        return ('case', subj, whens, els)


# ----------------------------------------------------------------------------------------
# Schema, data
# ----------------------------------------------------------------------------------------

NUM_TYPES = {'int', 'integer', 'bigint', 'smallint', 'tinyint', 'mediumint'}
DEC_TYPES = {'decimal', 'numeric', 'number', 'float', 'real', 'double', 'float4', 'float8'}
STR_TYPES = {'varchar', 'char', 'text', 'tinytext', 'mediumtext', 'longtext', 'varchar2'}


INT_RANGES = {'tinyint': (-128, 127), 'smallint': (-32768, 32767), 'mediumint': (-8388608, 8388607), 'int': (-2147483648, 2147483647), 'integer': (-2147483648, 2147483647), 'bigint': (-9223372036854775808, 9223372036854775807)}


class Table:
    def __init__(self, name, cols):
        self.limits = []
        self.name = name
        self.cols = cols  # list of (name, kind) kind in 'Z','S','Q'
        self.rows = []
        self.ok = True


def coq_str(s):
    if any(ord(c) < 32 or ord(c) > 126 for c in s):
        raise Skip('non-ascii string')
    return '"' + s.replace('"', '""') + '"'


def attr(kind, name):
    return '(Attr_%s %s)' % ({'Z': 'Z', 'S': 'string', 'Q': 'Q'}[kind], coq_str(name))


def scaled_lit(txt):
    """The unscaled integer and the scale of a decimal literal: 1.50 is (150, 2)."""
    if 'e' in txt.lower():
        raise Skip('float literal')
    neg = txt.startswith('-')
    if neg:
        txt = txt[1:]
    a, b = txt.split('.') if '.' in txt else (txt, '')
    n = int((a or '0') + b)
    return ('-' if neg else '') + str(n), len(b)


def round_to_scale(txt, scale):
    """The unscaled integer of a decimal literal stored in a DECIMAL(p, scale) column: MySQL rounds
    half away from zero."""
    n, s = scaled_lit(txt)
    n = int(n)
    if s <= scale:
        return n * 10 ** (scale - s)
    q, r = divmod(abs(n), 10 ** (s - scale))
    if 2 * r >= 10 ** (s - scale):
        q += 1
    return q if n >= 0 else -q


def dec_lit(txt):
    neg = txt.startswith('-')
    if neg:
        txt = txt[1:]
    if '.' in txt:
        a, b = txt.split('.')
        n = int((a or '0') + b)
        d = 10 ** len(b)
    else:
        n = int(txt)
        d = 1
    return ('-' if neg else '') + str(n), d


def parse_number_prefix(s):
    m = re.match(r'\s*([+-]?)(\d*)(\.?)(\d*)', s)
    sign, a, dot, b = m.groups()
    if not a and not b:
        return 0
    return float(sign + (a or '0') + '.' + (b or '0')) if dot and b else int(sign + (a or '0'))


class Ctx:
    """Name resolution of a SELECT block."""

    def __init__(self, tables, parent=None):
        self.tables = tables  # dict name -> Table
        self.scope = []  # list of (alias, Table)
        self.parent = parent

    def resolve(self, q, c):
        try:
            return self.resolve_here(q, c)
        except Skip as e:
            if self.parent is not None and str(e).startswith('unknown column'):
                return self.parent.resolve(q, c)
            raise

    def resolve_here(self, q, c):
        cands = []
        for alias, t in self.scope:
            if q is not None and q.lower() != alias.lower():
                continue
            for name, kind in t.cols:
                if name.lower() == c.lower():
                    cands.append((alias, name, kind))
        if not cands:
            raise Skip('unknown column ' + c)
        if len(cands) > 1:
            raise Skip('ambiguous column ' + c)
        return cands[0]


# ----------------------------------------------------------------------------------------
# Translation of expressions and queries to Coq
# ----------------------------------------------------------------------------------------

AGGS = {'count', 'sum', 'avg', 'min', 'max', 'group_concat', 'bit_and', 'bit_or', 'var_pop', 'var_samp', 'variance'}
FUNS = {'abs', 'sign', 'floor', 'ceil', 'ceiling', 'round', 'truncate', 'power', 'pow', 'mod', 'greatest', 'least',
        'coalesce', 'ifnull', 'nullif', 'concat', 'concat_ws', 'length', 'char_length', 'upper', 'lower', 'trim',
        'ltrim', 'rtrim', 'reverse', 'substring', 'substr', 'mid', 'left', 'right', 'replace', 'repeat', 'locate',
        'instr', 'ucase', 'lcase', 'character_length', 'ascii', 'space', 'lpad', 'rpad', 'strcmp', 'if'}
ALIAS = {'ucase': 'upper', 'lcase': 'lower', 'character_length': 'char_length'}


class Tr:
    def __init__(self, ctx, qt=None):
        self.ctx = ctx
        self.qt = qt

    def sub(self, q, ncols=None):
        if self.qt is None:
            raise Skip('subquery')
        cq, n, _, _ = self.qt.query(q, self.ctx)
        if ncols is not None and n != ncols:
            raise Skip('subquery arity')
        return cq, n

    def ex(self, e):
        k = e[0]
        if k == 'num':
            txt = e[1]
            if '.' in txt or 'e' in txt.lower():
                n, sc = scaled_lit(txt)
                return '(cst (VD (%s) %d))' % (n, sc)
            return '(int (%s))' % txt
        if k == 'str':
            return '(str %s)' % coq_str(e[1])
        if k == 'null':
            return '(cst NullZ)'
        if k == 'col':
            alias, name, kind = self.ctx.resolve(e[1], e[2])
            return '(col %s)' % attr(kind, alias + '.' + name)
        if k == 'neg':
            return '(fn "neg" [%s])' % self.ex(e[1])
        if k == 'bin':
            op = e[1]
            if op in ('and', 'or', 'xor', '||'):
                return '(e_cond %s)' % self.cond(e) if op in ('and', 'or') and False else \
                       '(fn "%s" [%s; %s])' % (op, self.ex(e[2]), self.ex(e[3]))
            name = {'+': '+', '-': '-', '*': '*', '/': '/', '%': '%', 'div': 'div', 'mod': 'mod'}[op]
            return '(fn "%s" [%s; %s])' % (name, self.ex(e[2]), self.ex(e[3]))
        if k in ('cmp', 'is', 'in', 'like', 'between', 'not', 'exists', 'insub', 'quant'):
            return '(e_cond %s)' % self.cond(e)
        if k == 'subq':
            cq, n = self.sub(e[1], 1)
            return '(e_sub %s)' % cq
        if k == 'row':
            raise Skip('row value')
        if k == 'cast':
            ty = e[1]
            f = {'signed': 'cast_int', 'unsigned': 'cast_int', 'integer': 'cast_int', 'int': 'cast_int', 'bigint': 'cast_int', 'smallint': 'cast_int', 'char': 'cast_string', 'varchar': 'cast_string', 'text': 'cast_string', 'decimal': 'cast_numeric', 'numeric': 'cast_numeric', 'real': 'cast_numeric', 'float': 'cast_numeric', 'double': 'cast_numeric'}.get(ty)
            if f is None:
                raise Skip('cast type ' + ty)
            return '(fn "%s" [%s])' % (f, self.ex(e[2]))
        if k == 'case':
            subj, whens, els = e[1], e[2], e[3]
            out = self.ex(els)
            for c, v in reversed(whens):
                cc = self.cond(('cmp', '=', subj, c)) if subj is not None else self.cond(c)
                out = '(e_case %s %s %s)' % (cc, self.ex(v), out)
            return out
        if k == 'call':
            name, args, star, distinct = e[1], e[2], e[3], e[4]
            if name in AGGS:
                if star:
                    if name != 'count':
                        raise Skip('star')
                    return 'count_star'
                if len(args) != 1:
                    raise Skip('aggregate arity')
                nm = 'group_concat' if name == 'group_concat' else name
                if distinct:
                    return '(agg_distinct "%s" %s)' % (nm, self.ex(args[0]))
                return '(agg "%s" %s)' % (nm, self.ex(args[0]))
            if name in FUNS:
                name = ALIAS.get(name, name)
                if name == 'if':
                    if len(args) != 3:
                        raise Skip('if arity')
                    return '(fn "if" [(e_cond %s); %s; %s])' % (self.cond(args[0]), self.ex(args[1]), self.ex(args[2]))
                return '(fn "%s" [%s])' % (name, '; '.join(self.ex(a) for a in args))
            raise Skip('function ' + name)
        raise Skip('expr ' + k)

    def cond(self, e):
        k = e[0]
        if k == 'bin' and e[1] == 'and':
            return '(c_and %s %s)' % (self.cond(e[2]), self.cond(e[3]))
        if k == 'bin' and e[1] == 'or':
            return '(c_or %s %s)' % (self.cond(e[2]), self.cond(e[3]))
        if k == 'not':
            return '(c_not %s)' % self.cond(e[1])
        if k == 'cmp':
            op = {'=': '=', '<>': '<>', '!=': '<>', '<': '<', '<=': '<=', '>': '>', '>=': '>=', '<=>': '<=>'}[e[1]]
            if e[2][0] == 'row' or e[3][0] == 'row':
                if e[2][0] != 'row' or e[3][0] != 'row' or len(e[2][1]) != len(e[3][1]) or op not in ('=', '<>'):
                    raise Skip('row comparison')
                return '(pred "row%s" [%s])' % (op, '; '.join(self.ex(x) for x in e[2][1] + e[3][1]))
            return '(pred "%s" [%s; %s])' % (op, self.ex(e[2]), self.ex(e[3]))
        if k == 'exists':
            cq, n = self.sub(e[1])
            return '(c_exists %s)' % cq
        if k == 'insub':
            neg, lhs, q = e[1], e[2], e[3]
            cq, n = self.sub(q, len(lhs))
            atts = '; '.join('(Attr_Z "c%d")' % i for i in range(n))
            c = '(c_in [%s] %s [%s])' % ('; '.join(self.ex(x) for x in lhs), cq, atts)
            return '(c_not %s)' % c if neg else c
        if k == 'quant':
            op, qn, lhs, q = e[1], e[2], e[3], e[4]
            if op == '<=>':
                raise Skip('quantified null-safe')
            op = {'=': '=', '<>': '<>', '!=': '<>', '<': '<', '<=': '<=', '>': '>', '>=': '>='}[op]
            cq, n = self.sub(q, len(lhs))
            if len(lhs) != 1:
                raise Skip('quantified row')
            return '(%s "%s" [%s] %s [(Attr_Z "c0")])' % ('c_any' if qn == 'any' else 'c_all', op, self.ex(lhs[0]), cq)
        if k == 'is':
            what, neg, x = e[1], e[2], e[3]
            return '(pred "is %s%s" [%s])' % ('not ' if neg else '', what, self.ex(x))
        if k == 'in':
            return '(pred "%s" [%s])' % ('not in' if e[1] else 'in', '; '.join([self.ex(e[2])] + [self.ex(i) for i in e[3]]))
        if k == 'like':
            return '(pred "%s" [%s; %s])' % ('not like' if e[1] else 'like', self.ex(e[2]), self.ex(e[3]))
        if k == 'between':
            return '(pred "%s" [%s; %s; %s])' % ('not between' if e[1] else 'between', self.ex(e[2]), self.ex(e[3]), self.ex(e[4]))
        return '(c_expr %s)' % self.ex(e)


def has_call(e, name):
    if isinstance(e, list):
        return any(has_call(x, name) for x in e)
    if not isinstance(e, tuple):
        return False
    if e[0] == 'call' and e[1] == name:
        return True
    return any(has_call(x, name) for x in e[1:])


def has_agg(e):
    if not isinstance(e, tuple):
        return False
    if e[0] == 'call' and e[1] in AGGS:
        return True
    return any(has_agg(x) or (isinstance(x, list) and any(has_agg(y) for y in x)) for x in e[1:])


def col_refs(e, out):
    if not isinstance(e, tuple):
        if isinstance(e, list):
            for x in e:
                col_refs(x, out)
        return
    if e[0] == 'col':
        out.append(e)
    for x in e[1:]:
        col_refs(x, out)


def plain_cols(e, out):
    """The columns of an expression which are not inside an aggregate."""
    if isinstance(e, list):
        for x in e:
            plain_cols(x, out)
        return
    if not isinstance(e, tuple):
        return
    if e[0] == 'call' and e[1] in AGGS:
        return
    if e[0] == 'col':
        out.append(e)
        return
    for x in e[1:]:
        plain_cols(x, out)


class QTr:
    def __init__(self, tables):
        self.tables = tables
        self.used = set()

    def table_of(self, name):
        t = self.tables.get(name.lower())
        if t is None:
            raise Skip('unknown table ' + name)
        if not t.ok:
            raise Skip('unreliable table ' + name)
        self.used.add(t.name.lower())
        return t

    def frm(self, f, ctx):
        k = f[0]
        if k == 'table':
            t = self.table_of(f[1])
            alias = f[2]
            if any(a.lower() == alias.lower() for a, _ in ctx.scope):
                raise Skip('duplicate alias')
            ctx.scope.append((alias, t))
            ren = '; '.join('(%s, %s)' % (attr(kd, n), attr(kd, alias + '.' + n)) for n, kd in t.cols)
            return '(from_as (table %s) [%s])' % (coq_str(t.name), ren)
        if k == 'derived':
            q, alias, cols = f[1], f[2], f[3]
            if any(a.lower() == alias.lower() for a, _ in ctx.scope):
                raise Skip('duplicate alias')
            cq, n, _, names = self.query(q, ctx.parent)
            if cols is not None:
                if len(cols) != n:
                    raise Skip('derived arity')
                names = cols
            if len(set(x.lower() for x in names)) != len(names) or any(x is None for x in names):
                raise Skip('derived column names')
            t = Table(alias, [(nm, 'Z') for nm in names])
            ctx.scope.append((alias, t))
            ren = '; '.join('((Attr_Z "c%d"), %s)' % (i, attr('Z', alias + '.' + nm)) for i, nm in enumerate(names))
            return '(from_as %s [%s])' % (cq, ren)
        if k == 'join':
            jt, l, r, c = f[1], f[2], f[3], f[4]
            lt = self.frm(l, ctx)
            rt = self.frm(r, ctx)
            tr = Tr(ctx, self)
            cond = tr.cond(c) if c is not None else 'c_true'
            ty = {'cross': 'J_Inner', 'inner': 'J_Inner', 'left': 'J_Left', 'right': 'J_Right', 'full': 'J_Full'}[jt]
            return '(join %s %s %s %s)' % (ty, lt, rt, cond)
        raise Skip('from')

    def query(self, q, parent=None):
        """Returns (coq query, number of columns, ordered, names of the columns)"""
        k = q[0]
        if k == 'select':
            return self.select(q, None, None, parent)
        if k == 'orderq':
            inner, order, limit = q[1], q[2], q[3]
            if inner[0] == 'select':
                return self.select(inner, order, limit, parent)
            cq, n, _, names = self.query(inner, parent)
            return self.apply_order(cq, n, order, limit) + (names,)
        if k == 'setop':
            op, allq, l, r = q[1], q[2], q[3], q[4]
            lq, ln, _, lnames = self.query(l, parent)
            rq, rn, _, _ = self.query(r, parent)
            if ln != rn:
                raise Skip('set op arity')
            o = {'union': 'Union', 'intersect': 'Inter', 'except': 'Diff', 'minus': 'Diff'}[op]
            return '(set_op_ %s %s %s %s)' % (o, 'Set_All' if allq else 'Set_Distinct', lq, rq), ln, False, lnames
        raise Skip('query')

    def apply_order(self, cq, n, order, limit):
        if order is None and limit is None:
            return cq, n, False
        keys = []
        for e, d in (order or []):
            if e[0] == 'num' and '.' not in e[1] and 1 <= int(e[1]) <= n:
                keys.append('(o_by (col (Attr_Z "c%d")) %s)' % (int(e[1]) - 1, 'Asc' if d == 'asc' else 'Desc'))
            else:
                raise Skip('order by expression over a set operation')
        off, lim = (limit if limit else (0, None))
        return '(order_limit %s [%s] %s %s)' % (cq, '; '.join(keys),
                                                 'None' if off == 0 else '(Some %d%%N)' % off,
                                                 'None' if lim is None else '(Some %d%%N)' % lim), bool(order)

    def select(self, s, order, limit, parent=None):
        _, distinct, items, frm, where, group, having = s
        ctx = Ctx(self.tables, parent)
        fr = []
        if frm:
            fr = [self.frm(frm, ctx)]
        tr = Tr(ctx, self)
        sel = []
        exprs = []
        for it in items:
            if it[0] == 'star':
                if not ctx.scope:
                    raise Skip('star without from')
                for alias, t in ctx.scope:
                    for n, kd in t.cols:
                        exprs.append((('col', alias, n), n))
            else:
                exprs.append((it[1], it[2]))
        names = {}
        outnames = []
        for i, (e, a) in enumerate(exprs):
            if a:
                names[a.lower()] = i
            sel.append('(as_ %s (Attr_Z "c%d"))' % (tr.ex(e), i))
            outnames.append(a if a else (e[2] if e[0] == 'col' else None))
        n = len(exprs)

        def subst(e, alias_first=False):
            """ORDER BY / GROUP BY: aliases and ordinals refer to select items. ORDER BY looks at the
            select list first, GROUP BY at the tables first."""
            if e[0] == 'col' and e[1] is None and e[2].lower() in names:
                if alias_first:
                    return exprs[names[e[2].lower()]][0]
                try:
                    ctx.resolve(None, e[2])
                    return e
                except Skip:
                    return exprs[names[e[2].lower()]][0]
            if e[0] == 'num' and '.' not in e[1] and 1 <= int(e[1]) <= n:
                return exprs[int(e[1]) - 1][0]
            return e
        if limit is not None and not order:
            raise Skip('limit without order by (the rows are implementation defined)')
        if any(has_call(e, 'group_concat') for e, _ in exprs):
            raise Skip('group_concat (the order of the elements is implementation defined)')
        w = tr.cond(where) if where is not None else 'c_true'
        if where is not None and has_agg(where):
            raise Skip('aggregate in where')
        agg_query = any(has_agg(e) for e, _ in exprs) or (having is not None and has_agg(having))
        if group is not None:
            g = '(g_by [%s])' % '; '.join(tr.ex(subst(x)) for x in group)
        else:
            g = 'g_fine'
        h = tr.cond(having) if having is not None else 'c_true'
        order_exprs = [subst(e, True) for e, _ in (order or [])]
        if group is not None or agg_query or any(has_agg(e) for e in order_exprs):
            gexprs = [subst(x) for x in (group or [])]

            def covered(e):
                """a column is not bare when the expression which contains it is a grouping expression"""
                if isinstance(e, list):
                    return all(covered(x) for x in e)
                if not isinstance(e, tuple):
                    return True
                if e in gexprs:
                    return True
                if e[0] == 'call' and e[1] in AGGS:
                    return True
                if e[0] in ('subq', 'exists', 'insub', 'quant'):
                    return True
                if e[0] == 'col':
                    return False
                return all(covered(x) for x in e[1:])
            checks = [e for e, _ in exprs] + order_exprs + ([having] if having is not None else [])
            if not all(covered(e) for e in checks):
                raise Skip('bare column (the value is implementation defined)')
        body = '(select_full %s (s_list [%s]) [%s] %s %s %s)' % (
            'Set_Distinct' if distinct else 'Set_All', '; '.join(sel), '; '.join(fr), w, g, h)
        ordered = False
        if order is not None or limit is not None:
            keys = []
            for (e, d), e2 in zip((order or []), order_exprs):
                # an ORDER BY key which is a select item is the output column
                idx = None
                for i, (x, _) in enumerate(exprs):
                    if x == e2:
                        idx = i
                        break
                kx = '(col (Attr_Z "c%d"))' % idx if idx is not None else tr.ex(e2)
                keys.append('(o_by %s %s)' % (kx, 'Asc' if d == 'asc' else 'Desc'))
            off, lim = (limit if limit else (0, None))
            body = '(order_limit %s [%s] %s %s)' % (body, '; '.join(keys),
                                                     'None' if off == 0 else '(Some %d%%N)' % off,
                                                     'None' if lim is None else '(Some %d%%N)' % lim)
            ordered = bool(order)
        return body, n, ordered, outnames


# ----------------------------------------------------------------------------------------
# Script replay
# ----------------------------------------------------------------------------------------

STMT_START = re.compile(r'^(select|insert|update|delete|create|drop|alter|set|show|explain|desc|describe|truncate|replace|with|begin|commit|rollback|use|analyze|call|prepare|execute|deallocate|source|connect|connection|disconnect|sleep|--|#|let|eval|echo|if|while|}|\{|start|flush|lock|unlock|grant|revoke|rename|load|optimize|checksum|kill|reset|purge|handler|do|\()', re.I)


def split_blocks(lines):
    """Statement text followed by its result lines."""
    blocks = []
    cur = None
    i = 0
    while i < len(lines):
        l = lines[i]
        if cur is None:
            if l.strip() == '':
                i += 1
                continue
            cur = [l, []]
            # statement may span lines until ';'
            while not stmt_complete(cur[0]) and i + 1 < len(lines):
                i += 1
                cur[0] += '\n' + lines[i]
            blocks.append(cur)
            i += 1
            # result lines: until a line which starts a statement
            j = i
            res = []
            while j < len(lines):
                ll = lines[j]
                if STMT_START.match(ll) and (not res or looks_like_statement(ll)):
                    break
                res.append(ll)
                j += 1
            cur[1] = res
            i = j
            cur = None
        else:
            i += 1
    return blocks


def stmt_complete(s):
    # complete when the last non-space char is ';' outside quotes
    inq = None
    esc = False
    for c in s:
        if esc:
            esc = False
            continue
        if c == '\\':
            esc = True
            continue
        if inq:
            if c == inq:
                inq = None
        elif c in "'\"`":
            inq = c
    return (inq is None) and s.rstrip().endswith(';')


def looks_like_statement(l):
    return bool(re.match(r'^(select|insert|update|delete|create|drop|alter|set|show|explain|truncate|replace|with|commit|rollback|use|analyze|call|start|begin)\b', l, re.I))


def parse_create(toks):
    p = P(toks)
    p.need_kw('create')
    if p.kw('temporary'):
        p.i += 1
    if not p.eat_kw('table'):
        raise Skip('create other')
    if p.eat_kw('if'):
        p.need_kw('not')
        p.need_kw('exists')
    name = p.ident()
    if p.op('.'):
        raise Skip('qualified')
    if not p.eat_op('('):
        raise Skip('create like/as')
    cols = []
    limits = []
    while True:
        if p.kw('primary', 'unique', 'key', 'index', 'constraint', 'foreign', 'fulltext', 'check'):
            depth = 0
            while True:
                t = p.peek()
                if t == ('op', '('):
                    depth += 1
                elif t == ('op', ')'):
                    if depth == 0:
                        break
                    depth -= 1
                elif t == ('op', ',') and depth == 0:
                    break
                elif t[0] == 'eof':
                    raise Skip('eof')
                p.i += 1
        else:
            cname = p.ident()
            ty = p.ident().lower()
            width = None
            if ty in STR_TYPES and p.op('(') and p.peek(1)[0] == 'num':
                width = int(p.peek(1)[1])
            if ty in ('decimal', 'numeric'):
                # DECIMAL(p, s); DECIMAL(p) and DECIMAL have the scale 0
                width = ('dec', 0)
                if p.op('(') and p.peek(1)[0] == 'num':
                    if p.peek(2) == ('op', ',') and p.peek(3)[0] == 'num':
                        width = ('dec', int(p.peek(3)[1]))
            if p.op('('):
                depth = 0
                while True:
                    t = p.peek()
                    p.i += 1
                    if t == ('op', '('):
                        depth += 1
                    elif t == ('op', ')'):
                        depth -= 1
                        if depth == 0:
                            break
            if ty in NUM_TYPES:
                kind = 'Z'
            elif ty in DEC_TYPES:
                kind = 'Q'
            elif ty in STR_TYPES:
                kind = 'S'
            else:
                raise Skip('column type ' + ty)
            # column options: skip to ',' or ')' at depth 0
            depth = 0
            while True:
                t = p.peek()
                if t == ('op', '('):
                    depth += 1
                elif t == ('op', ')'):
                    if depth == 0:
                        break
                    depth -= 1
                elif t == ('op', ',') and depth == 0:
                    break
                elif t[0] == 'eof':
                    raise Skip('eof')
                elif t[0] in ('id', 'kw') and t[1].lower() in ('collate', 'charset', 'character', 'zerofill', 'default', 'auto_increment', 'generated', 'as', 'binary', 'unsigned', 'on', 'check', 'references'):
                    raise Skip('column option ' + t[1])
                p.i += 1
            cols.append((cname, kind))
            limits.append(width if width is not None else INT_RANGES.get(ty))
        if p.eat_op(','):
            continue
        p.need_op(')')
        break
    return name, cols, limits


def literal(p):
    neg = p.eat_op('-')
    t = p.peek()
    if t[0] == 'num':
        p.i += 1
        return ('num', ('-' if neg else '') + t[1])
    if neg:
        raise Skip('literal')
    if t[0] == 'str':
        p.i += 1
        return ('str', t[1])
    if p.eat_kw('null'):
        return ('null',)
    raise Skip('insert value')


def conv_value(lit, kind, limit=None):
    """The Coq value which is stored, with the conversion of the column type."""
    if lit[0] == 'str' and isinstance(limit, int) and len(lit[1]) > limit:
        raise Skip('truncation')
    if lit[0] == 'num' and isinstance(limit, tuple) and limit[0] != 'dec' and '.' not in lit[1] and not (limit[0] <= int(lit[1]) <= limit[1]):
        raise Skip('out of range')
    if lit[0] == 'null':
        return {'Z': 'NullZ', 'S': 'NullS', 'Q': 'NullQ'}[kind]
    if kind == 'S':
        if lit[0] == 'str':
            return 'VS %s' % coq_str(lit[1])
        raise Skip('number into string column')
    if lit[0] == 'str':
        raise Skip('string into numeric column')
    txt = lit[1]
    if kind == 'Z':
        if '.' in txt:
            raise Skip('decimal into int column')
        return 'VZ (%s)' % txt
    if isinstance(limit, tuple) and limit[0] == 'dec':
        return 'VD (%s) %d' % (round_to_scale(txt, limit[1]), limit[1])
    n, d = dec_lit(txt)
    return 'VQ (%s) %d' % (n, d)


def parse_insert(toks, tables):
    p = P(toks)
    p.need_kw('insert')
    if p.kw('ignore'):
        p.i += 1
    p.eat_kw('into')
    name = p.ident()
    t = tables.get(name.lower())
    if t is None:
        raise Skip('unknown table')
    cols = None
    if p.eat_op('('):
        cols = []
        while True:
            cols.append(p.ident())
            if not p.eat_op(','):
                break
        p.need_op(')')
    if not p.eat_kw('values') and not p.eat_kw('value'):
        raise Skip('insert select')
    rows = []
    while True:
        p.need_op('(')
        vals = []
        while True:
            vals.append(literal(p))
            if not p.eat_op(','):
                break
        p.need_op(')')
        rows.append(vals)
        if not p.eat_op(','):
            break
    if p.kw('on'):
        raise Skip('on duplicate')
    out = []
    idx = {c.lower(): i for i, (c, _) in enumerate(t.cols)}
    for vals in rows:
        row = [None] * len(t.cols)
        if cols is None:
            if len(vals) != len(t.cols):
                raise Skip('arity')
            for i, v in enumerate(vals):
                row[i] = conv_value(v, t.cols[i][1], t.limits[i] if i < len(t.limits) else None)
        else:
            if len(vals) != len(cols):
                raise Skip('arity')
            for c, v in zip(cols, vals):
                i = idx.get(c.lower())
                if i is None:
                    raise Skip('column')
                row[i] = conv_value(v, t.cols[i][1], t.limits[i] if i < len(t.limits) else None)
            for i in range(len(row)):
                if row[i] is None:
                    row[i] = {'Z': 'NullZ', 'S': 'NullS', 'Q': 'NullQ'}[t.cols[i][1]]
        out.append(row)
    return t, out


def parse_results(res_lines, ncols):
    """Rows of a result in the tab format: the first line is the header."""
    lines = [l for l in res_lines]
    while lines and lines[-1].strip() == '':
        lines.pop()
    if not lines:
        return None
    if lines[0].startswith('ERROR'):
        return None
    if lines[0].startswith('+'):
        # result_format 4: +---+ / | h | / +---+ / | v | / +---+
        body = [l for l in lines if l.startswith('|')]
        if len(lines) < 3 or lines[2].startswith('+') is False:
            return None
        rows = []
        for l in body[1:]:
            cells = [c.strip() for c in l.strip()[1:-1].split('|')]
            if len(cells) != ncols:
                return None
            rows.append(cells)
        return rows
    hdr = lines[0].split('\t')
    if len(hdr) != ncols:
        return None
    rows = []
    for l in lines[1:]:
        cells = l.split('\t')
        if len(cells) != ncols:
            return None
        rows.append(cells)
    return rows


def norm(s):
    return re.sub(r'\s+', ' ', s.strip().rstrip(';').strip()).lower()


def test_items(test_src, blocks):
    """The statements of the test script, in order, each with its recorded result (None when the
    statement is not echoed in the result file, for instance after --disable_query_log) and whether
    the script expects it to fail."""
    stmts = []
    cur = ''
    pending_error = False
    for line in test_src.split('\n'):
        st = line.strip()
        if not cur:
            if st == '' or st.startswith('#'):
                continue
            if st.startswith('--'):
                if re.match(r'^--\s*error\b', st):
                    pending_error = True
                continue
        cur += line + '\n'
        if stmt_complete(cur):
            stmts.append((cur.strip(), pending_error))
            cur = ''
            pending_error = False
    items = []
    bi = 0
    for text, err in stmts:
        found = None
        for j in range(bi, min(bi + 8, len(blocks))):
            if norm(blocks[j][0]) == norm(text):
                found = j
                break
        if found is not None:
            items.append((blocks[found][0], blocks[found][1], err))
            bi = found + 1
        else:
            items.append((text, None, err))
    return items


def process(path, out, stats):
    import os
    if os.path.getsize(path) > 3000000:
        stats['skipped_files'] += 1
        return
    lines = open(path, encoding='utf-8', errors='replace').read().split('\n')
    tables = {}
    blocks = split_blocks(lines)
    base = path.split('/')[-1].replace('.result', '')
    cases = []
    # the statements which a loop or an eval of the test script runs are not in the result file
    test_path = re.sub(r'/r/mysql/([^/]*)\.result$', r'/t/\1.test', path)
    items = None
    try:
        test_src = open(test_path, encoding='utf-8', errors='replace').read()
        if re.search(r'^\s*(while|eval|let|--source|--exec|--perl|--eval)\b', test_src, re.I | re.M):
            stats['skipped_files'] += 1
            return
        if re.search(r'^\s*(connect|connection|delimiter)\b', test_src, re.I | re.M):
            stats['skipped_files'] += 1
            return
        items = test_items(test_src, blocks)
    except OSError:
        pass
    if items is None:
        items = [(stmt, res, False) for stmt, res in blocks]
    unsafe = re.compile(r'\b(rollback|savepoint|create\s+procedure|create\s+function|delimiter|call\s|prepare\s|load\s+data|set\s+autocommit|start\s+transaction|begin\b|xa\s)', re.I)
    if any(unsafe.search(stmt) for stmt, _, _ in items):
        stats['skipped_files'] += 1
        return
    for bi, (stmt, res, expect_err) in enumerate(items):
        s = stmt.strip()
        if len(s) > 20000:
            continue
        failed = expect_err or (res is not None and any(l.startswith('ERROR') for l in res))
        try:
            toks = tokenize(s)
        except Skip:
            if re.match(r'^\s*(update|delete|insert|replace|alter|truncate|rename|create|drop|merge|load)\b', s, re.I):
                for t in tables.values():
                    if re.search(r'\b' + re.escape(t.name) + r'\b', s, re.I):
                        t.ok = False
            continue
        if not toks:
            continue
        head = toks[0][1].lower() if toks[0][0] in ('id', 'kw') else ''
        if failed and head in ('create', 'insert', 'update', 'delete', 'replace', 'alter', 'truncate', 'rename'):
            continue
        try:
            if head == 'drop':
                p = P(toks)
                p.i = 1
                if not p.eat_kw('table'):
                    continue
                if p.eat_kw('if'):
                    p.need_kw('exists')
                while True:
                    n = p.ident()
                    tables.pop(n.lower(), None)
                    if not p.eat_op(','):
                        break
            elif head == 'create':
                try:
                    name, cols, limits = parse_create(toks)
                    tables[name.lower()] = Table(name, cols)
                    tables[name.lower()].limits = limits
                except Skip:
                    # an unsupported table: remember that it exists but is unreliable
                    p = P(toks)
                    p.i = 1
                    while p.kw('temporary'):
                        p.i += 1
                    if p.eat_kw('table'):
                        if p.eat_kw('if'):
                            p.need_kw('not')
                            p.need_kw('exists')
                        try:
                            n = p.ident()
                            t = Table(n, [])
                            t.ok = False
                            tables[n.lower()] = t
                        except Skip:
                            pass
            elif head == 'insert':
                try:
                    t, rows = parse_insert(toks, tables)
                    if t.ok:
                        t.rows.extend(rows)
                except Skip:
                    p = P(toks)
                    p.i = 1
                    p.eat_kw('ignore')
                    p.eat_kw('into')
                    try:
                        n = p.ident()
                        if n.lower() in tables:
                            tables[n.lower()].ok = False
                    except Skip:
                        pass
            elif head in ('update', 'delete', 'replace', 'truncate', 'alter', 'rename'):
                for t in tables.values():
                    if re.search(r'\b' + re.escape(t.name) + r'\b', s, re.I):
                        t.ok = False
            elif head == 'select':
                if res is None:
                    stats['hidden'] = stats.get('hidden', 0) + 1
                    continue
                stats['selects'] += 1
                p = P(toks)
                q = p.query()
                p.eat_op(';')
                if p.peek()[0] != 'eof':
                    raise Skip('trailing')
                qt = QTr(tables)
                cq, ncols, ordered, _ = qt.query(q)
                rows = parse_results(res, ncols)
                if rows is None:
                    stats['no_result'] += 1
                    continue
                tabs = []
                for tn in sorted(qt.used):
                    t = tables[tn]
                    tabs.append('(%s, [%s], [%s])' % (coq_str(t.name),
                                                      '; '.join(attr(kd, n) for n, kd in t.cols),
                                                      '; '.join('[%s]' % '; '.join(r) for r in t.rows)))
                exp = '[%s]' % '; '.join('[%s]' % '; '.join(coq_str(c) for c in r) for r in rows)
                try:
                    sql_txt = coq_str(' '.join(s.split())[:400])
                except Skip:
                    sql_txt = '""'
                cases.append('  mk_case %s %s [%s] %s %s %s' % (
                    coq_str('%s:%d' % (base, bi)), 'true' if ordered else 'false', '; '.join(tabs), cq, exp, sql_txt))
                stats['translated'] += 1
        except Skip as e:
            if head == 'select':
                stats['skip'][str(e).split(' ')[0] + ' ' + (str(e).split(' ')[1] if ' ' in str(e) else '')] = stats['skip'].get(str(e).split(' ')[0] + ' ' + (str(e).split(' ')[1] if ' ' in str(e) else ''), 0) + 1
        except (IndexError, KeyError, ValueError, AttributeError) as e:
            if head == 'select':
                stats['skip']['internal ' + type(e).__name__] = stats['skip'].get('internal ' + type(e).__name__, 0) + 1
    if cases:
        out.append((base, cases))


HEADER = """Require Import List String ZArith NArith.
Require Import FiniteSet Values TuplesImpl GenericInstance SqlSyntax SqlFull SqlFullSyntax Dialects
        PostgreSQL MySQL SQLite OceanBase SpecRunner.
Import ListNotations.
Open Scope string_scope.
"""


def main():
    args = sys.argv[1:]
    dialect, outdir = 'OceanBaseMySQL', None
    while args and args[0].startswith('--'):
        if args[0] == '--dialect':
            dialect = args[1]
        elif args[0] == '--outdir':
            outdir = args[1]
        args = args[2:]
    import os
    stats = {'selects': 0, 'translated': 0, 'no_result': 0, 'skipped_files': 0, 'skip': {}}
    for path in args:
        out = []
        process(path, out, stats)
        for base, cases in out:
            name = re.sub(r'\W', '_', base)
            body = 'Definition cases_%s : list spec_case := [\n%s\n].\n' % (name, ';\n'.join(cases))
            body += 'Eval vm_compute in (diagnose %s cases_%s).\n' % (dialect, name)
            if outdir:
                os.makedirs(outdir, exist_ok=True)
                with open(os.path.join(outdir, 'Spec_%s.v' % name), 'w') as f:
                    f.write(HEADER + body)
            else:
                print(body)
    sys.stderr.write(json.dumps(stats, indent=1, sort_keys=True) + '\n')


if __name__ == '__main__':
    main()
