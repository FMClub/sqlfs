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
        elif s.startswith('/*!', i) and ENGINE == 'mysql':
            # an executable comment of the MySQL family: /*! body */ is code, /*!NNNNN body */ is code from the
            # server version NNNNN (MySQL 8.4 is 80400, MariaDB 11.4 is 110400); the body is put back in place
            j = s.find('*/', i + 3)
            if j < 0:
                raise Skip('comment')
            m = re.match(r'(\d{5,6})', s[i + 3:j])
            body = s[i + 3 + (len(m.group(1)) if m else 0):j]
            if m and int(m.group(1)) > SERVER_VERSION:
                body = ''
            s = s[:i] + ' ' + body + ' ' + s[j + 2:]
            n = len(s)
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
            if m is None:
                raise Skip('non-ASCII identifier')
            w = m.group(0)
            toks.append(('kw' if w.lower() in KEYWORDS else 'id', w))
            i += len(w)
        elif s.startswith(('<=>', ), i):
            toks.append(('op', '<=>'))
            i += 3
        elif s[i:i + 2] in ('<=', '>=', '<>', '!=', '||', '&&', ':=', '<<', '>>'):
            toks.append(('op', s[i:i + 2]))
            i += 2
        elif c in '+-*/%=<>(),.;@&|^~![]:':
            toks.append(('op', c))
            i += 1
        else:
            raise Skip('char %r' % c)
    return toks


# ----------------------------------------------------------------------------------------
# Parser
# ----------------------------------------------------------------------------------------

NAMED_WINDOWS = {}
# the version of the server, for the executable comments /*!NNNNN ... */ of the MySQL family
SERVER_VERSION = 80400
# the views of the script: name -> (query, columns); a view is a derived table where it is used
VIEWS = {}


class P:
    def __init__(self, toks):
        self.t = toks
        self.i = 0
        # the named windows of the statement (WINDOW w AS ...), read by the translation of OVER w
        global NAMED_WINDOWS
        NAMED_WINDOWS = {}
        self.named_windows = NAMED_WINDOWS

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
        # INTERSECT binds tighter than UNION and EXCEPT in PostgreSQL and MySQL (8.0.31); SQLite and
        # Oracle give them the same precedence, from left to right
        tight = ENGINE in ('postgresql', 'mysql')
        q = self.intersect_term() if tight else self.select_or_paren()
        while self.kw('union', 'intersect', 'except', 'minus'):
            op = self.peek()[1].lower()
            self.i += 1
            allq = self.eat_kw('all')
            if not allq:
                self.eat_kw('distinct')
            r = self.intersect_term() if tight else self.select_or_paren()
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

    def intersect_term(self):
        q = self.select_or_paren()
        while self.kw('intersect'):
            self.i += 1
            allq = self.eat_kw('all')
            if not allq:
                self.eat_kw('distinct')
            r = self.select_or_paren()
            q = ('setop', 'intersect', allq, q, r)
        return q

    def select_or_paren(self):
        if self.eat_op('('):
            q = self.query()
            self.need_op(')')
            return q
        if ENGINE in ('postgresql', 'sqlite') and self.kw('values'):
            # VALUES (e, ...), (e, ...): a query whose columns are c0, c1, ...
            self.i += 1
            rows = []
            while True:
                self.need_op('(')
                row = [self.expr()]
                while self.eat_op(','):
                    row.append(self.expr())
                self.need_op(')')
                rows.append(row)
                if not self.eat_op(','):
                    break
            if len(set(len(r) for r in rows)) != 1:
                raise Skip('values arity')
            return ('values', rows)
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
            if self.peek()[0] in ('id', 'kw') and self.peek()[1].lower() == 'dual':
                # FROM DUAL (MySQL, Oracle): no table
                self.i += 1
            else:
                frm = self.from_clause()
        where = self.expr() if self.eat_kw('where') else None
        group = None
        if self.kw('group'):
            self.i += 1
            self.need_kw('by')
            dist_sets = False
            if self.eat_kw('distinct'):
                dist_sets = True
            else:
                self.eat_kw('all')
            elems = []
            while True:
                elems.append(self.group_element())
                if not self.eat_op(','):
                    break
            if self.kw('with'):
                # MySQL: GROUP BY a, b WITH ROLLUP
                self.i += 1
                if not (self.peek()[0] in ('id', 'kw') and self.peek()[1].lower() == 'rollup'):
                    raise Skip('with rollup')
                self.i += 1
                if any(k != 'plain' for k, _ in elems):
                    raise Skip('with rollup')
                elems = [('sets', rollup_sets([x for _, ss in elems for x in ss[0]]))]
            if all(k == 'plain' for k, _ in elems):
                group = [x for _, ss in elems for x in ss[0]]
            else:
                sets = [[]]
                for _, ss in elems:
                    sets = [a + b for a in sets for b in ss]
                if dist_sets:
                    out = []
                    for st in sets:
                        if not any(sorted(map(repr, st)) == sorted(map(repr, o)) for o in out):
                            out.append(st)
                    sets = out
                group = ('sets', sets)
        having = self.expr() if self.eat_kw('having') else None
        # WINDOW w AS (spec), ...: the named windows (one name space per statement)
        if self.peek()[0] in ('id', 'kw') and self.peek()[1].lower() == 'window':
            self.i += 1
            while True:
                name = self.ident().lower()
                self.need_kw('as')
                self.need_op('(')
                self.named_windows[name] = self.window_spec()
                if not self.eat_op(','):
                    break
        if self.kw('window', 'for', 'lock', 'into', 'procedure'):
            raise Skip('clause')
        return ('select', distinct, items, frm, where, group, having)

    def group_element(self):
        """an element of GROUP BY: an expression, (), ROLLUP (...), CUBE (...), GROUPING SETS (...); its grouping
        sets ('plain' for an expression: one set of one expression)"""
        def item():
            # an argument of ROLLUP / CUBE: (e1, e2) is one item of several expressions
            if self.op('(') and self.peek(1) == ('op', ')'):
                self.i += 2
                return []
            if self.op('('):
                save = self.i
                self.i += 1
                xs = [self.expr()]
                if self.eat_op(','):
                    xs.append(self.expr())
                    while self.eat_op(','):
                        xs.append(self.expr())
                    self.need_op(')')
                    return xs
                self.i = save
            return [self.expr()]
        w = self.peek()[1].lower() if self.peek()[0] in ('id', 'kw') else ''
        if w in ('rollup', 'cube') and self.peek(1) == ('op', '('):
            self.i += 2
            items = [item()]
            while self.eat_op(','):
                items.append(item())
            self.need_op(')')
            if w == 'rollup':
                return ('sets', [sum(items[:k], []) for k in range(len(items), -1, -1)])
            def cube(l):
                if not l:
                    return [[]]
                sub = cube(l[1:])
                return [l[0] + x for x in sub] + sub
            return ('sets', cube(items))
        if w == 'grouping' and self.peek(1)[0] in ('id', 'kw') and self.peek(1)[1].lower() == 'sets':
            self.i += 2
            self.need_op('(')
            sets = []
            while True:
                if self.op('(') and self.peek(1) == ('op', ')'):
                    self.i += 2
                    sets.append([])
                else:
                    k, ss = self.group_element_in_sets()
                    sets += ss
                if not self.eat_op(','):
                    break
            self.need_op(')')
            return ('sets', sets)
        if self.op('(') and self.peek(1) == ('op', ')'):
            self.i += 2
            return ('sets', [[]])
        return ('plain', [[self.expr()]])

    def group_element_in_sets(self):
        """an element inside GROUPING SETS: (e1, e2) is one set; ROLLUP, CUBE, GROUPING SETS nest"""
        w = self.peek()[1].lower() if self.peek()[0] in ('id', 'kw') else ''
        if w in ('rollup', 'cube', 'grouping'):
            return self.group_element()
        if self.op('('):
            save = self.i
            self.i += 1
            xs = [self.expr()]
            if self.eat_op(','):
                xs.append(self.expr())
                while self.eat_op(','):
                    xs.append(self.expr())
                self.need_op(')')
                return ('sets', [xs])
            self.i = save
        return ('sets', [[self.expr()]])

    def window_spec(self):
        """the inside of OVER ( ... ), after '(': [name] [PARTITION BY ...] [ORDER BY ...] [frame] ')'"""
        base = None
        if self.peek()[0] == 'id' and self.peek()[1].lower() not in ('partition', 'order', 'rows', 'range', 'groups'):
            base = self.ident().lower()
        part, order, frame = [], [], None
        if self.eat_kw('partition'):
            self.need_kw('by')
            part.append(self.expr())
            while self.eat_op(','):
                part.append(self.expr())
        if self.eat_kw('order'):
            self.need_kw('by')
            while True:
                e = self.expr()
                d = 'asc'
                if self.eat_kw('desc'):
                    d = 'desc'
                else:
                    self.eat_kw('asc')
                nulls = None
                if self.eat_kw('nulls'):
                    nulls = 'first' if self.eat_kw('first') else ('last' if self.eat_kw('last') else None)
                    if nulls is None:
                        raise Skip('window nulls')
                order.append((e, d, nulls))
                if not self.eat_op(','):
                    break
        if self.peek()[0] in ('id', 'kw') and self.peek()[1].lower() in ('rows', 'range', 'groups'):
            mode = self.peek()[1].lower()
            self.i += 1

            def bound():
                if self.eat_kw('unbounded'):
                    if self.eat_kw('preceding'):
                        return ('up',)
                    self.need_kw('following')
                    return ('uf',)
                if self.eat_kw('current'):
                    self.need_kw('row')
                    return ('cr',)
                t = self.peek()
                if t[0] != 'num' or '.' in t[1]:
                    raise Skip('window frame offset')
                self.i += 1
                if self.eat_kw('preceding'):
                    return ('p', int(t[1]))
                self.need_kw('following')
                return ('f', int(t[1]))
            if self.eat_kw('between'):
                lo = bound()
                self.need_kw('and')
                hi = bound()
            else:
                lo, hi = bound(), ('cr',)
            excl = None
            if self.peek()[0] in ('id', 'kw') and self.peek()[1].lower() == 'exclude':
                self.i += 1
                if self.eat_kw('current'):
                    self.need_kw('row')
                    excl = 'Excl_Current_Row'
                elif self.eat_kw('group'):
                    excl = 'Excl_Group'
                elif self.peek()[1].lower() == 'ties':
                    self.i += 1
                    excl = 'Excl_Ties'
                else:
                    self.need_kw('no')
                    self.i += 1
                    excl = 'Excl_No_Others'
            frame = (mode, lo, hi, excl)
        self.need_op(')')
        return ('spec', base, part, order, frame)

    def over(self):
        """OVER (spec) or OVER name, after a call; None if there is none"""
        if not self.kw('over'):
            return None
        self.i += 1
        if self.eat_op('('):
            return self.window_spec()
        return ('spec', self.ident().lower(), [], [], None)

    def null_treatment(self):
        """IGNORE NULLS / RESPECT NULLS (between the call and OVER)"""
        if self.peek()[0] in ('id', 'kw') and self.peek()[1].lower() in ('ignore', 'respect') and \
           self.peek(1)[0] in ('id', 'kw') and self.peek(1)[1].lower() == 'nulls':
            ign = self.peek()[1].lower() == 'ignore'
            self.i += 2
            return ign
        return False

    def ident(self):
        t = self.peek()
        if t[0] in ('id', 'kw'):
            self.i += 1
            return t[1]
        raise Skip('identifier')

    def from_clause(self):
        # a comma binds less than JOIN: a, b JOIN c ON .. is a, (b JOIN c ON ..)
        item = self.join_chain()
        while self.eat_op(','):
            item = ('join', 'cross', item, self.join_chain(), None)
        return item

    def join_chain(self):
        item = self.table_ref()
        while True:
            jt = None
            natural = False
            if self.eat_kw('natural'):
                natural = True
            if self.peek()[0] in ('id', 'kw') and self.peek()[1].lower() == 'straight_join':
                self.i += 1
                jt = 'inner'
            elif self.eat_kw('cross'):
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
                if natural:
                    raise Skip('natural')
                break
            r = self.table_ref()
            cond = None
            using = None
            if natural:
                using = 'natural'
            elif self.eat_kw('on'):
                cond = self.expr()
            elif self.eat_kw('using'):
                self.need_op('(')
                using = [self.ident()]
                while self.eat_op(','):
                    using.append(self.ident())
                self.need_op(')')
            item = ('join', jt, item, r, cond, using)
        return item

    def table_ref(self):
        if self.op('('):
            save = self.i
            self.i += 1
            if self.op('('):
                # ((SELECT ...) UNION (SELECT ...)) AS a: a query whose first operand is parenthesised
                try:
                    q = self.query()
                    self.need_op(')')
                    self.eat_kw('as')
                    alias = self.ident()
                    cols = None
                    if self.eat_op('('):
                        cols = [self.ident()]
                        while self.eat_op(','):
                            cols.append(self.ident())
                        self.need_op(')')
                    return ('derived', q, alias, cols)
                except Skip:
                    self.i = save + 1
            if not self.kw('select', 'values', 'with'):
                # a parenthesised join: (t1 JOIN t2 ON ...)
                inner = self.from_clause()
                self.need_op(')')
                if self.peek()[0] == 'id' and not self.kw('join', 'inner', 'left', 'right', 'full', 'cross', 'natural',
                                                         'on', 'where', 'group', 'order', 'limit', 'having', 'union',
                                                         'intersect', 'except', 'minus', 'using') or self.kw('as'):
                    raise Skip('parenthesised join with an alias')
                return inner
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
        if self.op('(') and name.lower() == 'json_table' and ENGINE == 'mysql':
            # JSON_TABLE (doc, rowpath COLUMNS (c type PATH p, ...)) [AS] alias
            self.i += 1
            doc = self.expr()
            self.need_op(',')
            rowpath = self.e_primary()
            if not (self.peek()[0] in ('id', 'kw') and self.peek()[1].lower() == 'columns'):
                raise Skip('json_table')
            self.i += 1
            self.need_op('(')
            cols, paths = [], []
            while True:
                cname = self.ident()
                depth = 0
                # the type, up to PATH
                while not (self.peek()[0] in ('id', 'kw') and self.peek()[1].lower() in ('path', 'for')):
                    if self.peek()[0] == 'eof':
                        raise Skip('json_table column')
                    self.i += 1
                if self.peek()[1].lower() == 'for':
                    raise Skip('json_table ordinality')
                self.i += 1
                paths.append(self.e_primary())
                cols.append(cname)
                if self.kw('default', 'null', 'error'):
                    raise Skip('json_table on empty')
                if not self.eat_op(','):
                    break
            self.need_op(')')
            self.need_op(')')
            self.eat_kw('as')
            alias = self.ident()
            return ('tfun', 'json_table', [doc, rowpath] + paths, False, alias, cols)
        if self.op('(') and ENGINE in ('postgresql', 'sqlite'):
            # a table function: name (args) [WITH ORDINALITY] [AS] alias [(columns)]
            self.i += 1
            args = []
            if not self.op(')'):
                args.append(self.expr())
                while self.eat_op(','):
                    args.append(self.expr())
            self.need_op(')')
            ord_ = False
            if self.peek()[0] in ('id', 'kw') and self.peek()[1].lower() == 'with' and self.peek(1)[1].lower() == 'ordinality':
                self.i += 2
                ord_ = True
            self.eat_kw('as')
            alias = name
            if self.peek()[0] == 'id' and not self.kw('join', 'inner', 'left', 'right', 'full', 'cross', 'natural', 'on', 'where', 'group', 'order', 'limit', 'having'):
                alias = self.ident()
            cols = None
            if self.eat_op('('):
                cols = [self.ident()]
                while self.eat_op(','):
                    cols.append(self.ident())
                self.need_op(')')
            return ('tfun', name.lower(), args, ord_, alias, cols)
        if self.op('.'):
            raise Skip('qualified table')
        alias = name
        if self.eat_kw('as'):
            alias = self.ident()
        elif self.peek()[0] == 'id' and not self.kw('join', 'inner', 'left', 'right', 'full', 'cross', 'natural', 'on', 'where', 'group', 'order', 'limit', 'having', 'union', 'intersect', 'except', 'minus', 'using', 'use', 'force', 'ignore', 'partition', 'straight_join'):
            alias = self.ident()
        if self.kw('use', 'force', 'ignore', 'partition'):
            raise Skip('index hint')
        cols = None
        if self.op('(') and ENGINE in ('postgresql', 'sqlite'):
            # t [AS] alias (c1, c2, ...): the columns renamed
            self.i += 1
            cols = [self.ident()]
            while self.eat_op(','):
                cols.append(self.ident())
            self.need_op(')')
        if name.lower() in VIEWS:
            q, vcols = VIEWS[name.lower()]
            return ('derived', q, alias, cols or vcols)
        if cols is not None:
            return ('derived', ('select', False, [('star', None)], ('table', name, name), None, None, None), alias, cols)
        return ('table', name, alias)

    # ---- expressions (precedence climbing)
    def expr(self):
        return self.e_or()

    def e_or(self):
        l = self.e_xor()
        while self.eat_kw('or') or (ENGINE != 'postgresql' and self.eat_op('||')):
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

    def postfix(self, e):
        # a[i] and a[i:j] (PostgreSQL)
        while ENGINE == 'postgresql' and self.op('['):
            self.i += 1
            lo = self.expr()
            if self.eat_op(':'):
                hi = self.expr()
                self.need_op(']')
                e = ('call', 'slice', [e, lo, hi], False, False)
            else:
                self.need_op(']')
                e = ('call', 'subscript', [e, lo], False, False)
        return e

    def ilike_mark(self):
        self.i += 1
        return True

    def e_pred(self):
        l = self.e_bitor()
        while True:
            neg = False
            save = self.i
            if self.kw('not') and self.peek(1)[1].lower() in ('in', 'like', 'ilike', 'between', 'regexp', 'rlike', 'similar'):
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
                if self.op('(') and self.peek(1)[0] in ('id', 'kw') and self.peek(1)[1].lower() in ('select', 'with', 'values'):
                    # IN ((SELECT ...) UNION (SELECT ...)): a query whose first operand is parenthesised
                    save_in = self.i
                    try:
                        q = self.query()
                        self.need_op(')')
                        l = ('insub', neg, [l] if l[0] != 'row' else l[1], q)
                        continue
                    except Skip:
                        self.i = save_in
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
            elif self.eat_kw('like') or (self.peek()[0] in ('id', 'kw') and self.peek()[1].lower() == 'ilike'
                                         and ENGINE == 'postgresql' and not self.eat_kw('like')
                                         and self.ilike_mark()):
                ci = self.t[self.i - 1][1].lower() == 'ilike'
                r = self.e_bitor()
                esc = None
                if self.eat_kw('escape'):
                    esc = self.e_bitor()
                if self.kw('binary'):
                    raise Skip('like binary')
                l = ('like', neg, l, r, esc, ci)
            elif self.eat_kw('between'):
                sym = False
                if self.peek()[0] in ('id', 'kw') and self.peek()[1].lower() in ('symmetric', 'asymmetric'):
                    sym = self.peek()[1].lower() == 'symmetric'
                    self.i += 1
                lo = self.e_bitor()
                self.need_kw('and')
                hi = self.e_bitor()
                l = ('between', neg, l, lo, hi, sym)
            elif self.kw('regexp', 'rlike') or (self.peek()[0] in ('id', 'kw') and self.peek()[1].lower() in ('regexp', 'rlike')):
                self.i += 1
                r = self.e_bitor()
                l = ('regexp', neg, l, r)
            elif ENGINE == 'postgresql' and self.peek()[0] in ('id', 'kw') and self.peek()[1].lower() == 'similar' \
                    and self.peek(1)[1].lower() == 'to':
                self.i += 2
                r = self.e_bitor()
                esc = None
                if self.eat_kw('escape'):
                    esc = self.e_bitor()
                l = ('similar', neg, l, r, esc)
            else:
                if neg:
                    self.i = save
                    break
                t = self.peek()
                if ENGINE == 'postgresql' and t == ('op', '~') or (t == ('op', '!') and self.peek(1) == ('op', '~')):
                    negm = t == ('op', '!')
                    self.i += 2 if negm else 1
                    ci = self.peek() == ('op', '*')
                    if ci:
                        self.i += 1
                    r = self.e_bitor()
                    l = ('cmp', ('!' if negm else '') + '~' + ('*' if ci else ''), l, r)
                    continue
                if t[0] == 'op' and t[1] in ('=', '<>', '!=', '<', '<=', '>', '>=', '<=>'):
                    self.i += 1
                    if self.kw('any', 'some', 'all'):
                        quant = 'all' if self.peek()[1].lower() == 'all' else 'any'
                        self.i += 1
                        self.need_op('(')
                        if not self.kw('select'):
                            if ENGINE != 'postgresql':
                                raise Skip('quantified list')
                            arr = self.expr()
                            self.need_op(')')
                            l = ('cmp_array', t[1], quant, l, arr)
                            continue
                        q = self.query()
                        self.need_op(')')
                        l = ('quant', t[1], quant, [l] if l[0] != 'row' else l[1], q)
                        continue
                    l = ('cmp', t[1], l, self.e_bitor())
                else:
                    break
        return l

    # the bit operators of the MySQL family: | below &, below << >>, below + -; ^ above * /
    def e_bitor(self):
        l = self.e_bitand()
        # in PostgreSQL, [||] is an operator of the same level as [|]: below [+], above the comparisons
        while self.peek() == ('op', '|') or (ENGINE == 'postgresql' and self.peek() == ('op', '||')):
            op = self.peek()[1]
            self.i += 1
            l = ('bin', op, l, self.e_bitand())
        return l

    def e_bitand(self):
        l = self.e_shift()
        while self.peek() == ('op', '&'):
            self.i += 1
            l = ('bin', '&', l, self.e_shift())
        return l

    def e_shift(self):
        l = self.e_add()
        while self.peek() in (('op', '<<'), ('op', '>>')):
            op = self.peek()[1]
            self.i += 1
            l = ('bin', op, l, self.e_add())
        return l

    def e_bitxor(self):
        l = self.e_unary()
        while self.peek() == ('op', '^'):
            self.i += 1
            l = ('bin', '^', l, self.e_unary())
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
        l = self.e_bitxor()
        while True:
            t = self.peek()
            if t[0] == 'op' and t[1] in ('*', '/', '%'):
                self.i += 1
                l = ('bin', t[1], l, self.e_bitxor())
            elif self.kw('div', 'mod'):
                w = t[1].lower()
                self.i += 1
                l = ('bin', w, l, self.e_bitxor())
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
        if self.eat_op('~'):
            return ('bitnot', self.e_unary())
        if self.eat_kw('not'):
            return ('not', self.e_unary())
        e = self.e_primary()
        # PostgreSQL [e :: type]
        while ENGINE == 'postgresql' and self.peek() == ('op', ':') and self.peek(1) == ('op', ':'):
            self.i += 2
            ty, args = self.pg_type()
            if ty in ('decimal', 'numeric') and args:
                p_, s_ = (args + [0])[:2]
                e = ('cast_dec', p_, s_, e)
            else:
                e = ('cast', ty, e)
            e = self.postfix(e)
        return e

    def agg_filter(self):
        """[FILTER (WHERE c)] after an aggregate"""
        if self.peek()[0] in ('id', 'kw') and self.peek()[1].lower() == 'filter' and self.peek(1) == ('op', '('):
            self.i += 2
            self.need_kw('where')
            c = self.expr()
            self.need_op(')')
            return c
        return None

    def pg_type(self):
        """A type name (several words: double precision, character varying, timestamp with time zone),
        its arguments, and [] for an array (not modelled: Skip)."""
        words = [self.peek()[1].lower()]
        self.i += 1
        while self.peek()[0] in ('id', 'kw') and self.peek()[1].lower() in ('precision', 'varying', 'with', 'without',
                                                                          'time', 'zone'):
            words.append(self.peek()[1].lower())
            self.i += 1
        args = []
        if self.op('('):
            self.i += 1
            while not self.eat_op(')'):
                t = self.peek()
                if t[0] == 'num':
                    args.append(int(t[1]))
                self.i += 1
        if self.op('['):
            raise Skip('cast type array')
        ty = ' '.join(words)
        ty = {'double precision': 'double', 'character varying': 'varchar', 'character': 'char',
              'timestamp with time zone': 'timestamptz', 'timestamp without time zone': 'timestamp',
              'time without time zone': 'time', 'time with time zone': 'timetz'}.get(ty, ty)
        return ty, args

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
            return ('bool', True) if ENGINE == 'postgresql' else ('num', '1')
        if self.eat_kw('false'):
            return ('bool', False) if ENGINE == 'postgresql' else ('num', '0')
        if self.kw('case'):
            return self.case()
        if self.kw('cast'):
            self.i += 1
            self.need_op('(')
            e = self.expr()
            self.need_kw('as')
            if ENGINE == 'postgresql':
                ty, args = self.pg_type()
            else:
                ty = self.peek()[1].lower()
                self.i += 1
                args = []
                if self.op('('):
                    self.i += 1
                    while not self.eat_op(')'):
                        t = self.peek()
                        if t[0] == 'num':
                            args.append(int(t[1]))
                        self.i += 1
            if ty == 'unsigned' or ty == 'signed':
                self.eat_kw('integer') or self.eat_kw('int')
            self.need_op(')')
            if ty in ('decimal', 'numeric') and (args or ENGINE == 'mysql'):
                # DECIMAL(p, s); DECIMAL(p) is DECIMAL(p, 0); DECIMAL is DECIMAL(10, 0) in the MySQL family
                p_, s_ = (args + [10, 0][len(args):])[:2] if args else (10, 0)
                return ('cast_dec', p_, s_, e)
            return ('cast', ty, e)
        if self.kw('exists') and self.peek(1) == ('op', '('):
            self.i += 2
            q = self.query()
            self.need_op(')')
            return ('exists', q)
        if self.kw('date', 'timestamp', 'time') and self.peek(1)[0] == 'str':
            ty = self.peek()[1].lower()
            lit = self.peek(1)[1]
            self.i += 2
            return ('temporal', ty, lit)
        # PostgreSQL [type 'literal']: CAST ('literal' AS type)
        if ENGINE == 'postgresql' and self.peek()[0] in ('id', 'kw') and self.peek(1)[0] == 'str' and \
           self.peek()[1].lower() in ('int2', 'int4', 'int8', 'integer', 'int', 'smallint', 'bigint', 'float4', 'float8',
                                      'real', 'numeric', 'decimal', 'text', 'varchar', 'bool', 'boolean', 'interval',
                                      'json', 'jsonb', 'timestamptz', 'name', 'bpchar'):
            ty = self.peek()[1].lower()
            lit = self.peek(1)[1]
            self.i += 2
            return ('cast', ty, ('str', lit))
        if self.kw('interval') and self.peek(1) == ('op', '(') and ENGINE == 'mysql':
            # the function INTERVAL (n, n1, n2, ...)
            self.i += 2
            args = [self.expr()]
            while self.eat_op(','):
                args.append(self.expr())
            self.need_op(')')
            return ('call', 'interval_index', args, False, False)
        if self.kw('interval'):
            self.i += 1
            if self.peek()[0] == 'str' and ENGINE == 'postgresql':
                lit = self.peek()[1]
                self.i += 1
                return ('pginterval', lit)
            n = self.e_primary()
            unit = self.peek()[1]
            if unit.upper() not in ('YEAR', 'QUARTER', 'MONTH', 'WEEK', 'DAY', 'HOUR', 'MINUTE', 'SECOND', 'MICROSECOND',
                                    'YEAR_MONTH', 'DAY_HOUR', 'DAY_MINUTE', 'DAY_SECOND', 'HOUR_MINUTE', 'HOUR_SECOND',
                                    'MINUTE_SECOND'):
                raise Skip('interval unit')
            self.i += 1
            return ('interval', n, unit.upper())
        if ENGINE == 'postgresql' and t[0] in ('id', 'kw') and t[1].lower() == 'array' and self.peek(1) == ('op', '['):
            self.i += 2
            items = []
            if not self.op(']'):
                items.append(self.expr())
                while self.eat_op(','):
                    items.append(self.expr())
            self.need_op(']')
            return self.postfix(('call', 'array', items, False, False))
        # the niladic functions written without parentheses
        if t[0] in ('id', 'kw') and self.peek(1) != ('op', '(') and \
                t[1].lower() in (('current_user', 'session_user', 'current_role', 'current_catalog', 'current_schema', 'user')
                                 if ENGINE == 'postgresql' else ('current_user',) if ENGINE == 'mysql' else ()):
            self.i += 1
            return ('call', t[1].lower(), [], False, False)
        if self.kw('binary'):
            raise Skip('construct')
        if t[0] in ('id', 'kw'):
            name = t[1]
            self.i += 1
            if self.op('('):
                self.i += 1
                lname = name.lower()
                # the special syntaxes of the standard: TRIM ([LEADING | TRAILING | BOTH] [r] FROM s),
                # POSITION (a IN b), SUBSTRING (s FROM n [FOR m]), OVERLAY (s PLACING r FROM n [FOR m])
                if lname == 'trim' and (self.kw('leading', 'trailing', 'both') or
                                        any(tk == ('kw', 'from') or (tk[0] == 'kw' and tk[1].lower() == 'from')
                                            for tk in self.t[self.i:self.i + 4])):
                    where = 'both'
                    if self.peek()[0] in ('id', 'kw') and self.peek()[1].lower() in ('leading', 'trailing', 'both'):
                        where = self.peek()[1].lower()
                        self.i += 1
                    r = None
                    if not self.kw('from'):
                        r = self.e_bitor()
                    self.need_kw('from')
                    src = self.expr()
                    self.need_op(')')
                    return ('call', 'trim_' + where, [src] + ([r] if r is not None else []), False, False)
                # EXTRACT (unit FROM e)
                if lname == 'extract' and self.peek()[0] in ('id', 'kw') and \
                        (self.peek(1) == ('kw', 'from') or (self.peek(1)[0] == 'kw' and self.peek(1)[1].lower() == 'from')):
                    unit = self.peek()[1]
                    self.i += 2
                    src = self.expr()
                    self.need_op(')')
                    unit = unit.upper() if ENGINE == 'mysql' else unit.lower()
                    return ('call', 'extract', [('str', unit), src], False, False)
                if lname == 'position':
                    a = self.e_bitor()
                    self.need_kw('in')
                    b = self.expr()
                    self.need_op(')')
                    return ('call', 'position', [a, b], False, False)
                if lname in ('substring', 'overlay'):
                    save = self.i
                    try:
                        src = self.expr()
                        placing = None
                        if lname == 'overlay':
                            if not (self.peek()[0] in ('id', 'kw') and self.peek()[1].lower() == 'placing'):
                                raise Skip('overlay')
                            self.i += 1
                            placing = self.expr()
                        if self.eat_kw('from'):
                            n = self.expr()
                            m = None
                            if self.peek()[0] in ('id', 'kw') and self.peek()[1].lower() == 'for':
                                self.i += 1
                                m = self.expr()
                            self.need_op(')')
                            args = [src] + ([placing] if placing is not None else []) + [n] + ([m] if m is not None else [])
                            if lname == 'substring' and ENGINE == 'postgresql' and n[0] == 'str' and m is None:
                                return ('call', 'substring_regex', [src, n], False, False)
                            return ('call', lname, args, False, False)
                    except Skip:
                        if lname == 'overlay':
                            raise
                    self.i = save
                if self.eat_op('*'):
                    self.need_op(')')
                    flt = self.agg_filter()
                    e = ('call', lname, [], True, False)
                    w = self.over()
                    if w is not None:
                        if flt is not None:
                            raise Skip('window filter')
                        return ('wcall', e, w, False)
                    return ('filter', e, flt) if flt is not None else e
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
                within = None
                # an ordered-set aggregate: f (args) WITHIN GROUP (ORDER BY e [ASC | DESC])
                if self.peek()[0] in ('id', 'kw') and self.peek()[1].lower() == 'within':
                    self.i += 1
                    self.need_kw('group')
                    self.need_op('(')
                    self.need_kw('order')
                    self.need_kw('by')
                    oe = self.expr()
                    desc = False
                    if self.eat_kw('desc'):
                        desc = True
                    else:
                        self.eat_kw('asc')
                    if self.kw('nulls'):
                        raise Skip('within group nulls')
                    self.need_op(')')
                    within = (oe, desc)
                flt = self.agg_filter()
                ign = self.null_treatment()
                e = ('call', lname, args, False, distinct, within)
                w = self.over()
                if w is not None:
                    if flt is not None or distinct or within is not None:
                        raise Skip('window clause')
                    return ('wcall', e, w, ign)
                if ign:
                    raise Skip('null treatment')
                return ('filter', e, flt) if flt is not None else e
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


# the size of FLOAT: binary32 in the MySQL family, binary64 in SQLite and PostgreSQL (set by slt2coq)
FLOAT_BITS = 32
# the engine whose types are used: 'mysql' (the MySQL family) or 'postgresql' or 'sqlite' (set by slt2coq)
ENGINE = 'mysql'

# the size of REAL: binary64 in the MySQL family (without REAL_AS_FLOAT) and SQLite, binary32 in PostgreSQL
REAL_BITS = 64


def float_lit(txt):
    """A literal with an exponent (1.5e3), as an unscaled integer and a power of ten: (15, 2)."""
    t = txt.lower()
    neg = t.startswith('-')
    if neg:
        t = t[1:]
    mant, _, ex = t.partition('e')
    a, b = mant.split('.') if '.' in mant else (mant, '')
    n = int((a or '0') + (b or '')) * (-1 if neg else 1)
    return n, int(ex or '0') - len(b)


def float_coq(n, e, bits):
    """The Coq value of the float nearest to n * 10^e."""
    return '(VFl %s (%d) (%d) %s)' % ('true' if bits == 32 else 'false', n, e, '')


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


def temporal_value(txt, ty, fsp=0):
    """The Coq value of a DATE, DATETIME, TIMESTAMP or TIME column holding the text txt."""
    import datetime
    epoch = datetime.datetime(1970, 1, 1)
    t = txt.strip()
    try:
        if ty == 'date':
            d = datetime.datetime.strptime(t[:10], '%Y-%m-%d')
            return '(NullValues.VDate (%d))' % (d - epoch).days
        if ty == 'time':
            h, m, s = t.split(':')
            us = ((int(h) * 60 + int(m)) * 60) * 1000000 + int(round(float(s) * 1000000))
            return '(NullValues.VTime (%d) %d)' % (us, fsp)
        fmt = '%Y-%m-%d %H:%M:%S' if ' ' in t else '%Y-%m-%d'
        frac = 0
        if '.' in t:
            t, f = t.split('.')
            # the fractional seconds are rounded to the precision of the column
            frac = int(round(float('0.' + f) * 10 ** fsp)) * 10 ** (6 - fsp)
        d = datetime.datetime.strptime(t, fmt)
        us = ((d - epoch).days * 86400 + (d - epoch).seconds) * 1000000 + frac
        return '(NullValues.VTs (%d) %d)' % (us, fsp)
    except ValueError:
        raise Skip('temporal value')


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
        # the columns merged by USING / NATURAL: name -> (alias, name, kind) or ('coalesce', l, r)
        self.merged = {}
        # the columns of SELECT * in order (alias, name, kind), when a USING join fixed it
        self.star = None

    def star_of(self, scope):
        return [(alias, n, kd) for alias, t in scope for n, kd in t.cols]

    def resolve(self, q, c):
        try:
            return self.resolve_here(q, c)
        except Skip as e:
            if self.parent is not None and str(e).startswith('unknown column'):
                return self.parent.resolve(q, c)
            raise

    def resolve_here(self, q, c):
        if q is None and c.lower() in self.merged:
            return self.merged[c.lower()]
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

AGGS = {'count', 'sum', 'avg', 'min', 'max', 'group_concat', 'bit_and', 'bit_or', 'var_pop', 'var_samp', 'variance',
        'bit_xor', 'std', 'stddev', 'stddev_pop', 'stddev_samp', 'any_value', 'json_arrayagg', 'json_agg', 'jsonb_agg',
        'bool_and', 'bool_or', 'every', 'covar_pop', 'covar_samp', 'corr', 'regr_count', 'regr_slope',
        'regr_intercept', 'regr_r2', 'regr_sxx', 'regr_syy', 'regr_sxy', 'regr_avgx', 'regr_avgy',
        'json_objectagg', 'json_object_agg', 'jsonb_object_agg', 'median', 'array_agg', 'json_group_array'}
# the aggregates of two arguments
AGGS2 = {'covar_pop', 'covar_samp', 'corr', 'regr_count', 'regr_slope', 'regr_intercept', 'regr_r2', 'regr_sxx',
         'regr_syy', 'regr_sxy', 'regr_avgx', 'regr_avgy', 'json_objectagg', 'json_object_agg', 'jsonb_object_agg'}
FUNS = {'date_add', 'date_sub', 'bin', 'oct', 'conv', 'crc32', 'inet_aton', 'inet_ntoa', 'quote', 'make_set',
        'export_set', 'weekofyear', 'sqrt', 'exp', 'ln', 'log', 'log2', 'log10', 'sin', 'cos', 'tan', 'asin', 'acos', 'atan', 'atan2', 'cot',
        'pi', 'degrees', 'radians', 'cbrt', 'abs', 'sign', 'floor', 'ceil', 'ceiling', 'round', 'truncate', 'power', 'pow', 'mod', 'greatest', 'least',
        'coalesce', 'ifnull', 'nullif', 'concat', 'concat_ws', 'length', 'char_length', 'upper', 'lower', 'trim',
        'ltrim', 'rtrim', 'reverse', 'substring', 'substr', 'mid', 'left', 'right', 'replace', 'repeat', 'locate',
        'instr', 'ucase', 'lcase', 'character_length', 'ascii', 'space', 'lpad', 'rpad', 'strcmp', 'if',
        'trim_both', 'trim_leading', 'trim_trailing', 'position', 'overlay', 'substring_index', 'translate',
        'initcap', 'ord', 'char', 'chr', 'split_part', 'format', 'strpos', 'btrim', 'quote_ident', 'quote_literal',
        'quote', 'md5', 'sha1', 'sha', 'sha2', 'hex', 'unhex', 'to_base64', 'from_base64', 'soundex', 'insert',
        'elt', 'field', 'find_in_set', 'to_hex', 'unicode', 'octet_length', 'bit_length',
        'iif', 'nvl', 'nvl2', 'decode', 'isnull', 'num_nulls', 'num_nonnulls', 'likely', 'unlikely', 'likelihood',
        'interval_index', 'regexp_like', 'regexp_instr', 'regexp_substr', 'regexp_replace', 'regexp_count',
        'substring_regex', 'extract', 'str_to_date', 'makedate', 'maketime', 'sec_to_time', 'time_to_sec',
        'from_days', 'from_unixtime', 'dayname', 'monthname', 'period_add', 'period_diff', 'timediff', 'addtime',
        'subtime', 'time_format', 'utc_date', 'utc_time', 'utc_timestamp', 'age', 'to_date', 'to_timestamp',
        'make_time', 'make_timestamp', 'make_interval', 'justify_days', 'justify_hours', 'justify_interval',
        'date_bin', 'isfinite', 'next_day', 'date_format', 'to_days', 'datediff', 'last_day', 'dayofweek',
        'dayofmonth', 'dayofyear', 'weekday', 'week', 'quarter', 'year', 'month', 'day', 'hour', 'minute',
        'second', 'microsecond', 'date', 'unix_timestamp', 'timestampdiff', 'curdate', 'now', 'sysdate',
        'date_trunc', 'date_part', 'to_char', 'make_date', 'json_set', 'json_insert', 'json_replace', 'json_remove',
        'json_array_append', 'json_array_insert', 'json_merge_patch', 'json_merge_preserve', 'json_merge',
        'json_depth', 'json_contains_path', 'json_search', 'json_overlaps', 'json_pretty', 'json_patch', 'json_quote',
        'jsonb_set', 'jsonb_insert', 'jsonb_strip_nulls', 'json_strip_nulls', 'jsonb_pretty', 'array_length',
        'cardinality', 'array_append', 'array_prepend', 'array_cat', 'array_position', 'array_positions',
        'array_remove', 'array_replace', 'array_to_string', 'string_to_array', 'array_lower', 'array_upper',
        'array_ndims', 'array_dims', 'version', 'database', 'schema', 'user', 'current_user', 'session_user',
        'system_user', 'connection_id', 'last_insert_id', 'row_count', 'found_rows', 'current_database',
        'current_schema', 'current_catalog', 'current_role', 'pg_backend_pid', 'sqlite_version', 'last_insert_rowid',
        'changes', 'total_changes'}
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
            if 'e' in txt.lower():
                n, ex = float_lit(txt)
                return '(cst (VFl false (%d) (%d)))' % (n, ex)
            if '.' in txt:
                n, sc = scaled_lit(txt)
                return '(cst (VD (%s) %d))' % (n, sc)
            return '(int (%s))' % txt
        if k == 'str':
            return '(str %s)' % coq_str(e[1])
        if k == 'null':
            return '(cst NullZ)'
        if k == 'col':
            r = self.ctx.resolve(e[1], e[2])
            if r[0] == 'coalesce':
                # the merged column of a FULL JOIN ... USING
                (la, ln, lk), (ra, rn, rk) = r[1], r[2]
                return '(fn "coalesce" [(col %s); (col %s)])' % (attr(lk, la + '.' + ln), attr(rk, ra + '.' + rn))
            alias, name, kind = r
            return '(col %s)' % attr(kind, alias + '.' + name)
        if k == 'neg':
            return '(fn "neg" [%s])' % self.ex(e[1])
        if k == 'bitnot':
            return '(fn "~" [%s])' % self.ex(e[1])
        if k == 'bin':
            op = e[1]
            if op in ('and', 'or', 'xor', '||'):
                return '(e_cond %s)' % self.cond(e) if op in ('and', 'or') and False else \
                       '(fn "%s" [%s; %s])' % (op, self.ex(e[2]), self.ex(e[3]))
            name = {'+': '+', '-': '-', '*': '*', '/': '/', '%': '%', 'div': 'div', 'mod': 'mod',
                    '&': '&', '|': '|', '<<': '<<', '>>': '>>',
                    # [^] is the exclusive or of the MySQL family, [#] that of PostgreSQL
                    '^': '#' if ENGINE == 'postgresql' else '^'}[op]
            if op == '^' and ENGINE == 'postgresql':
                name = 'power'
            return '(fn "%s" [%s; %s])' % (name, self.ex(e[2]), self.ex(e[3]))
        if k in ('cmp', 'is', 'in', 'like', 'between', 'not', 'exists', 'insub', 'quant', 'regexp', 'similar', 'cmp_array'):
            return '(e_cond %s)' % self.cond(e)
        if k == 'subq':
            cq, n = self.sub(e[1], 1)
            return '(e_sub %s)' % cq
        if k == 'row':
            raise Skip('row value')
        if k == 'temporal':
            f = {'date': 'cast_date', 'timestamp': 'cast_timestamp', 'time': 'cast_time'}[e[1]]
            if ENGINE == 'mysql' and e[1] == 'timestamp':
                f = 'cast_datetime'
            return '(fn "%s" [(str %s)])' % (f, coq_str(e[2]))
        if k == 'interval':
            return '(fn "interval" [%s; (str "%s")])' % (self.ex(e[1]), e[2])
        if k == 'pginterval':
            return '(fn "cast_interval" [(str %s)])' % coq_str(e[1])
        if k == 'cast_dec':
            return '(fn "cast_decimal" [%s; (int %d); (int %d)])' % (self.ex(e[3]), e[1], e[2])
        if k == 'filter':
            call, c = e[1], e[2]
            name, args, star, distinct = call[1], call[2], call[3], call[4]
            if name not in AGGS or distinct or (len(call) > 5 and call[5] is not None):
                raise Skip('filter clause')
            if star:
                return '(agg_filter "count" (int 1) %s)' % self.cond(c)
            if len(args) != 1 or name in AGGS2:
                raise Skip('filter clause')
            return '(agg_filter "%s" %s %s)' % (name, self.ex(args[0]), self.cond(c))
        if k == 'bool':
            return '(cst (NullValues.Value_bool (Some %s)))' % ('true' if e[1] else 'false')
        if k == 'icol':
            return '(col (Attr_Z "%s"))' % e[1]
        if k == 'wcall':
            raise Skip('window function in this position')
        if k == 'cast':
            ty = e[1]
            f = {'signed': 'cast_int', 'unsigned': 'cast_unsigned', 'integer': 'cast_int', 'int': 'cast_int', 'bigint': 'cast_int', 'smallint': 'cast_int', 'char': 'cast_string', 'varchar': 'cast_string', 'text': 'cast_string', 'decimal': 'cast_numeric', 'numeric': 'cast_numeric', 'real': 'cast_double', 'float': 'cast_double', 'double': 'cast_double'}.get(ty)
            if ENGINE == 'postgresql':
                f = {'bigint': 'cast_bigint', 'smallint': 'cast_smallint', 'real': 'cast_float4', 'float': 'cast_float8',
                     'double': 'cast_float8', 'int2': 'cast_smallint', 'int4': 'cast_int', 'int8': 'cast_bigint',
                     'float4': 'cast_float4', 'float8': 'cast_float8', 'bool': 'cast_bool', 'boolean': 'cast_bool',
                     'date': 'cast_date', 'time': 'cast_time', 'timestamp': 'cast_timestamp',
                     'timestamptz': 'cast_timestamptz', 'interval': 'cast_interval', 'json': 'cast_json',
                     'jsonb': 'cast_jsonb', 'bpchar': 'cast_string', 'name': 'cast_string'}.get(ty, f)
            if ENGINE == 'sqlite':
                f = {'real': 'cast_real', 'float': 'cast_real', 'double': 'cast_real'}.get(ty, f)
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
        if k == 'call' and len(e) > 5 and e[5] is not None:
            name, args, (oe, desc) = e[1], e[2], e[5]
            d = 'Desc' if desc else 'Asc'
            if name in ('percentile_cont', 'percentile_disc') and len(args) == 1:
                return '(agg_x "%s" %s (Some %s) [o_by %s %s])' % (name, self.ex(oe), self.ex(args[0]), self.ex(oe), d)
            if name == 'mode' and not args:
                return '(agg_x "mode" %s None [o_by %s %s])' % (self.ex(oe), self.ex(oe), d)
            if name in ('rank', 'dense_rank', 'percent_rank', 'cume_dist') and len(args) == 1:
                return '(agg_x "hyp_%s_%s" %s (Some %s) [o_by %s %s])' % (name, 'desc' if desc else 'asc', self.ex(oe),
                                                                         self.ex(args[0]), self.ex(oe), d)
            raise Skip('within group ' + name)
        if k == 'call' and e[1] == 'grouping' and e[2]:
            # GROUPING (a, b, ...): the bits of the arguments which are not grouped, the first one highest
            gs = ['(grouping %s)' % self.ex(a) for a in e[2]]
            out = gs[0]
            for g_ in gs[1:]:
                out = '(fn "+" [(fn "*" [%s; int 2]); %s])' % (out, g_)
            return out
        if k == 'call':
            name, args, star, distinct = e[1], e[2], e[3], e[4]
            if name in ('max', 'min') and ENGINE == 'sqlite' and len(args) > 1 and not star:
                return '(fn "%s_scalar" [%s])' % (name, '; '.join(self.ex(a) for a in args))
            if name in AGGS:
                if star:
                    if name != 'count':
                        raise Skip('star')
                    return 'count_star'
                if name in AGGS2 and len(args) == 2 and not distinct:
                    return '(agg_x "%s" %s (Some %s) [])' % (name, self.ex(args[0]), self.ex(args[1]))
                if name == 'count' and distinct and len(args) == 2 and ENGINE == 'mysql':
                    return '(agg_x "count_distinct2" %s (Some %s) [])' % (self.ex(args[0]), self.ex(args[1]))
                if len(args) != 1 or name in AGGS2:
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
        if k == 'bool':
            return 'c_true' if e[1] else '(c_not c_true)'
        if k == 'bin' and e[1] == 'and':
            return '(c_and %s %s)' % (self.cond(e[2]), self.cond(e[3]))
        if k == 'bin' and e[1] == 'or':
            return '(c_or %s %s)' % (self.cond(e[2]), self.cond(e[3]))
        if k == 'not':
            return '(c_not %s)' % self.cond(e[1])
        if k == 'cmp':
            op = {'=': '=', '<>': '<>', '!=': '<>', '<': '<', '<=': '<=', '>': '>', '>=': '>=', '<=>': '<=>',
                  '~': '~', '~*': '~*', '!~': '!~', '!~*': '!~*'}[e[1]]
            if e[2][0] == 'row' or e[3][0] == 'row':
                if e[2][0] != 'row' or e[3][0] != 'row' or len(e[2][1]) != len(e[3][1]) or \
                        op not in ('=', '<>', '<', '<=', '>', '>='):
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
            esc = e[4] if len(e) > 4 else None
            ci = e[5] if len(e) > 5 else False
            name = ('ilike' if ci else 'like') + ('_escape' if esc is not None else '')
            if not ci and esc is None:
                name = 'like'
            name = ('not ' if e[1] else '') + name
            args = [self.ex(e[2]), self.ex(e[3])] + ([self.ex(esc)] if esc is not None else [])
            return '(pred "%s" [%s])' % (name, '; '.join(args))
        if k == 'cmp_array':
            op = {'=': '=', '<>': '<>', '!=': '<>', '<': '<', '<=': '<=', '>': '>', '>=': '>='}[e[1]]
            return '(pred "%s%s" [%s; %s])' % (op, e[2], self.ex(e[3]), self.ex(e[4]))
        if k == 'regexp':
            return '(pred "%s" [%s; %s])' % ('not regexp' if e[1] else 'regexp', self.ex(e[2]), self.ex(e[3]))
        if k == 'similar':
            args = [self.ex(e[2]), self.ex(e[3])] + ([self.ex(e[4])] if e[4] is not None else [])
            return '(pred "%s" [%s])' % ('not similar to' if e[1] else 'similar to', '; '.join(args))
        if k == 'between':
            name = ('not between' if e[1] else 'between') + (' symmetric' if len(e) > 5 and e[5] else '')
            return '(pred "%s" [%s; %s; %s])' % (name, self.ex(e[2]), self.ex(e[3]), self.ex(e[4]))
        return '(c_expr %s)' % self.ex(e)


def has_wcall(e):
    if isinstance(e, list):
        return any(has_wcall(x) for x in e)
    if not isinstance(e, tuple):
        return False
    if e and e[0] == 'wcall':
        return True
    return any(has_wcall(x) for x in e[1:])


def rollup_sets(l):
    return [l[:k] for k in range(len(l), -1, -1)]


RANKING = {'row_number': 'w_row_number', 'rank': 'w_rank', 'dense_rank': 'w_dense_rank',
           'percent_rank': 'w_percent_rank', 'cume_dist': 'w_cume_dist'}


def has_call(e, name):
    if isinstance(e, list):
        return any(has_call(x, name) for x in e)
    if not isinstance(e, tuple):
        return False
    if e[0] == 'call' and e[1] == name:
        return True
    return any(has_call(x, name) for x in e[1:])


def is_agg_call(e):
    # the scalar max (a, b, ...) and min of SQLite are not aggregates; WITHIN GROUP makes an aggregate
    if e[0] == 'call' and len(e) > 5 and e[5] is not None:
        return True
    if e[0] == 'filter':
        return True
    if e[0] == 'call' and e[1] == 'grouping':
        return True
    return (e[0] == 'call' and e[1] in AGGS and
            not (ENGINE == 'sqlite' and e[1] in ('max', 'min') and len(e[2]) > 1))


def has_agg(e):
    if not isinstance(e, tuple):
        return False
    if is_agg_call(e):
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
    if is_agg_call(e):
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
            # an unnamed column (an expression without alias) cannot be referenced: a placeholder name
            names = [x if x is not None else '#c%d' % i for i, x in enumerate(names)]
            if len(set(x.lower() for x in names)) != len(names):
                raise Skip('derived column names')
            t = Table(alias, [(nm, 'Z') for nm in names])
            ctx.scope.append((alias, t))
            ren = '; '.join('((Attr_Z "c%d"), %s)' % (i, attr('Z', alias + '.' + nm)) for i, nm in enumerate(names))
            return '(from_as %s [%s])' % (cq, ren)
        if k == 'tfun':
            name, args, ord_, alias, cols = f[1], f[2], f[3], f[4], f[5]
            # the default columns of the functions
            defaults = {'json_each': ['key', 'value', 'type', 'atom', 'id', 'parent', 'fullkey', 'path'],
                        'jsonb_each': ['key', 'value'], 'json_each_text': ['key', 'value'],
                        'jsonb_each_text': ['key', 'value']}
            if cols is None:
                cols = defaults.get(name, [alias])
                if ord_:
                    cols = cols + ['ordinality']
            if any(a.lower() == alias.lower() for a, _ in ctx.scope):
                raise Skip('duplicate alias')
            tr = Tr(ctx, self)
            cargs = '; '.join(tr.ex(a) for a in args)
            t = Table(alias, [(c, 'Z') for c in cols])
            ctx.scope.append((alias, t))
            atts = '; '.join(attr('Z', alias + '.' + c) for c in cols)
            return '(from_fun "%s" [%s] %s [%s])' % (name, cargs, 'true' if ord_ else 'false', atts)
        if k == 'join':
            jt, l, r, c = f[1], f[2], f[3], f[4]
            using = f[5] if len(f) > 5 else None
            nl = len(ctx.scope)
            lt = self.frm(l, ctx)
            lscope = ctx.scope[nl:]
            # the left operand may itself be a join with USING, whose * is fixed
            lstar = ctx.star if ctx.star is not None else ctx.star_of(lscope)
            nr = len(ctx.scope)
            rt = self.frm(r, ctx)
            rscope = ctx.scope[nr:]
            rstar = ctx.star_of(rscope)
            ty = {'cross': 'J_Inner', 'inner': 'J_Inner', 'left': 'J_Left', 'right': 'J_Right', 'full': 'J_Full'}[jt]
            if using is not None:
                # USING (c, ...) or NATURAL: the common columns are equal, and merged
                lnames = [n for (_, n, _) in lstar]
                rnames = [n for (_, n, _) in rstar]
                if using == 'natural':
                    cols = [n for n in lnames if n.lower() in [x.lower() for x in rnames]]
                else:
                    cols = using
                pairs = []
                for cn in cols:
                    lc = [x for x in lstar if x[1].lower() == cn.lower()]
                    rc = [x for x in rstar if x[1].lower() == cn.lower()]
                    if len(lc) != 1 or len(rc) != 1 or lc[0][0] == 'merged' or rc[0][0] == 'merged':
                        raise Skip('using column ' + cn)
                    pairs.append((lc[0], rc[0]))
                conds = ['(pred "=" [(col %s); (col %s)])' % (attr(a[2], a[0] + '.' + a[1]), attr(b[2], b[0] + '.' + b[1]))
                         for a, b in pairs]
                cond = 'c_true'
                for cc in conds:
                    cond = cc if cond == 'c_true' else '(c_and %s %s)' % (cond, cc)
                merged_keys = []
                for a, b in pairs:
                    if jt == 'full':
                        ctx.merged[a[1].lower()] = ('coalesce', a, b)
                    elif jt == 'right':
                        ctx.merged[a[1].lower()] = b
                    else:
                        ctx.merged[a[1].lower()] = a
                    merged_keys.append(a[1].lower())
                # SELECT *: the merged columns, then the others of the left, then of the right; a RIGHT JOIN
                # is a LEFT JOIN of the operands swapped (MySQL), so its right operand comes first
                lrest = [x for x in lstar if x[1].lower() not in merged_keys]
                rrest = [x for x in rstar if x[1].lower() not in merged_keys]
                ctx.star = ([('merged', a[1], a[2]) for a, b in pairs]
                            + (rrest + lrest if jt == 'right' else lrest + rrest))
                return '(join %s %s %s %s)' % (ty, lt, rt, cond)
            tr = Tr(ctx, self)
            cond = tr.cond(c) if c is not None else 'c_true'
            if ctx.star is not None:
                ctx.star = ctx.star + [x for x in rstar]
            # a table function on the right is lateral: its arguments may read the left rows
            return '(%s %s %s %s %s)' % ('join_lateral' if r[0] == 'tfun' else 'join', ty, lt, rt, cond)
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
        if k == 'values':
            rows = q[1]
            if any(has_agg(e) or has_wcall(e) for r in rows for e in r):
                raise Skip('values with aggregates')
            tr = Tr(Ctx(self.tables, parent), self)
            n = len(rows[0])
            atts = '; '.join('(Attr_Z "c%d")' % i for i in range(n))
            body = '; '.join('[%s]' % '; '.join(tr.ex(e) for e in r) for r in rows)
            return '(values_ [%s] [%s])' % (atts, body), n, False, [None] * n
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

    def window_select(self, s, exprs, order, limit, parent, tr):
        """A query with window functions: an inner query computes the arguments, the partition and order
        keys of the windows and the other parts of the select items (with the WHERE, GROUP BY and HAVING of
        the query); SQ_Window adds one column per window function; an outer query computes the select
        items from these columns, then DISTINCT, ORDER BY, LIMIT."""
        _, distinct, items, frm, where, group, having = s
        inner = []
        wins = []

        def icol(e):
            for i, x in enumerate(inner):
                if x == e:
                    return ('icol', 'c%d' % i)
            inner.append(e)
            return ('icol', 'c%d' % (len(inner) - 1))

        def lift(e):
            if isinstance(e, list):
                return [lift(x) for x in e]
            if not isinstance(e, tuple):
                return e
            if e[0] == 'wcall':
                for k, w in enumerate(wins):
                    if w == e:
                        return ('icol', 'w%d' % k)
                wins.append(e)
                return ('icol', 'w%d' % (len(wins) - 1))
            if not has_wcall(e):
                return icol(e)
            if e[0] in ('subq', 'exists', 'insub', 'quant'):
                raise Skip('window function in a subquery')
            return tuple([e[0]] + [lift(x) for x in e[1:]])

        names = {a.lower(): i for i, (_, a) in enumerate(exprs) if a}
        outer = [lift(e) for e, _ in exprs]
        okeys = []
        for e, d in (order or []):
            if e[0] == 'col' and e[1] is None and e[2].lower() in names:
                okeys.append((('item', names[e[2].lower()]), d))
            elif e[0] == 'num' and '.' not in e[1] and 1 <= int(e[1]) <= len(exprs):
                okeys.append((('item', int(e[1]) - 1), d))
            else:
                okeys.append((lift(e), d))
        if limit is not None and not order:
            raise Skip('limit without order by (the rows are implementation defined)')
        # the windows
        wl = []
        for k, (_, call, spec, ign) in enumerate(wins):
            base = spec[1]
            part, wo, frame = spec[2], spec[3], spec[4]
            if base is not None:
                if base not in NAMED_WINDOWS:
                    raise Skip('unknown window ' + base)
                b = NAMED_WINDOWS[base]
                if b[1] is not None:
                    raise Skip('window chain')
                part = b[2]
                wo = wo or b[3]
                frame = frame or b[4]
            lp = ['(col (Attr_Z "%s"))' % icol(x)[1] for x in part]
            lo = []
            for x, d, nulls in wo:
                c = '(col (Attr_Z "%s"))' % icol(x)[1]
                dd = 'Asc' if d == 'asc' else 'Desc'
                if nulls is None:
                    lo.append('(o_by %s %s)' % (c, dd))
                else:
                    lo.append('(o_by_nulls %s %s %s)' % (c, dd, 'Nulls_First' if nulls == 'first' else 'Nulls_Last'))
            if frame is None:
                fr = 'default_frame' if wo else 'whole_partition'
            else:
                mode, lo_b, hi_b, excl = frame
                offsets = any(b[0] in ('p', 'f') for b in (lo_b, hi_b))

                def cb(b):
                    if b[0] == 'up':
                        return 'Unbounded_Preceding'
                    if b[0] == 'uf':
                        return 'Unbounded_Following'
                    if b[0] == 'cr':
                        return 'Current_Row'
                    if mode == 'range':
                        return '(%s (QArith_base.Qmake (%d) 1))' % ('Preceding_Q' if b[0] == 'p' else 'Following_Q', b[1])
                    return '(%s %d)' % ('Preceding' if b[0] == 'p' else 'Following', b[1])
                if mode == 'range' and not offsets:
                    ctor = 'Frame_Groups'
                elif mode == 'range':
                    if len(wo) != 1:
                        raise Skip('range frame keys')
                    ctor = 'Frame_Range'
                else:
                    ctor = {'rows': 'Frame_Rows', 'groups': 'Frame_Groups'}[mode]
                fr = '(%s %s %s)' % (ctor, cb(lo_b), cb(hi_b))
                if excl:
                    fr = '(Frame_Excl %s %s)' % (fr, excl)
            name, args, star = call[1], call[2], call[3]

            def lit_nat(x):
                if x[0] != 'num' or '.' in x[1] or x[1].startswith('-'):
                    raise Skip('window function argument')
                return int(x[1])
            if name in RANKING and not args:
                f = RANKING[name]
            elif name == 'ntile' and len(args) == 1:
                f = '(w_ntile %d)' % lit_nat(args[0])
            elif name in ('lag', 'lead') and 1 <= len(args) <= 3:
                n_ = lit_nat(args[1]) if len(args) > 1 else 1
                dflt = '(col (Attr_Z "%s"))' % icol(args[2])[1] if len(args) > 2 else '(cst NullZ)'
                f = '(w_%s (col (Attr_Z "%s")) %d %s)' % (name, icol(args[0])[1], n_, dflt)
            elif name in ('first_value', 'last_value') and len(args) == 1:
                f = '(w_%s (col (Attr_Z "%s")) %s)' % (name, icol(args[0])[1], fr)
            elif name == 'nth_value' and len(args) == 2:
                f = '(w_nth_value (col (Attr_Z "%s")) %d %s)' % (icol(args[0])[1], lit_nat(args[1]), fr)
            elif name in AGGS and star and name == 'count':
                f = '(w_agg "count(*)" (int 1) %s)' % fr
            elif name in AGGS and len(args) == 1 and name not in AGGS2 and name != 'group_concat':
                f = '(w_agg "%s" (col (Attr_Z "%s")) %s)' % (name, icol(args[0])[1], fr)
            else:
                raise Skip('window function ' + name)
            if ign:
                f = '(w_opts %s true false)' % f
            wl.append('(w_as %s [%s] [%s] (Attr_Z "w%d"))' % (f, '; '.join(lp), '; '.join(lo), k))
        if not inner:
            icol(('num', '1'))
        inner_s = ('select', False, [('item', x, None) for x in inner], frm, where, group, having)
        body, _, _, _ = self.select(inner_s, None, None, parent)
        win = '(window %s [%s])' % (body, '; '.join(wl))
        n = len(outer)
        sel = ['(as_ %s (Attr_Z "c%d"))' % (tr.ex(e), i) for i, e in enumerate(outer)]
        keys = []
        for e, d in okeys:
            dd = 'Asc' if d == 'asc' else 'Desc'
            if e[0] == 'item':
                keys.append('(o_by (col (Attr_Z "c%d")) %s)' % (e[1], dd))
                continue
            idx = next((i for i, x in enumerate(outer) if x == e), None)
            if idx is None:
                if distinct:
                    raise Skip('order by a hidden column of a distinct query')
                idx = len(sel)
                sel.append('(as_ %s (Attr_Z "c%d"))' % (tr.ex(e), idx))
            keys.append('(o_by (col (Attr_Z "c%d")) %s)' % (idx, dd))
        body = '(select_full %s (s_list [%s]) [(from_query %s)] c_true g_fine c_true)' % (
            'Set_Distinct' if distinct else 'Set_All', '; '.join(sel), win)
        ordered = False
        if order:
            off, lim = (limit if limit else (0, None))
            body = '(order_limit %s [%s] %s %s)' % (body, '; '.join(keys),
                                                     'None' if off == 0 else '(Some %d%%N)' % off,
                                                     'None' if lim is None else '(Some %d%%N)' % lim)
            ordered = True
        outnames = [a if a else (e[2] if e[0] == 'col' else None) for e, a in exprs]
        return body, n, ordered, outnames

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
                if ctx.star is not None:
                    for alias, n, kd in ctx.star:
                        exprs.append((('col', None if alias == 'merged' else alias, n), n))
                    continue
                for alias, t in ctx.scope:
                    for n, kd in t.cols:
                        exprs.append((('col', alias, n), n))
            else:
                exprs.append((it[1], it[2]))
        if any(has_wcall(e) for e, _ in exprs) or any(has_wcall(e) for e, _ in (order or [])):
            return self.window_select(s, exprs, order, limit, parent, tr)
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

        def subst_deep(e, alias_first):
            """an alias inside an expression of ORDER BY or HAVING: allowed by MySQL and SQLite (an alias which
            is not a column of the tables, or any alias when [alias_first]); PostgreSQL only takes a bare alias
            in ORDER BY, and none in HAVING"""
            if isinstance(e, list):
                return [subst_deep(x, alias_first) for x in e]
            if not isinstance(e, tuple):
                return e
            if e[0] == 'col' and e[1] is None and e[2].lower() in names:
                if alias_first:
                    return exprs[names[e[2].lower()]][0]
                try:
                    ctx.resolve(None, e[2])
                    return e
                except Skip:
                    if ENGINE in ('mysql', 'sqlite'):
                        return exprs[names[e[2].lower()]][0]
                    raise
            if e[0] in ('subq', 'exists', 'insub', 'quant'):
                return e
            return tuple([e[0]] + [subst_deep(x, alias_first) for x in e[1:]])
        if having is not None:
            having = subst_deep(having, ENGINE in ('mysql',))
        if order:
            order = [(subst_deep(e, False) if e[0] != 'col' else e, d) for e, d in order]
        if limit is not None and not order:
            # LIMIT without ORDER BY: any n rows of the result (TODO 3.10); only at the top of the query
            if s is getattr(self, 'top_select', None) and limit[0] == 0 and limit[1] is not None:
                self.limit_any = limit[1]
                limit = None
            else:
                raise Skip('limit without order by (the rows are implementation defined)')
        if any(has_call(e, 'group_concat') for e, _ in exprs):
            raise Skip('group_concat (the order of the elements is implementation defined)')
        w = tr.cond(where) if where is not None else 'c_true'
        if where is not None and has_agg(where):
            raise Skip('aggregate in where')
        agg_query = any(has_agg(e) for e, _ in exprs) or (having is not None and has_agg(having))
        if isinstance(group, tuple) and group[0] == 'sets':
            g = '(g_sets [%s])' % '; '.join('[%s]' % '; '.join(tr.ex(subst(x)) for x in st) for st in group[1])
            group = [x for st in group[1] for x in st]
        elif group is not None:
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
                if is_agg_call(e):
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


def split_statements(s):
    """the statements of a text, at the ';' outside quotes (each keeps its ';')"""
    out, cur, inq, esc = [], '', None, False
    for c in s:
        cur += c
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
        elif c == ';':
            out.append(cur.strip())
            cur = ''
    if cur.strip():
        out.append(cur.strip())
    return out or [s]


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
    if p.kw('temporary') or (p.peek()[0] in ('id', 'kw') and p.peek()[1].lower() in ('temp', 'unlogged')):
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
                if ty == 'char':
                    width = ('char', width)
            if ty in ('float', 'real', 'double', 'float4', 'float8'):
                bits = {'double': 64, 'float8': 64, 'float4': 32, 'real': REAL_BITS}.get(ty, FLOAT_BITS)
                width = ('flt', bits)
            fsp = 0
            if ty in ('datetime', 'timestamp', 'time') and p.op('(') and p.peek(1)[0] == 'num':
                fsp = int(p.peek(1)[1])
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
            if ty in ('date', 'datetime', 'timestamp', 'time') and ENGINE != 'sqlite':
                kind = 'Z'
                width = ('tmp', ty, fsp)
            elif ty in NUM_TYPES:
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
                elif t[0] in ('id', 'kw') and t[1].lower() == 'unsigned' and ty in NUM_TYPES and ENGINE == 'mysql':
                    width = ('uns', ty)
                elif t[0] in ('id', 'kw') and t[1].lower() == 'unsigned' and ENGINE == 'mysql' and \
                        ty in ('float', 'double', 'real', 'decimal', 'numeric'):
                    pass  # UNSIGNED on a float or a decimal only rejects the negative values (an error: not replayed)
                elif t[0] in ('id', 'kw') and t[1].lower() in ('collate', 'charset', 'character', 'zerofill', 'default', 'auto_increment', 'generated', 'as', 'binary', 'unsigned', 'on', 'check', 'references'):
                    raise Skip('column option ' + t[1])
                p.i += 1
            cols.append((cname, kind))
            if width is None and ENGINE == 'postgresql' and ty in ('int', 'integer', 'smallint', 'int4', 'int2'):
                width = ('pgint', 16 if ty in ('smallint', 'int2') else 32)
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
    if lit[0] == 'str' and isinstance(limit, tuple) and limit[0] == 'char' and len(lit[1]) > limit[1]:
        raise Skip('truncation')
    if lit[0] == 'str' and isinstance(limit, int) and len(lit[1]) > limit:
        raise Skip('truncation')
    if lit[0] == 'num' and isinstance(limit, tuple) and limit[0] not in ('dec', 'flt', 'uns', 'pgint', 'char', 'tmp') and '.' not in lit[1] and 'e' not in lit[1].lower() and not (limit[0] <= int(lit[1]) <= limit[1]):
        raise Skip('out of range')
    if lit[0] == 'null':
        return {'Z': 'NullZ', 'S': 'NullS', 'Q': 'NullQ'}[kind]
    if kind == 'S':
        if lit[0] == 'str':
            # a CHAR(n) column of the MySQL family returns its value without the trailing spaces
            # (unless PAD_CHAR_TO_FULL_LENGTH)
            if isinstance(limit, tuple) and limit[0] == 'char' and ENGINE == 'mysql':
                return 'VS %s' % coq_str(lit[1].rstrip(' '))
            return 'VS %s' % coq_str(lit[1])
        raise Skip('number into string column')
    if lit[0] == 'str' and isinstance(limit, tuple) and limit[0] == 'tmp':
        return temporal_value(lit[1], limit[1], limit[2])
    if lit[0] == 'str':
        raise Skip('string into numeric column')
    txt = lit[1]
    if isinstance(limit, tuple) and limit[0] == 'tmp':
        raise Skip('number into temporal column')
    if kind == 'Z':
        if '.' in txt:
            raise Skip('decimal into int column')
        if isinstance(limit, tuple) and limit[0] == 'uns':
            if int(txt) < 0 or int(txt) >= 2 ** {'tinyint': 8, 'smallint': 16, 'mediumint': 24, 'int': 32, 'integer': 32}.get(limit[1], 64):
                raise Skip('out of range')
            return 'VU (%s)' % txt
        if isinstance(limit, tuple) and limit[0] == 'pgint':
            if not (-2 ** (limit[1] - 1) <= int(txt) < 2 ** (limit[1] - 1)):
                raise Skip('out of range')
            return '(NullValues.Value_I (Some ((%s)%%Z, %d%%nat)))' % (txt, limit[1])
        return 'VZ (%s)' % txt
    if isinstance(limit, tuple) and limit[0] == 'dec':
        return 'VD (%s) %d' % (round_to_scale(txt, limit[1]), limit[1])
    if isinstance(limit, tuple) and limit[0] == 'flt':
        if 'e' in txt.lower():
            n, ex = float_lit(txt)
        else:
            n, sc = scaled_lit(txt)
            n, ex = int(n), -sc
        return 'VFl %s (%d) (%d)' % ('true' if limit[1] == 32 else 'false', n, ex)
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
    # the warnings which a test prints after a result (--enable_warnings) are not rows
    for k, l in enumerate(lines):
        if l == 'Level\tCode\tMessage':
            lines = lines[:k]
            break
    blank = 0
    while lines and lines[-1].strip() == '':
        lines.pop()
        blank += 1
    if not lines:
        return None
    if len(lines) == 1 and ncols == 1 and not lines[0].startswith(('ERROR', '+')):
        # a header alone is an empty result; followed by one blank line, a row holding ''
        # (several blank lines are ambiguous with the separators, and skipped)
        return [] if blank == 0 else [['']] if blank == 1 else None
    # an error: [ERROR 1064 ...] (mysqltest), [Error 1582 (42000): ...] (TiDB)
    if lines[0].startswith('ERROR') or re.match(r'^Error \d+', lines[0]):
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
            # several statements on one line: each is a statement of the script
            parts = split_statements(cur.strip())
            for k, part in enumerate(parts):
                stmts.append((part, pending_error and k == 0))
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


LENIENT = False
USER_FUNCS = set()


def process(path, out, stats):
    USER_FUNCS.clear()
    VIEWS.clear()
    import os
    if os.path.getsize(path) > 3000000:
        stats['skipped_files'] += 1
        return
    lines = open(path, encoding='utf-8', errors='replace').read().split('\n')
    if lines and lines[-1] == '':
        lines.pop()  # the end of the last line, not an empty line
    tables = {}
    blocks = split_blocks(lines)
    base = path.split('/')[-1].replace('.result', '')
    cases = []
    # the statements which a loop or an eval of the test script runs are not in the result file
    # the test script: OceanBase r/mysql/x.result -> t/x.test; TiDB and MySQL r/x.result -> t/x.test;
    # MariaDB main/x.result -> main/x.test
    test_path = path
    test_src = None
    for pat, rep in ((r'/r/mysql/([^/]*)\.result$', r'/t/\1.test'), (r'/r/([^/]*)\.result$', r'/t/\1.test'),
                     (r'/integrationtest/r/(.*)\.result$', r'/integrationtest/t/\1.test'),
                     (r'\.result$', '.test')):
        cand = re.sub(pat, rep, path)
        if cand != path and os.path.exists(cand):
            test_path = cand
            break
    items = None
    try:
        if test_path == path:
            raise OSError('no test script')
        test_src = open(test_path, encoding='utf-8', errors='replace').read()
        src_check = test_src
        if LENIENT:
            # (--lenient) the includes which only check the server (have_innodb, not_embedded, ...) do not
            # change the data
            src_check = re.sub(r'(?im)^\s*-?-?source\s+include/(have|not|no|default|big|count_sessions|'
                               r'wait_until_count_sessions|have_[a-z0-9_]*)[a-z0-9_]*\.inc\s*;?\s*$', '', test_src)
        m_unsafe = re.search(r'^\s*(while|eval|let|--source|source|--exec|--perl|--eval|connect|connection|delimiter)\b',
                             src_check, re.I | re.M)
        if LENIENT and m_unsafe:
            # (--lenient) the statements before the first loop, variable or connection are replayed
            test_src = src_check[:m_unsafe.start()]
            src_check = test_src
            stats['truncated_files'] = stats.get('truncated_files', 0) + 1
        if re.search(r'^\s*(while|eval|let|--source|source|--exec|--perl|--eval)\b', src_check, re.I | re.M):
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
    elif test_src:
        # the lines which --echo prints are not rows of a result
        echoed = set(m.strip() for m in re.findall(r'(?im)^\s*-?-?echo\s+(.*?);?\s*$', test_src))
        echoed |= set(e.rstrip(';').strip() for e in list(echoed))
        if echoed:
            items = [(st, ([l for l in res if l.strip() not in echoed] if res is not None else None), err)
                     for st, res, err in items]
    unsafe = re.compile(r'\b(rollback|savepoint|create\s+procedure|create\s+function|delimiter|call\s|prepare\s|load\s+data|set\s+autocommit|start\s+transaction|begin\b|xa\s)', re.I)
    if not LENIENT and any(unsafe.search(stmt) for stmt, _, _ in items):
        stats['skipped_files'] += 1
        return
    in_txn = False
    for bi, (stmt, res, expect_err) in enumerate(items):
        s = stmt.strip()
        if len(s) > 20000:
            continue
        if LENIENT and re.match(r'^\s*set\s+(session\s+|global\s+|@@session\.|@@global\.|@@)?(sql_mode|names|'
                                r'character_set_\w+|collation_\w+|time_zone|div_precision_increment|'
                                r'tidb_enable_new_collation\w*|default_collation\w*|group_concat_max_len|'
                                r'tidb_enable_noop_functions)\b|^\s*set\s+(character\s+set|charset)\b', s, re.I):
            # (--lenient) the semantics of the rest of the script depends on the new sql_mode, collation, character
            # set, time zone or precision: stop
            stats['skip']['after a change of the session'] = stats['skip'].get('after a change of the session', 0) + len(items) - bi
            break
        if LENIENT:
            # (--lenient) a transaction, a routine or a statement which the translator cannot follow makes
            # the tables which it mentions unreliable, instead of skipping the file
            if re.match(r'^\s*(begin|start\s+transaction)\b', s, re.I):
                in_txn = True
            ends = re.match(r'^\s*(commit|rollback|end|abort)\b', s, re.I)
            # a child (INHERITS, PARTITION OF) adds its rows to the parent: the parent is unreliable
            for m in re.finditer(r'\b(?:inherits\s*\(\s*|partition\s+of\s+)(\w+)', s, re.I):
                if m.group(1).lower() in tables:
                    tables[m.group(1).lower()].ok = False
            # a data-modifying WITH, SELECT INTO, CREATE TABLE AS: the tables mentioned are unreliable
            if re.match(r'^\s*with\b', s, re.I) and re.search(r'\b(insert|update|delete|merge)\b', s, re.I) or \
               re.search(r'\binto\s+(temp\w*\s+|unlogged\s+)?(table\s+)?\w+\s+from\b', s, re.I) and re.match(r'^\s*select', s, re.I):
                for t in tables.values():
                    if re.search(r'\b' + re.escape(t.name) + r'\b', s, re.I):
                        t.ok = False
                stats['skip']['data-modifying statement'] = stats['skip'].get('data-modifying statement', 0) + 1
                continue
            if in_txn or unsafe.search(s) or re.match(r'^\s*(create\s+(or\s+replace\s+)?(function|procedure|'
                                                      r'aggregate|operator|type|domain|cast|rule|trigger)|do\b)', s, re.I):
                for t in tables.values():
                    if re.search(r'\b' + re.escape(t.name) + r'\b', s, re.I):
                        t.ok = False
                if re.match(r'^\s*create\s+(or\s+replace\s+)?(function|aggregate|operator|cast)', s, re.I):
                    m = re.search(r'(function|aggregate)\s+([\w.]+)', s, re.I)
                    if m:
                        USER_FUNCS.add(m.group(2).split('.')[-1].lower())
                if ends:
                    in_txn = False
                stats['skip']['transaction or routine'] = stats['skip'].get('transaction or routine', 0) + 1
                continue
        if USER_FUNCS and re.search(r'\b(' + '|'.join(map(re.escape, USER_FUNCS)) + r')\s*\(', s, re.I):
            stats['skip']['user-defined function'] = stats['skip'].get('user-defined function', 0) + 1
            continue
        failed = expect_err or (res is not None and any(l.startswith('ERROR') or re.match(r'^Error \d+', l) for l in res))
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
        # a parenthesised query: (SELECT ...) UNION (SELECT ...)
        if head == '' and toks[0] == ('op', '(') and len(toks) > 1 and toks[1][0] in ('id', 'kw') and \
                toks[1][1].lower() in ('select', 'with', 'values'):
            head = 'select'
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
            elif head == 'create' and re.match(r'^\s*create\s+(or\s+replace\s+)?(temp|temporary\s+)?\s*view\b', s, re.I):
                p = P(toks)
                p.i = 1
                if p.eat_kw('or'):
                    p.i += 1
                if p.peek()[1].lower() in ('temp', 'temporary'):
                    p.i += 1
                p.i += 1  # VIEW
                vname = p.ident().lower()
                vcols = None
                if p.eat_op('('):
                    vcols = [p.ident()]
                    while p.eat_op(','):
                        vcols.append(p.ident())
                    p.need_op(')')
                p.need_kw('as')
                VIEWS[vname] = (p.query(), vcols)
            elif head == 'create':
                # the parents of the foreign keys: a change of a parent can cascade to the child
                refs = [toks[i + 1][1].lower() for i in range(len(toks) - 1)
                        if toks[i][0] in ('id', 'kw') and toks[i][1].lower() == 'references'
                        and toks[i + 1][0] in ('id', 'kw')]
                try:
                    name, cols, limits = parse_create(toks)
                    tables[name.lower()] = Table(name, cols)
                    tables[name.lower()].limits = limits
                    tables[name.lower()].parents = refs
                except Skip:
                    # an unsupported table: remember that it exists but is unreliable
                    p = P(toks)
                    p.i = 1
                    while p.kw('temporary') or (p.peek()[0] in ('id', 'kw') and p.peek()[1].lower() in ('temp', 'unlogged')):
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
            elif head == 'insert' and re.match(r'^\s*insert\s+(ignore\s+)?(into\s+)?(\w+)', s, re.I) and \
                    re.match(r'^\s*insert\s+(ignore\s+)?(into\s+)?(\w+)', s, re.I).group(3).lower() in VIEWS:
                # an insert through a view: the tables of the view (any of them) are unreliable
                for t in tables.values():
                    t.ok = False
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
                            # ON DUPLICATE KEY UPDATE can cascade to the children
                            for t in tables.values():
                                if n.lower() in getattr(t, 'parents', []):
                                    t.ok = False
                    except Skip:
                        pass
            elif head in ('update', 'delete', 'replace', 'truncate', 'alter', 'rename', 'insert') and \
                    any(re.search(r'\b' + re.escape(v) + r'\b', s, re.I) for v in VIEWS):
                # a change through a view: the tables of the view (any of them) are unreliable
                for t in tables.values():
                    t.ok = False
            elif head in ('update', 'delete', 'replace', 'truncate', 'alter', 'rename'):
                changed = set()
                for t in tables.values():
                    if re.search(r'\b' + re.escape(t.name) + r'\b', s, re.I):
                        t.ok = False
                        changed.add(t.name.lower())
                # the cascades of the foreign keys (ON DELETE / ON UPDATE CASCADE, SET NULL)
                grew = True
                while grew:
                    grew = False
                    for t in tables.values():
                        if t.name.lower() not in changed and changed & set(getattr(t, 'parents', [])):
                            t.ok = False
                            changed.add(t.name.lower())
                            grew = True
            elif head == 'select':
                if res is None:
                    stats['hidden'] = stats.get('hidden', 0) + 1
                    continue
                stats['selects'] += 1
                p = P(toks)
                q = p.query()
                # locking clauses (TODO 3.11): FOR UPDATE [OF t] [NOWAIT | SKIP LOCKED], FOR SHARE,
                # LOCK IN SHARE MODE: no effect on the rows of a query
                while p.peek()[0] in ('id', 'kw') and p.peek()[1].lower() in ('for', 'lock'):
                    w = [p.peek(k)[1].lower() if p.peek(k)[0] in ('id', 'kw') else '' for k in range(4)]
                    if w[0] == 'for' and w[1] in ('update', 'share'):
                        p.i += 2
                        if p.peek()[0] in ('id', 'kw') and p.peek()[1].lower() == 'of':
                            p.i += 1
                            p.ident()
                            while p.eat_op(','):
                                p.ident()
                        if p.peek()[0] in ('id', 'kw') and p.peek()[1].lower() == 'nowait':
                            p.i += 1
                        elif p.peek()[0] in ('id', 'kw') and p.peek()[1].lower() == 'skip':
                            p.i += 2
                        elif p.peek()[0] in ('id', 'kw') and p.peek()[1].lower() == 'wait':
                            p.i += 2
                    elif w[0] == 'lock' and w[1] == 'in' and w[2] == 'share' and w[3] == 'mode':
                        p.i += 4
                    else:
                        break
                p.eat_op(';')
                if p.peek()[0] != 'eof':
                    raise Skip('trailing')
                qt = QTr(tables)
                qt.top_select = q[1] if q[0] == 'orderq' and not q[2] else q
                qt.limit_any = None
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
                if qt.limit_any is not None:
                    # any [n] rows of the result
                    cases.append('  mk_case_limit %s %d [%s] %s %s %s' % (
                        coq_str('%s:%d' % (base, bi)), qt.limit_any, '; '.join(tabs), cq, exp, sql_txt))
                else:
                    cases.append('  mk_case %s %s [%s] %s %s %s' % (
                        coq_str('%s:%d' % (base, bi)), 'true' if ordered else 'false', '; '.join(tabs), cq, exp, sql_txt))
                stats['translated'] += 1
        except Skip as e:
            if head == 'select':
                if os.environ.get('SQL2COQ_DEBUG'):
                    sys.stderr.write('SKIP %s :: %s\n' % (e, s[:200].replace('\n', ' ')))
                stats['skip'][str(e).split(' ')[0] + ' ' + (str(e).split(' ')[1] if ' ' in str(e) else '')] = stats['skip'].get(str(e).split(' ')[0] + ' ' + (str(e).split(' ')[1] if ' ' in str(e) else ''), 0) + 1
        except (IndexError, KeyError, ValueError, AttributeError, RecursionError) as e:
            if os.environ.get('SQL2COQ_DEBUG'):
                import traceback
                sys.stderr.write('INTERNAL %s :: %s\n%s' % (e, s[:200], traceback.format_exc(limit=4)))
            if head == 'select':
                stats['skip']['internal ' + type(e).__name__] = stats['skip'].get('internal ' + type(e).__name__, 0) + 1
    if cases:
        out.append((base, cases))


HEADER = """Require Import List String ZArith NArith.
Require Import FiniteSet Values TuplesImpl GenericInstance SqlSyntax SqlFull SqlFullSyntax Dialects
        PostgreSQL MySQL SQLite OceanBase MariaDB TiDB Percona PolarDB SpecRunner.
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
        elif args[0] == '--lenient':
            global LENIENT
            LENIENT = True
            args = args[1:]
            continue
        args = args[2:]
    import os
    global ENGINE
    ENGINE = {'PostgreSQL': 'postgresql', 'SQLite': 'sqlite'}.get(dialect, 'mysql')
    global SERVER_VERSION
    SERVER_VERSION = {'MariaDB': 110400, 'TiDB': 80011, 'OceanBaseMySQL': 50725, 'PolarDB': 80018}.get(dialect, 80400)
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
