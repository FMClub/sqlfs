#!/usr/bin/env python3
"""Translate a term of tools/spec/sql2coq.py (Coq syntax: applications, lists, pairs, strings, numerals) to an
OCaml expression over the extracted library of build_lib.sh (TODO 6.6).

The extracted constructors take their arguments as a tuple, the definitions curried; extraction renames the
definitions which clash with OCaml or with other names (NAMES); a numeral takes the type of the argument
position where it stands (KINDS), Z by default, or the one of its scope suffix (%Z, %nat, %N).
"""
import re

NAMES = {'int': 'int0', 'pred': 'pred0', 'join': 'join0', 'VZ': 'vZ', 'VS': 'vS', 'VD': 'vD', 'VFl': 'vFl',
         'NullZ': 'nullZ', 'NullS': 'nullS', 'NullQ': 'nullQ', 'NullValues.VDate': 'Prelude.vdate',
         'NullValues.VTs': 'Prelude.vts', 'NullValues.VTime': 'Prelude.vtime',
         'QArith_base.Qmake': 'Prelude.qmake'}
KINDS = {'VD': ['Z', 'nat'], 'VFl': [None, 'Z', 'Z'], 'NullValues.VDate': ['Z'], 'NullValues.VTs': ['Z', 'int'],
         'NullValues.VTime': ['Z', 'int'], 'Preceding': ['nat'], 'Following': ['nat'],
         'QArith_base.Qmake': ['Z', 'positive'], 'w_nth_value': [None, 'nat', None], 'w_ntile': ['nat'],
         'w_lead': [None, 'nat', None], 'w_lag': [None, 'nat', None], 'mk_case_limit': [None, 'nat']}
SCOPES = {'Z': 'Z', 'nat': 'nat', 'N': 'N', 'positive': 'positive'}

TOKEN = re.compile(r'\s*(?:(?P<str>"(?:[^"]|"")*")|(?P<num>-?\d+)|(?P<id>[A-Za-z_][A-Za-z_0-9\'.]*)|(?P<op>[()\[\];,%]))')


def tokenize(s):
    out, i = [], 0
    while True:
        m = TOKEN.match(s, i)
        if not m:
            if s[i:].strip():
                raise ValueError('unexpected text: ' + s[i:i + 40])
            return out
        i = m.end()
        kind = m.lastgroup
        out.append((kind, m.group(kind)))


class Parser:
    def __init__(self, toks):
        self.t, self.i = toks, 0

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else ('eof', '')

    def take(self, v=None):
        tk = self.peek()
        if v is not None and tk[1] != v:
            raise ValueError('expected %s, found %s' % (v, tk[1]))
        self.i += 1
        return tk

    def scope(self, node):
        if self.peek() == ('op', '%'):
            self.i += 1
            return ('scoped', node, self.take()[1])
        return node

    def atom(self):
        k, v = self.peek()
        if k == 'str':
            self.i += 1
            return ('str', v[1:-1].replace('""', '"'))
        if k == 'num':
            self.i += 1
            return self.scope(('num', v))
        if k == 'id':
            self.i += 1
            return ('id', v)
        if v == '(':
            self.i += 1
            items = [self.term()]
            while self.peek() == ('op', ','):
                self.i += 1
                items.append(self.term())
            self.take(')')
            return self.scope(items[0] if len(items) == 1 else ('tuple', items))
        if v == '[':
            self.i += 1
            items = []
            if self.peek() != ('op', ']'):
                items.append(self.term())
                while self.peek() == ('op', ';'):
                    self.i += 1
                    if self.peek() == ('op', ']'):
                        break
                    items.append(self.term())
            self.take(']')
            return ('list', items)
        return None

    def term(self):
        head = self.atom()
        if head is None:
            raise ValueError('unexpected token %s' % (self.peek(),))
        args = []
        while True:
            save = self.i
            a = self.atom() if self.peek()[0] != 'eof' and self.peek()[1] not in (')', ']', ';', ',', '%') else None
            if a is None:
                self.i = save
                break
            args.append(a)
        return ('app', head, args) if args else head


def ml_string(s):
    out = []
    for b in s.encode('utf-8'):
        c = chr(b)
        if c == '"' or c == '\\':
            out.append('\\' + c)
        elif 32 <= b < 127:
            out.append(c)
        else:
            out.append('\\x%02x' % b)
    return '"' + ''.join(out) + '"'


def numeral(v, kind):
    kind = kind or 'Z'
    if kind == 'int':
        return '(%d)' % int(v)
    if kind == 'nat':
        return '(Prelude.nat %d)' % int(v)
    if kind == 'N':
        return '(Prelude.n "%s")' % v
    if kind == 'positive':
        return '(Prelude.pos "%s")' % v
    return '(Prelude.z "%s")' % v


def is_constructor(name):
    last = name.split('.')[-1]
    return name not in NAMES and last[:1].isupper()


def emit(node, kind=None):
    k = node[0]
    if k == 'str':
        return ml_string(node[1])
    if k == 'num':
        return numeral(node[1], kind)
    if k == 'scoped':
        return emit(node[1], SCOPES.get(node[2], kind))
    if k == 'id':
        return NAMES.get(node[1], node[1])
    if k == 'tuple':
        # (a, b, c) is ((a, b), c) in Coq
        out = emit(node[1][0], kind)
        for x in node[1][1:]:
            out = '(%s, %s)' % (out, emit(x, kind))
        return out
    if k == 'list':
        return '[%s]' % '; '.join(emit(x, kind) for x in node[1])
    if k == 'app':
        head, args = node[1], node[2]
        if head[0] != 'id':
            raise ValueError('application of a non-name')
        name = head[1]
        if name == 'Some':
            return '(Some %s)' % emit(args[0], kind)
        kinds = KINDS.get(name, [])
        out = [emit(a, kinds[i] if i < len(kinds) else None) for i, a in enumerate(args)]
        if name in ('mk_case', 'mk_case_limit') and len(out) > 2:
            # the attributes of the tables are those of the module type of tuples, abstract in OCaml
            out[2] = '(Obj.magic %s)' % out[2]
        if is_constructor(name):
            return '(%s (%s))' % (name, ', '.join(out))
        return '(%s %s)' % (NAMES.get(name, name), ' '.join(out))
    raise ValueError(k)


def to_ml(term):
    p = Parser(tokenize(term))
    t = p.term()
    if p.peek()[0] != 'eof':
        raise ValueError('trailing text')
    return emit(t)
