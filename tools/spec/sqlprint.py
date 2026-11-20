#!/usr/bin/env python3
"""The printer of the SQL frontend, and its round-trip test (TODO 7.1).

print_query turns the syntax tree of sql2coq.py's parser back into SQL text (every composite expression is
parenthesised, so the text does not depend on the precedence tables); roundtrip.py-style checking: for every
SELECT of the given result files, parse (s) == parse (print (parse (s))). The kinds of nodes which the printer
does not know are counted, not guessed.

Usage: sqlprint.py --dialect D RESULT_FILES...
"""
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import sql2coq as S  # noqa: E402


class Unsupported(Exception):
    pass


def lit(s):
    return "'" + s.replace('\\', '\\\\').replace("'", "''") + "'"


def ident(n):
    return n if re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', n) and n.lower() not in S.KEYWORDS else '`%s`' % n


def ex(e):
    k = e[0]
    if k == 'col':
        return ident(e[2]) if e[1] is None else '%s.%s' % (ident(e[1]), ident(e[2]))
    if k == 'num':
        return e[1] if not e[1].startswith('-') else '(%s)' % e[1]
    if k == 'str':
        return lit(e[1])
    if k == 'null':
        return 'NULL'
    if k == 'bool':
        return 'TRUE' if e[1] else 'FALSE'
    if k == 'bin':
        op = {'and': 'AND', 'or': 'OR', 'xor': 'XOR', 'div': 'DIV', 'mod': 'MOD'}.get(e[1], e[1])
        return '(%s %s %s)' % (ex(e[2]), op, ex(e[3]))
    if k == 'cmp':
        return '(%s %s %s)' % (ex(e[2]), e[1], ex(e[3]))
    if k == 'not':
        return '(NOT %s)' % ex(e[1])
    if k == 'neg':
        return '(- %s)' % ex(e[1])
    if k == 'is':
        return '(%s IS %s%s)' % (ex(e[3]), 'NOT ' if e[2] else '', e[1].upper())
    if k == 'in':
        # a scalar subquery as an item of the list keeps its own parentheses: IN ((SELECT ...)) is a subquery IN
        items = ', '.join('(%s)' % ex(x) if x[0] == 'subq' else ex(x) for x in e[3])
        return '(%s %sIN (%s))' % (ex(e[2]), 'NOT ' if e[1] else '', items)
    if k == 'insub':
        lhs = ex(e[2][0]) if len(e[2]) == 1 else '(%s)' % ', '.join(ex(x) for x in e[2])
        return '(%s %sIN (%s))' % (lhs, 'NOT ' if e[1] else '', query(e[3]))
    if k == 'between':
        return '(%s %sBETWEEN %s%s AND %s)' % (ex(e[2]), 'NOT ' if e[1] else '', 'SYMMETRIC ' if e[5] else '',
                                                ex(e[3]), ex(e[4]))
    if k == 'like':
        esc = ' ESCAPE %s' % ex(e[4]) if e[4] is not None else ''
        return '(%s %s%s %s%s)' % (ex(e[2]), 'NOT ' if e[1] else '', 'ILIKE' if e[5] else 'LIKE', ex(e[3]), esc)
    if k == 'similar':
        esc = ' ESCAPE %s' % ex(e[4]) if e[4] is not None else ''
        return '(%s %sSIMILAR TO %s%s)' % (ex(e[2]), 'NOT ' if e[1] else '', ex(e[3]), esc)
    if k == 'cmp_array':
        return '(%s %s %s (%s))' % (ex(e[3]), e[1], e[2].upper(), ex(e[4]))
    if k == 'filter':
        return '%s FILTER (WHERE %s)' % (ex(e[1]), ex(e[2]))
    if k == 'regexp':
        return '(%s %sREGEXP %s)' % (ex(e[2]), 'NOT ' if e[1] else '', ex(e[3]))
    if k == 'bitnot':
        return '(~ %s)' % ex(e[1])
    if k == 'case':
        subj, whens, els = e[1], e[2], e[3]
        w = ' '.join('WHEN %s THEN %s' % (ex(c), ex(v)) for c, v in whens)
        return 'CASE %s%s ELSE %s END' % ((ex(subj) + ' ') if subj is not None else '', w, ex(els))
    if k == 'subq':
        return '(%s)' % query(e[1])
    if k == 'exists':
        return '(EXISTS (%s))' % query(e[1])
    if k == 'row':
        return '(%s)' % ', '.join(ex(x) for x in e[1])
    if k == 'call':
        name, args, star = e[1], e[2], e[3]
        distinct = e[4] if len(e) > 4 else False
        within = e[5] if len(e) > 5 else None
        if within is not None:
            return '%s(%s) WITHIN GROUP (ORDER BY %s %s)' % (name, ', '.join(ex(a) for a in args), ex(within[0]),
                                                             'DESC' if within[1] else 'ASC')
        if name == 'array' and S.ENGINE == 'postgresql':
            return 'ARRAY[%s]' % ', '.join(ex(a) for a in args)
        # the special syntaxes of the standard, as the parser reads them
        if name in ('trim_both', 'trim_leading', 'trim_trailing'):
            where = name[5:].upper()
            return 'TRIM(%s %sFROM %s)' % (where, (ex(args[1]) + ' ') if len(args) > 1 else '', ex(args[0]))
        if name == 'extract':
            return 'EXTRACT(%s FROM %s)' % (args[0][1], ex(args[1]))
        if name == 'position':
            return 'POSITION(%s IN %s)' % (ex(args[0]), ex(args[1]))
        if name == 'substring_regex':
            return 'SUBSTRING(%s FROM %s)' % (ex(args[0]), ex(args[1]))
        if name == 'interval_index':
            return 'INTERVAL(%s)' % ', '.join(ex(a) for a in args)
        if star:
            return '%s(*)' % name
        return '%s(%s%s)' % (name, 'DISTINCT ' if distinct else '', ', '.join(ex(a) for a in args))
    if k == 'cast':
        return 'CAST(%s AS %s)' % (ex(e[2]), e[1].upper())
    if k == 'cast_dec':
        return 'CAST(%s AS DECIMAL(%d, %d))' % (ex(e[3]), e[1], e[2])
    if k == 'quant':
        lhs = ex(e[3][0]) if len(e[3]) == 1 else '(%s)' % ', '.join(ex(x) for x in e[3])
        return '(%s %s %s (%s))' % (lhs, e[1], e[2].upper(), query(e[4]))
    if k == 'wcall':
        call, spec, ign = e[1], e[2], e[3]
        txt = ex(call) + (' IGNORE NULLS' if ign else '')
        return '%s OVER %s' % (txt, window_spec(spec))
    if k == 'temporal':
        return '%s %s' % (e[1].upper(), lit(e[2]))
    if k == 'interval':
        return 'INTERVAL %s %s' % (ex(e[1]), e[2])
    raise Unsupported(k)


def window_spec(spec):
    _, base, part, order, frame = spec
    if base is not None and not part and not order and frame is None:
        return ident(base)
    out = []
    if base is not None:
        out.append(ident(base))
    if part:
        out.append('PARTITION BY ' + ', '.join(ex(x) for x in part))
    if order:
        out.append('ORDER BY ' + ', '.join('%s %s%s' % (ex(x), d.upper(), ' NULLS %s' % n.upper() if n else '')
                                           for x, d, n in order))
    if frame is not None:
        mode, lo, hi, excl = frame

        def b(x):
            return {'up': 'UNBOUNDED PRECEDING', 'uf': 'UNBOUNDED FOLLOWING', 'cr': 'CURRENT ROW'}.get(x[0]) or \
                '%d %s' % (x[1], 'PRECEDING' if x[0] == 'p' else 'FOLLOWING')
        ft = '%s BETWEEN %s AND %s' % (mode.upper(), b(lo), b(hi))
        if excl:
            ft += ' EXCLUDE ' + {'Excl_Current_Row': 'CURRENT ROW', 'Excl_Group': 'GROUP', 'Excl_Ties': 'TIES',
                                 'Excl_No_Others': 'NO OTHERS'}[excl]
        out.append(ft)
    return '(%s)' % ' '.join(out)


def frm(f):
    k = f[0]
    if k == 'table':
        return ident(f[1]) + ('' if f[2] == f[1] else ' AS %s' % ident(f[2]))
    if k == 'derived':
        cols = '(%s)' % ', '.join(ident(c) for c in f[3]) if f[3] else ''
        return '(%s) AS %s%s' % (query(f[1]), ident(f[2]), cols)
    if k == 'tfun':
        name, args, ord_, alias, cols = f[1], f[2], f[3], f[4], f[5]
        if name == 'json_table':
            # the parser keeps the column names and paths, not the types (any type reads back the same)
            colspec = ', '.join('%s JSON PATH %s' % (ident(c), ex(pth)) for c, pth in zip(cols, args[2:]))
            return 'JSON_TABLE(%s, %s COLUMNS (%s)) AS %s' % (ex(args[0]), ex(args[1]), colspec, ident(alias))
        txt = '%s(%s)%s' % (name, ', '.join(ex(a) for a in args), ' WITH ORDINALITY' if ord_ else '')
        txt += ' AS %s' % ident(alias)
        if cols is not None:
            txt += '(%s)' % ', '.join(ident(c) for c in cols)
        return txt
    if k == 'join':
        jt, l, r, c = f[1], f[2], f[3], f[4]
        using = f[5] if len(f) > 5 else None
        if isinstance(using, str):
            # NATURAL JOIN (the parser keeps the marker in the place of the USING list)
            return '(%s NATURAL %s %s)' % (frm(l), {'inner': 'JOIN', 'left': 'LEFT JOIN', 'right': 'RIGHT JOIN',
                                                    'full': 'FULL JOIN', 'cross': 'JOIN'}[jt], frm(r))
        if using:
            return '(%s %s %s USING (%s))' % (frm(l), {'inner': 'JOIN', 'left': 'LEFT JOIN', 'right': 'RIGHT JOIN',
                                                         'full': 'FULL JOIN', 'cross': 'JOIN'}[jt], frm(r),
                                              ', '.join(ident(x) for x in using))
        word = {'cross': 'CROSS JOIN', 'inner': 'JOIN', 'left': 'LEFT JOIN', 'right': 'RIGHT JOIN',
                'full': 'FULL JOIN'}.get(jt)
        if word is None:
            raise Unsupported('join ' + str(jt))
        return '(%s %s %s%s)' % (frm(l), word, frm(r), (' ON %s' % ex(c)) if c is not None else '')
    raise Unsupported('from ' + k)


def select(s):
    _, distinct, items, f, where, group, having = s
    out = []
    for it in items:
        if it[0] == 'star':
            out.append('*' if it[1] is None else '%s.*' % ident(it[1]))
        else:
            out.append(ex(it[1]) + (' AS %s' % ident(it[2]) if it[2] else ''))
    txt = 'SELECT %s%s' % ('DISTINCT ' if distinct else '', ', '.join(out))
    if f:
        txt += ' FROM ' + frm(f)
    if where is not None:
        txt += ' WHERE ' + ex(where)
    if group is not None:
        if isinstance(group, tuple):
            txt += ' GROUP BY GROUPING SETS (%s)' % ', '.join('(%s)' % ', '.join(ex(x) for x in st) for st in group[1])
        else:
            txt += ' GROUP BY ' + ', '.join(ex(x) for x in group)
    if having is not None:
        txt += ' HAVING ' + ex(having)
    return txt


def query(q):
    k = q[0]
    if k == 'select':
        return select(q)
    if k == 'setop':
        # a SELECT operand needs no parentheses (and the parser of a scalar subquery reads [(SELECT ((SELECT ...)
        # UNION ...))] as an expression): only the nested set operations and the ordered operands get them
        def operand(x):
            return query(x) if x[0] in ('select', 'values') else '(%s)' % query(x)
        return '%s %s%s %s' % (operand(q[3]), q[1].upper(), ' ALL' if q[2] else '', operand(q[4]))
    if k == 'orderq':
        inner, order, limit = q[1], q[2], q[3]
        # the ORDER BY of a set operation follows its last operand: the parser attaches it to the whole
        # operation (an ordered operand is parenthesised by operand above)
        if inner[0] in ('select', 'setop'):
            txt = query(inner)
        else:
            txt = '(%s)' % query(inner)
        if order:
            txt += ' ORDER BY ' + ', '.join('%s %s' % (ex(e), d.upper()) for e, d in order)
        if limit is not None:
            off, n = limit
            if n is None:
                raise Unsupported('offset without limit')
            txt += ' LIMIT %d%s' % (n, ' OFFSET %d' % off if off else '')
        return txt
    if k == 'values':
        return 'VALUES ' + ', '.join('(%s)' % ', '.join(ex(x) for x in row) for row in q[1])
    raise Unsupported('query ' + k)


def norm(x):
    """the syntax trees up to the forms of the same call ([('call', f, args, star, distinct)] with or without
    a trailing None)"""
    if isinstance(x, list):
        return [norm(y) for y in x]
    if isinstance(x, tuple):
        if x and x[0] == 'call' and len(x) == 6 and x[5] is None:
            x = x[:5]
        if x and x[0] == 'join' and len(x) == 6 and x[5] is None:
            x = x[:5]
        return tuple(norm(y) for y in x)
    return x


def parse(sql):
    p = S.P(S.tokenize(sql))
    q = p.query()
    return q


def main():
    args = sys.argv[1:]
    dialect = 'MySQL'
    if args[:1] == ['--dialect']:
        dialect, args = args[1], args[2:]
    S.ENGINE = {'PostgreSQL': 'postgresql', 'SQLite': 'sqlite'}.get(dialect, 'mysql')
    stats = {'selects': 0, 'parsed': 0, 'printed': 0, 'roundtrip': 0, 'mismatch': 0}
    unsup = {}
    bad = []
    for path in args:
        lines = open(path, encoding='utf-8', errors='replace').read().split('\n')
        for stmt, _ in S.split_blocks(lines):
            s = stmt.strip()
            if not re.match(r'^\s*select\b', s, re.I) or len(s) > 5000:
                continue
            stats['selects'] += 1
            try:
                q = parse(s)
            except Exception:
                continue
            stats['parsed'] += 1
            try:
                txt = print_query(q)
            except Unsupported as e:
                unsup[str(e)] = unsup.get(str(e), 0) + 1
                continue
            except (IndexError, TypeError, ValueError, AttributeError) as e:
                unsup['printer error ' + type(e).__name__] = unsup.get('printer error ' + type(e).__name__, 0) + 1
                continue
            stats['printed'] += 1
            try:
                q2 = parse(txt + ';')
            except Exception as e:
                stats['mismatch'] += 1
                bad.append((s, txt, 'reparse: %s' % e))
                continue
            if norm(q) == norm(q2):
                stats['roundtrip'] += 1
            else:
                stats['mismatch'] += 1
                bad.append((s, txt, 'different tree'))
    print(stats)
    print('not printed:', sorted(unsup.items(), key=lambda x: -x[1])[:12])
    for s, t, why in bad[:8]:
        print('---', why, '\n  ', s[:200], '\n  ', t[:200])
    sys.exit(1 if stats['mismatch'] else 0)


def print_query(q):
    return query(q)


if __name__ == '__main__':
    main()
