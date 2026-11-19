#!/usr/bin/env python3
"""Conformance tests from sqllogictest (https://github.com/gregrahn/sqllogictest).

sqllogictest is a set of SQL scripts whose expected results were computed by several
independent engines (SQLite, MySQL, PostgreSQL, Oracle, SQL Server), and which says where the
engines differ (`skipif mysql`, `onlyif sqlite`). The scripts are therefore a specification of
what the dialects have in common, and of how they differ.

The queries which are in the fragment formalised in `SqlFull.v` are translated to Coq, and the
results of the formal semantics of a dialect are compared with the expected ones, with the
conversions which sqllogictest applies (`I`: integer, `R`: `%.3f`, `T`: text, `(empty)` for the
empty string, `NULL`). Results which are only given by their MD5 hash are skipped.

Usage: slt2coq.py --engine ENGINE --dialect DIALECT --outdir DIR [--max N] FILE...
  ENGINE: the name used by the directives (sqlite, mysql, postgresql, oracle)
"""
import os
import re
import sys
import json

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sql2coq as m  # noqa: E402
from sql2coq import Skip, P, tokenize, QTr, Table, parse_create, parse_insert, coq_str, attr  # noqa: E402


def records(path):
    lines = open(path, encoding='utf-8', errors='replace').read().split('\n')
    i = 0
    n = len(lines)
    directives = []
    while i < n:
        l = lines[i].rstrip()
        if l == '' or l.startswith('#'):
            if l == '':
                directives = []
            i += 1
            continue
        w = l.split()
        if w[0] in ('skipif', 'onlyif'):
            directives.append((w[0], w[1]))
            i += 1
            continue
        if w[0] == 'halt':
            yield {'kind': 'halt', 'dir': directives}
            directives = []
            i += 1
            continue
        if w[0] == 'hash-threshold':
            i += 1
            continue
        if w[0] == 'statement':
            ok = len(w) > 1 and w[1] == 'ok'
            i += 1
            sql = []
            while i < n and lines[i].strip() != '':
                sql.append(lines[i])
                i += 1
            yield {'kind': 'statement', 'ok': ok, 'sql': '\n'.join(sql), 'dir': directives}
            directives = []
            continue
        if w[0] == 'query':
            types = w[1] if len(w) > 1 else ''
            sort = w[2] if len(w) > 2 and w[2] in ('nosort', 'rowsort', 'valuesort') else 'nosort'
            i += 1
            sql = []
            while i < n and lines[i].rstrip() != '----' and lines[i].strip() != '':
                sql.append(lines[i])
                i += 1
            res = []
            if i < n and lines[i].rstrip() == '----':
                i += 1
                while i < n and lines[i].strip() != '':
                    res.append(lines[i].rstrip('\n'))
                    i += 1
            yield {'kind': 'query', 'types': types, 'sort': sort, 'sql': '\n'.join(sql), 'res': res, 'dir': directives}
            directives = []
            continue
        i += 1


def applies(directives, engine):
    for kind, e in directives:
        if kind == 'skipif' and e == engine:
            return False
        if kind == 'onlyif' and e != engine:
            return False
    return True


SORT = {'nosort': 0, 'rowsort': 1, 'valuesort': 2}


def process(path, engine, maxq, stats):
    tables = {}
    phases = []  # (tables text, [cases])
    cur_key = None
    cur_cases = []
    nq = 0
    parts = os.path.normpath(path).split(os.sep)
    base = re.sub(r'\W', '_', '_'.join(parts[-2:]).replace('.test', ''))
    for ri, r in enumerate(records(path)):
        if r['kind'] == 'halt':
            if applies(r['dir'], engine) and r['dir']:
                break
            continue
        if not applies(r['dir'], engine):
            continue
        if r['kind'] == 'statement':
            sql = r['sql'].strip()
            if not r['ok']:
                continue
            try:
                mcopy = re.match(r'^insert\s+into\s+(\w+)\s+select\s+\*\s+from\s+(\w+)\s*;?$', sql, re.I)
                if mcopy:
                    dst, src = tables.get(mcopy.group(1).lower()), tables.get(mcopy.group(2).lower())
                    if dst is None or src is None or not src.ok or len(dst.cols) != len(src.cols):
                        raise Skip('copy')
                    dst.rows.extend([list(row) for row in src.rows])
                    continue
                toks = tokenize(sql)
                head = toks[0][1].lower() if toks else ''
                if head == 'create':
                    p = P(toks)
                    p.i = 1
                    if p.kw('index', 'unique'):
                        continue
                    name, cols, limits = parse_create(toks)
                    tables[name.lower()] = Table(name, cols)
                elif head == 'insert':
                    t, rows = parse_insert(toks, tables)
                    t.rows.extend(rows)
                elif head == 'drop':
                    p = P(toks)
                    p.i = 1
                    if p.eat_kw('table'):
                        if p.eat_kw('if'):
                            p.need_kw('exists')
                        tables.pop(p.ident().lower(), None)
                    # views and indexes: nothing to do
                elif head in ('update', 'delete', 'replace', 'alter', 'create', 'insert'):
                    raise Skip('dml')
                else:
                    continue
            except Skip:
                for t in tables.values():
                    if re.search(r'\b' + re.escape(t.name) + r'\b', sql, re.I):
                        t.ok = False
            continue
        # a query
        if maxq and nq >= maxq:
            break
        stats['queries'] += 1
        res = r['res']
        if len(res) == 1 and re.match(r'^\d+ values hashing to [0-9a-f]{32}$', res[0]):
            stats['hashed'] += 1
            continue
        try:
            toks = tokenize(r['sql'].strip())
            p = P(toks)
            q = p.query()
            p.eat_op(';')
            if p.peek()[0] != 'eof':
                raise Skip('trailing')
            qt = QTr(tables)
            cq, ncols, ordered, _ = qt.query(q)
            if ncols != len(r['types']):
                raise Skip('arity')
            if len(res) % max(ncols, 1) != 0:
                raise Skip('result arity')
            tabs = []
            for tn in sorted(qt.used):
                t = tables[tn]
                tabs.append('(%s, [%s], [%s])' % (coq_str(t.name),
                                                  '; '.join(attr(kd, n) for n, kd in t.cols),
                                                  '; '.join('[%s]' % '; '.join(row) for row in t.rows)))
            key = '[%s]' % '; '.join(tabs)
            exp = '[%s]' % '; '.join(coq_str(v) for v in res)
            try:
                sql_txt = coq_str(' '.join(r['sql'].split())[:300])
            except Skip:
                sql_txt = '""'
            case = '    mk_slt_case %s %s %d %s %s %s' % (
                coq_str('%s:%d' % (os.path.basename(path), ri)), coq_str(r['types']), SORT[r['sort']], cq, exp, sql_txt)
        except Skip as e:
            k = str(e).split(' ')[0]
            stats['skip'][k] = stats['skip'].get(k, 0) + 1
            continue
        except (IndexError, KeyError, ValueError, AttributeError) as e:
            stats['skip']['internal ' + type(e).__name__] = stats['skip'].get('internal ' + type(e).__name__, 0) + 1
            continue
        stats['translated'] += 1
        nq += 1
        if key != cur_key:
            if cur_cases:
                phases.append((cur_key, cur_cases))
            cur_key, cur_cases = key, []
        cur_cases.append(case)
    if cur_cases:
        phases.append((cur_key, cur_cases))
    return base, phases


HEADER = """Require Import List String ZArith NArith.
Require Import FiniteSet Values TuplesImpl GenericInstance SqlSyntax SqlFull SqlFullSyntax Dialects
        PostgreSQL MySQL SQLite OceanBase SpecRunner SltRunner.
Import ListNotations.
Open Scope string_scope.
"""


def main():
    args = sys.argv[1:]
    opts = {'--engine': 'sqlite', '--dialect': 'SQLite', '--outdir': None, '--max': '0', '--assert': '0'}
    while args and args[0] in opts:
        opts[args[0]] = args[1]
        args = args[2:]
    stats = {'queries': 0, 'hashed': 0, 'translated': 0, 'skip': {}}
    # FLOAT is a binary32 in MySQL, a binary64 in SQLite and PostgreSQL
    m.FLOAT_BITS = 32 if opts['--engine'] == 'mysql' else 64
    m.REAL_BITS = 32 if opts['--engine'] == 'postgresql' else 64
    outdir = opts['--outdir']
    os.makedirs(outdir, exist_ok=True)
    for path in args:
        base, phases = process(path, opts['--engine'], int(opts['--max']), stats)
        if not phases:
            continue
        body = 'Definition phases_%s : list slt_phase := [\n%s\n].\n' % (
            base, ';\n'.join('  (%s, [\n%s\n  ])' % (k, ';\n'.join(cs)) for k, cs in phases))
        if opts['--assert'] == '1':
            body += 'Example slt_%s_%s : slt_failures %s phases_%s = [].\nProof. vm_compute. reflexivity. Qed.\n' % (opts['--dialect'], base, opts['--dialect'], base)
        else:
            body += 'Eval vm_compute in (slt_diagnose %s phases_%s).\n' % (opts['--dialect'], base)
        with open(os.path.join(outdir, 'Slt_%s.v' % base), 'w') as f:
            f.write(HEADER + body)
    sys.stderr.write(json.dumps(stats, indent=1, sort_keys=True) + '\n')


if __name__ == '__main__':
    main()
