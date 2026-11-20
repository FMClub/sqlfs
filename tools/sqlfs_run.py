#!/usr/bin/env python3
"""Run a SQL query of a dialect on CSV tables with the formal semantics (TODO 6.6).

  tools/sqlfs_run.py --dialect MySQL --table t=data/t.csv [--table u=u.csv ...] "SELECT ..."

Each CSV file has a header line (the column names); a column whose values are all integers is an INT column, a
column of numbers a DECIMAL column (the largest scale), otherwise a VARCHAR column; an empty cell is NULL. The
tables and the query are translated by tools/spec/sql2coq.py, evaluated by Coq ([vm_compute] of the semantics of
src/data/sql/SqlFull.v with the dialect of src/data/dialects/), and the rows are printed as the client of the
dialect prints them ([ResultText.result_text]). Needs the compiled library in src/.
"""
import csv
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools' / 'spec'))
import sql2coq as S  # noqa: E402
sys.path.insert(0, str(ROOT / 'tools' / 'extraction'))
import term2ml  # noqa: E402


def col_type(vals):
    vs = [v for v in vals if v != '']
    if vs and all(re.fullmatch(r'-?\d+', v) for v in vs):
        return 'INT'
    if vs and all(re.fullmatch(r'-?\d+(\.\d+)?', v) for v in vs):
        sc = max((len(v.split('.')[1]) if '.' in v else 0) for v in vs)
        ip = max(len(v.split('.')[0].lstrip('-')) for v in vs)
        return 'DECIMAL(%d, %d)' % (ip + sc, sc)
    return 'VARCHAR(255)'


def lit(v, ty):
    if v == '':
        return 'NULL'
    if ty == 'VARCHAR(255)':
        return "'" + v.replace("'", "''") + "'"
    return v


def main():
    args = sys.argv[1:]
    dialect, tables, lib = 'MySQL', [], None
    while args and args[0].startswith('--'):
        if args[0] == '--dialect':
            dialect, args = args[1], args[2:]
        elif args[0] == '--table':
            name, path = args[1].split('=', 1)
            tables.append((name, path))
            args = args[2:]
        elif args[0] == '--extracted':
            lib, args = os.path.abspath(args[1]), args[2:]
        else:
            sys.exit('unknown option ' + args[0])
    if len(args) != 1:
        sys.exit(__doc__)
    query = args[0].strip().rstrip(';') + ';'
    lines, cols_of = [], {}
    for name, path in tables:
        rows = list(csv.reader(open(path, newline='', encoding='utf-8')))
        header, data = rows[0], rows[1:]
        tys = [col_type([r[i] for r in data]) for i in range(len(header))]
        cols_of[name.lower()] = header
        lines.append('CREATE TABLE %s (%s);' % (name, ', '.join('%s %s' % (c, t) for c, t in zip(header, tys))))
        if data:
            lines.append('INSERT INTO %s VALUES %s;' % (name, ', '.join(
                '(' + ', '.join(lit(v, t) for v, t in zip(r, tys)) + ')' for r in data)))
    # the number of columns of the result: the select items, a star being the columns of the tables
    S.ENGINE = {'PostgreSQL': 'postgresql', 'SQLite': 'sqlite'}.get(dialect, 'mysql')
    q = S.P(S.tokenize(query)).query()
    while q[0] in ('orderq', 'setop'):
        q = q[1] if q[0] == 'orderq' else q[3]
    n = 0
    for it in q[2]:
        if it[0] == 'star':
            n += sum(len(c) for t, c in cols_of.items() if re.search(r'\b%s\b' % re.escape(t), query, re.I)) \
                if it[1] is None else len(cols_of.get(it[1].lower(), []))
        else:
            n += 1
    n = max(n, 1)
    lines.append(query)
    lines.append('\t'.join('c%d' % i for i in range(n)))
    lines.append('\t'.join('x' for _ in range(n)))  # a placeholder row: only the actual rows are printed
    with tempfile.TemporaryDirectory() as d:
        res = Path(d) / 'q.result'
        res.write_text('\n'.join(lines) + '\n')
        out = Path(d) / 'out'
        subprocess.run([sys.executable, str(ROOT / 'tools/spec/sql2coq.py'), '--dialect', dialect, '--lenient',
                        '--outdir', str(out), str(res)], capture_output=True, text=True)
        files = list(out.glob('Spec_*.v')) if out.exists() else []
        if not files:
            sys.exit('the query is not in the fragment of the translator')
        spec = files[0]
        t = spec.read_text()
        name = re.search(r'Definition (cases_\w+)', t).group(1)
        if lib is not None:
            run_extracted(lib, dialect, n, t, Path(d))
            return
        t = t.replace('Eval vm_compute in (diagnose', '(* Eval vm_compute in (diagnose')
        t = t.rstrip() + ' *)\nRequire Import ResultText.\n' + \
            'Eval vm_compute in (map (fun c => map (map (result_text %s)) (run_rows %s c %d)) %s).\n' % (
                dialect, dialect, n, name)
        spec.write_text(t)
        r = subprocess.run(['coqc', '-R', '.', 'SQLFS', str(spec)], cwd=ROOT / 'src', capture_output=True, text=True)
        rows = re.findall(r'\[((?:"[^"]*"(?:;\s*)?)+)\]', r.stdout.replace('\n', ' '))
        if r.returncode != 0:
            sys.exit(r.stdout + r.stderr)
        for row in rows:
            print('\t'.join(re.findall(r'"([^"]*)"', row)))


def run_extracted(lib, dialect, n, spec_text, d):
    """the cases of the translated file, as an OCaml program linked with the extracted library"""
    m = re.search(r':= \[\n(.*)\n\]\.', spec_text, re.S)
    cases = [c.strip().rstrip(';') for c in m.group(1).split('\n') if c.strip()]
    body = '; '.join(term2ml.to_ml(c) for c in cases)
    ml = d / 'query.ml'
    ml.write_text('open Sqlfs_lib\nlet () =\n  match dialect_named %s with\n'
                  '  | None -> prerr_endline "unknown dialect"; exit 2\n'
                  '  | Some dl -> List.iter (fun c -> Prelude.print_rows dl (run_rows dl c (Prelude.nat %d))) [%s]\n'
                  % (term2ml.ml_string(dialect), n, body))
    exe = d / 'query'
    r = subprocess.run(['ocamlopt', '-I', lib, os.path.join(lib, 'sqlfs_lib.cmx'), os.path.join(lib, 'prelude.cmx'),
                        str(ml), '-o', str(exe)], capture_output=True, text=True, cwd=str(d))
    if r.returncode != 0:
        sys.exit(r.stdout + r.stderr)
    r = subprocess.run(['sh', '-c', 'ulimit -s unlimited; exec "$0"', str(exe)], capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(r.stdout + r.stderr)
    sys.stdout.write(r.stdout)


if __name__ == '__main__':
    main()
