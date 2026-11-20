#!/usr/bin/env python3
"""Differential testing of the model against a live engine (TODO 5.7).

Random tables and queries of the modelled fragment are generated from a grammar (integers with NULLs, short strings;
arithmetic, comparisons, three-valued logic, CASE, BETWEEN, IN, LIKE; WHERE, DISTINCT, GROUP BY with aggregates,
HAVING, inner and left joins, set operations, IN / EXISTS / scalar subqueries), run on the engine, and written with the
engine's rows as a result file; the file is translated by sql2coq.py and checked by the extracted interpreter
(check_terms.py): every case where the model and the engine differ is printed. A query which the engine rejects is
left out (the errors are not compared).

  tools/spec/live_diff.py --engine postgresql --pg-host SOCKET_DIR --lib LIBDIR --n 300 --seed 1 --out DIR
  tools/spec/live_diff.py --engine sqlite --lib LIBDIR --n 300 --seed 1 --out DIR
  tools/spec/live_diff.py --engine mariadb --lib LIBDIR --n 300 --seed 1 --out DIR   (a server on the default socket)
"""
import argparse
import os
import random
import sqlite3
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


class Gen:
    def __init__(self, rnd, engine):
        self.r = rnd
        self.engine = engine

    def int_lit(self):
        return str(self.r.choice([0, 1, 2, 3, -1, 5, 10]))

    def col(self, cols):
        return self.r.choice(cols)

    def iexpr(self, cols, d=0):
        k = self.r.random()
        if d > 2 or k < 0.35:
            return self.col(cols)
        if k < 0.5:
            return self.int_lit()
        if k < 0.6:
            return {'sqlite': 'NULL', 'mariadb': 'CAST(NULL AS SIGNED)'}.get(self.engine, 'CAST(NULL AS INT)')
        if k < 0.85:
            op = self.r.choice(['+', '-', '*'])
            return '(%s %s %s)' % (self.iexpr(cols, d + 1), op, self.iexpr(cols, d + 1))
        if k < 0.92:
            return '(-%s)' % self.iexpr(cols, d + 1)
        return 'CASE WHEN %s THEN %s ELSE %s END' % (self.cond(cols, d + 1), self.iexpr(cols, d + 1),
                                                    self.iexpr(cols, d + 1))

    def cond(self, cols, d=0):
        k = self.r.random()
        if d > 2 or k < 0.45:
            op = self.r.choice(['=', '<', '<=', '<>', '>', '>='])
            return '(%s %s %s)' % (self.iexpr(cols, d + 1), op, self.iexpr(cols, d + 1))
        if k < 0.55:
            return '(%s IS %sNULL)' % (self.iexpr(cols, d + 1), self.r.choice(['', 'NOT ']))
        if k < 0.65:
            return '(%s %sBETWEEN %s AND %s)' % (self.iexpr(cols, d + 1), self.r.choice(['', 'NOT ']),
                                                 self.int_lit(), self.int_lit())
        if k < 0.72:
            return '(%s %sIN (%s))' % (self.iexpr(cols, d + 1), self.r.choice(['', 'NOT ']),
                                       ', '.join(self.int_lit() for _ in range(self.r.randint(1, 3))))
        if k < 0.78:
            return "(c %sLIKE '%s')" % (self.r.choice(['', 'NOT ']), self.r.choice(['a%', '%b', '_', 'ab', '%']))
        if k < 0.88:
            return '(%s %s %s)' % (self.cond(cols, d + 1), self.r.choice(['AND', 'OR']), self.cond(cols, d + 1))
        return '(NOT %s)' % self.cond(cols, d + 1)

    def query(self):
        k = self.r.random()
        t1 = ['a', 'b']
        if k < 0.25:
            items = ', '.join('%s AS x%d' % (self.iexpr(t1), i) for i in range(self.r.randint(1, 3)))
            return 'SELECT %s%s FROM t1 WHERE %s' % (self.r.choice(['', 'DISTINCT ']), items, self.cond(t1))
        if k < 0.45:
            g = self.r.choice(['a', 'b', '(a + b)'])
            agg = self.r.choice(['count(*)', 'count(%s)' % self.iexpr(t1), 'sum(%s)' % self.iexpr(t1),
                                 'min(%s)' % self.iexpr(t1), 'max(%s)' % self.iexpr(t1)])
            having = ' HAVING count(*) %s %s' % (self.r.choice(['>', '>=', '=']), self.r.choice(['1', '2'])) \
                if self.r.random() < 0.4 else ''
            return 'SELECT %s AS g, %s AS v FROM t1 WHERE %s GROUP BY %s%s' % (g, agg, self.cond(t1), g, having)
        if k < 0.55:
            agg = self.r.choice(['count(*)', 'count(DISTINCT %s)' % self.col(t1), 'sum(%s)' % self.iexpr(t1),
                                 'min(%s)' % self.iexpr(t1), 'max(%s)' % self.iexpr(t1)])
            return 'SELECT %s AS v FROM t1 WHERE %s' % (agg, self.cond(t1))
        if k < 0.7:
            jt = self.r.choice(['JOIN', 'LEFT JOIN'])
            cols = ['t1.a', 't1.b', 't2.a', 't2.d']
            return 'SELECT %s AS x, %s AS y FROM t1 %s t2 ON t1.a = t2.a WHERE %s' % (
                self.iexpr(cols), self.iexpr(cols), jt, self.cond(['t1.a', 't1.b', 't2.a']))
        if k < 0.85:
            ops = ['UNION', 'UNION ALL', 'INTERSECT', 'EXCEPT']
            if self.engine == 'postgresql':
                ops += ['INTERSECT ALL', 'EXCEPT ALL']
            return 'SELECT %s AS x FROM t1 WHERE %s %s SELECT %s AS x FROM t2 WHERE %s' % (
                self.iexpr(t1), self.cond(t1), self.r.choice(ops), self.iexpr(['a', 'd']), self.cond(['a', 'd']))
        if k < 0.93:
            q = self.r.choice(['%s IN (SELECT a FROM t2 WHERE d > %s)' % (self.col(t1), self.int_lit()),
                               'EXISTS (SELECT 1 FROM t2 WHERE t2.a = t1.a AND %s)' % self.cond(['d']),
                               'NOT EXISTS (SELECT 1 FROM t2 WHERE t2.a = t1.b)'])
            return 'SELECT a AS x, b AS y FROM t1 WHERE %s' % q
        return 'SELECT a AS x, (SELECT max(d) FROM t2 WHERE t2.a = t1.a) AS y FROM t1'

    def tables(self):
        def v():
            return 'NULL' if self.r.random() < 0.2 else str(self.r.randint(-2, 5))

        def s():
            return 'NULL' if self.r.random() < 0.15 else "'%s'" % self.r.choice(['a', 'ab', 'b', 'ba', 'abc', ''])
        n1, n2 = self.r.randint(3, 9), self.r.randint(2, 7)
        return ['CREATE TABLE t1 (a INT, b INT, c VARCHAR(10));',
                'INSERT INTO t1 VALUES %s;' % ', '.join('(%s, %s, %s)' % (v(), v(), s()) for _ in range(n1)),
                'CREATE TABLE t2 (a INT, d INT);',
                'INSERT INTO t2 VALUES %s;' % ', '.join('(%s, %s)' % (v(), v()) for _ in range(n2))]


def run_pg(host, db, sql):
    r = subprocess.run(['psql', '-h', host, '-U', 'postgres', '-d', db, '-X', '-q', '-A', '-F', '\t', '-P', 'footer=off',
                        '-P', 'null=NULL', '-v', 'ON_ERROR_STOP=1', '-c', sql], capture_output=True, text=True)
    if r.returncode != 0:
        return None
    lines = r.stdout.rstrip('\n').split('\n')
    return len(lines[0].split('\t')), [l.split('\t') for l in lines[1:] if lines[0] != '']


def run_maria(db, sql):
    """the rows of a query on the MariaDB server of the default socket (pymysql: the client prints no header for an
    empty result); the values as the client prints them"""
    import pymysql
    con = pymysql.connect(unix_socket='/run/mysqld/mysqld.sock', user='root', database=db)
    try:
        cur = con.cursor()
        cur.execute(sql)
        return len(cur.description), [['NULL' if v is None else str(v) for v in row] for row in cur.fetchall()]
    except pymysql.MySQLError:
        return None
    finally:
        con.close()


def text_sqlite(v):
    if v is None:
        return 'NULL'
    return str(v)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--engine', choices=['postgresql', 'sqlite', 'mariadb'], required=True)
    ap.add_argument('--pg-host')
    ap.add_argument('--lib', required=True)
    ap.add_argument('--n', type=int, default=200)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--rounds', type=int, default=10, help='databases (each with n / rounds queries)')
    ap.add_argument('--out', required=True)
    a = ap.parse_args()
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    rnd = random.Random(a.seed)
    g = Gen(rnd, a.engine)
    dialect = {'postgresql': 'PostgreSQL', 'sqlite': 'SQLite', 'mariadb': 'MariaDB'}[a.engine]
    files, rejected, total = [], 0, 0
    for rd in range(a.rounds):
        setup = g.tables()
        lines = list(setup)
        if a.engine == 'postgresql':
            db = 'live%d' % rd
            subprocess.run(['psql', '-h', a.pg_host, '-U', 'postgres', '-X', '-q', '-c', 'DROP DATABASE IF EXISTS %s' % db],
                           capture_output=True)
            subprocess.run(['psql', '-h', a.pg_host, '-U', 'postgres', '-X', '-q', '-c', 'CREATE DATABASE %s' % db],
                           capture_output=True, check=True)
            for st in setup:
                if run_pg(a.pg_host, db, st) is None:
                    sys.exit('setup failed: ' + st)
        elif a.engine == 'mariadb':
            db = 'live%d' % rd
            subprocess.run(['mariadb', '-u', 'root', '-e', 'DROP DATABASE IF EXISTS %s; CREATE DATABASE %s' % (db, db)],
                           check=True)
            for st in setup:
                subprocess.run(['mariadb', '-u', 'root', db, '-e', st], check=True)
        else:
            con = sqlite3.connect(':memory:')
            for st in setup:
                con.execute(st)
        for _ in range(a.n // a.rounds):
            q = g.query()
            total += 1
            if a.engine == 'postgresql':
                res = run_pg(a.pg_host, db, q)
            elif a.engine == 'mariadb':
                res = run_maria(db, q)
            else:
                try:
                    cur = con.execute(q)
                    res = (len(cur.description), [[text_sqlite(v) for v in row] for row in cur.fetchall()])
                except sqlite3.Error:
                    res = None
            if res is None:
                rejected += 1
                continue
            n, rows = res
            lines.append(q + ';')
            lines.append('\t'.join('c%d' % i for i in range(n)))
            lines += ['\t'.join(r) for r in rows]
        f = out / ('live_%s_%d.result' % (a.engine, rd))
        f.write_text('\n'.join(lines) + '\n')
        files.append(f)
    print('%d queries generated, %d rejected by the engine' % (total, rejected))
    spec = out / 'spec'
    r = subprocess.run([sys.executable, str(HERE / 'sql2coq.py'), '--dialect', dialect, '--lenient', '--outdir', str(spec)]
                       + [str(f) for f in files], capture_output=True, text=True)
    print(r.stdout[-400:])
    specs = sorted(spec.glob('Spec_*.v'))
    r = subprocess.run([sys.executable, str(ROOT / 'tools' / 'extraction' / 'check_terms.py'), a.lib, dialect]
                       + [str(s) for s in specs], capture_output=True, text=True)
    print(r.stdout)


if __name__ == '__main__':
    main()
