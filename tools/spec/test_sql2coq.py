#!/usr/bin/env python3
"""Regression tests of the translator of the conformance harness (sql2coq.py).

Each test writes small result files in the format of the suites (the statement, then the header and the rows
separated by tabs, or an error line), translates them, and looks at the generated cases. The tests are the
problems which the audits found in the translator (docs/TODO.md, Phase 8).

Usage: test_sql2coq.py     (exit status 1 if a test fails)
"""
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
TOOL = os.path.join(HERE, 'sql2coq.py')


def translate(dialect, files):
    """files: {name: text}. Returns {name: text of the generated Spec_name.v}."""
    with tempfile.TemporaryDirectory() as d:
        paths = []
        for name, text in files.items():
            p = os.path.join(d, name + '.result')
            with open(p, 'w') as f:
                f.write(text)
            paths.append(p)
        out = os.path.join(d, 'out')
        subprocess.run([sys.executable, TOOL, '--dialect', dialect, '--lenient', '--outdir', out] + sorted(paths),
                       check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        res = {}
        for name in files:
            p = os.path.join(out, 'Spec_%s.v' % name)
            res[name] = open(p).read() if os.path.exists(p) else ''
        return res


def case(text, ident):
    m = re.search(r'mk_case\w* "%s".*' % re.escape(ident), text)
    return m.group(0) if m else ''


TESTS = []


def test(f):
    TESTS.append(f)
    return f


@test
def insert_ignore_not_null():
    """TODO 8.14: a NOT NULL column which INSERT IGNORE does not give takes the implicit default of its type."""
    out = translate('OceanBaseMySQL', {'a': (
        "CREATE TABLE t (c1 bigint NOT NULL, c2 varchar(50) NOT NULL, c3 int NOT NULL);\n"
        "INSERT IGNORE INTO t (c1) value (1);\n"
        "SELECT * FROM t;\n"
        "c1\tc2\tc3\n"
        "1\t\t0\n")})['a']
    c = case(out, 'a:2')
    assert '[[VZ (1); VS ""; VZ (0)]]' in c, c


@test
def insert_not_null_without_ignore():
    """TODO 8.14: without IGNORE the statement is an error of the strict mode: the table is not read."""
    out = translate('OceanBaseMySQL', {'a': (
        "CREATE TABLE t (c1 bigint NOT NULL, c2 varchar(50) NOT NULL);\n"
        "INSERT INTO t (c1) value (1);\n"
        "SELECT * FROM t;\n"
        "c1\tc2\n"
        "1\t\n")})['a']
    assert case(out, 'a:2') == '', out


@test
def options_of_an_earlier_table():
    """TODO 8.14: the AUTO_INCREMENT and NOT NULL columns of a table are forgotten when another script creates a
    table of the same name."""
    first = ("CREATE TABLE t (a int NOT NULL AUTO_INCREMENT, b int NOT NULL, PRIMARY KEY (a));\n"
             "SELECT 1;\n1\n1\n")
    second = ("CREATE TABLE t (a int, b int);\n"
              "INSERT INTO t (b) values (5);\n"
              "SELECT b FROM t;\n"
              "b\n"
              "5\n")
    out = translate('OceanBaseMySQL', {'a': first, 'b': second})['b']
    c = case(out, 'b:2')
    assert '[[NullZ; VZ (5)]]' in c, out


@test
def error_line_is_not_an_empty_result():
    """TODO 8.17: an error line under a query of one column is a case which expects an error."""
    out = translate('TiDB', {'a': (
        "select json_quote();\n"
        "Error 1582 (42000): Incorrect parameter count in the call to native function 'json_quote'\n"
        "select 1 from dual where 1 = 0;\n"
        "1\n")})['a']
    assert case(out, 'a:0').startswith('mk_case_error "a:0"'), out
    # a header alone is an empty result
    assert re.match(r'mk_case "a:1" false \[\] .* \[\] "', case(out, 'a:1')), out


@test
def error_cases_only_in_the_mysql_family():
    out = translate('PostgreSQL', {'a': "select 1/0;\nERROR:  division by zero\n"})['a']
    assert 'mk_case_error' not in out, out


@test
def dayname_as_a_number():
    """TODO 8.19: DAYNAME (d) in an arithmetic operator, or compared with a number, is WEEKDAY (d)."""
    out = translate('TiDB', {'a': (
        'select dayname("1962-03-01")+0;\ndayname("1962-03-01")+0\n3\n'
        'select dayname("1962-03-01")=3;\ndayname("1962-03-01")=3\n1\n'
        'select dayname("1962-03-01");\ndayname("1962-03-01")\nThursday\n')})['a']
    assert '(fn "weekday" [(str "1962-03-01")])' in case(out, 'a:0'), out
    assert '(fn "weekday" [(str "1962-03-01")])' in case(out, 'a:1'), out
    assert '(fn "dayname" [(str "1962-03-01")])' in case(out, 'a:2'), out


@test
def typed_literals_of_the_mysql_family():
    """TODO 8.20: TIMESTAMP '...' and TIME '...' are literals, stricter than the casts."""
    out = translate('TiDB', {'a': (
        "select timestamp '2017@01@01 00~00~00';\ntimestamp '2017@01@01 00~00~00'\n2017-01-01 00:00:00\n"
        "select time '1 01:00:00';\ntime '1 01:00:00'\n25:00:00\n")})['a']
    assert '(fn "lit_datetime" [(str "2017@01@01 00~00~00")])' in case(out, 'a:0'), out
    assert '(fn "lit_time" [(str "1 01:00:00")])' in case(out, 'a:1'), out
    out = translate('PostgreSQL', {'a': "select timestamp '2017-01-01 00:00:00';\ntimestamp\n2017-01-01 00:00:00\n"})['a']
    assert '(fn "cast_timestamp"' in case(out, 'a:0'), out


@test
def and_of_postgresql_is_a_condition():
    """TODO 8.9: AND and OR of PostgreSQL are conditions (booleans); functions on numbers in the MySQL family."""
    out = translate('PostgreSQL', {'a': "select true and false;\n?column?\nf\n"})['a']
    assert '(e_cond (c_and c_true (c_not c_true)))' in case(out, 'a:0'), out
    out = translate('TiDB', {'a': "select 1 and 0;\n1 and 0\n0\n"})['a']
    assert '(fn "and" [(int (1)); (int (0))])' in case(out, 'a:0'), out


@test
def conditions_of_a_block_with_grouping_sets():
    """TODO 8.9: in a block with grouping sets a condition is the truth of an expression, in the SELECT list, in
    GROUP BY and in HAVING, so that a grouped condition is hidden where it is not grouped."""
    out = translate('PostgreSQL', {'a': (
        "select not a from (values(true)) t(a) group by rollup(not a) having not not a;\n?column?\nf\n")})['a']
    c = case(out, 'a:0')
    grouped = '(e_cond (c_not (c_expr (col (Attr_Z "t.a")))))'
    assert '(g_sets [[%s]; []])' % grouped in c, c
    assert '(as_ %s (Attr_Z "c0"))' % grouped in c, c
    assert '(c_expr (e_cond (c_not (c_expr %s))))' % grouped in c, c
    # without grouping sets the conditions are written as they are
    out = translate('PostgreSQL', {'a': "select 1 from (values(true)) t(a) where not a;\n?column?\n"})['a']
    assert 'c_expr (e_cond' not in case(out, 'a:0'), out


@test
def result_files_of_the_same_name():
    """TODO 8.26: two result files of the same name in different directories give two files of cases."""
    with tempfile.TemporaryDirectory() as d:
        paths = []
        for sub, n in (('executor', 1), ('planner', 2)):
            os.makedirs(os.path.join(d, sub))
            p = os.path.join(d, sub, 'integration.result')
            with open(p, 'w') as f:
                f.write("select %d;\n%d\n%d\n" % (n, n, n))
            paths.append(p)
        out = os.path.join(d, 'out')
        subprocess.run([sys.executable, TOOL, '--dialect', 'TiDB', '--lenient', '--outdir', out] + paths,
                       check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        assert sorted(os.listdir(out)) == ['Spec_executor_integration.v', 'Spec_planner_integration.v'], os.listdir(out)
        assert 'mk_case "executor_integration:0"' in open(os.path.join(out, 'Spec_executor_integration.v')).read()


def main():
    failed = 0
    for t in TESTS:
        try:
            t()
            print('ok    %s' % t.__name__)
        except AssertionError as e:
            failed += 1
            print('FAIL  %s: %s' % (t.__name__, str(e)[:400]))
    print('%d tests, %d failed' % (len(TESTS), failed))
    sys.exit(1 if failed else 0)


if __name__ == '__main__':
    main()
