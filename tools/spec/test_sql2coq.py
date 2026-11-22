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
def backslash_in_a_string():
    """Iteration 18: a backslash is an escape in the strings of the MySQL family and in E'...' of PostgreSQL, and
    a character in the other strings of PostgreSQL."""
    out = translate('PostgreSQL', {'a': "select 'a' ~ '(a)\\1';\n?column?\nf\n",
                                   'b': "select E'x\\'y';\n?column?\nx'y\n"})
    assert '(str "(a)\\1")' in case(out['a'], 'a:0'), out['a']
    assert '(str "x\'y")' in case(out['b'], 'b:0'), out['b']
    out = translate('TiDB', {'a': "select 'a\\\\1';\na\\1\na\\1\n"})['a']
    assert '(str "a\\1")' in case(out, 'a:0'), out


@test
def window_in_an_aggregate():
    """TODO 8.25: a window function in the argument of an aggregate cannot be written in SqlFull: no case."""
    out = translate('MariaDB', {'a': (
        "create table t1 (i int);\ninsert into t1 values (1),(2);\n"
        "select SUM( SUM(i) OVER () ) from t1;\n"
        "ERROR HY000: Window function is not allowed in window specification or aggregate\n"
        "select SUM(i) OVER () from t1;\nSUM(i) OVER ()\n3\n3\n")})['a']
    assert case(out, 'a:2') == '', out
    assert case(out, 'a:3') != '', out


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


@test
def padding_of_a_psql_table():
    """Iteration 20: the spaces at the start of a cell are data in a column aligned on the left (texts) and
    padding in a column aligned on the right (numbers)."""
    sys.path.insert(0, HERE)
    import pg2result
    conv = pg2result.convert_output
    # a text wider than its header, alone: no padding at all
    assert conv([' to_char ', '----------', '  1.2e+03', '(1 row)']) == ['to_char', ' 1.2e+03']
    # a number under a wider header: its padding is kept (SpecRunner ignores the leading spaces of a number)
    assert conv([' ?column? ', '----------', '       37', '(1 row)']) == ['?column?', '      37']
    # texts of different lengths, then numbers
    out = conv([' t      | n  ', '--------+----', '  .00   |  5', ' - 4.20 | 10', '(2 rows)'])
    assert out == ['t\tn', ' .00\t 5', '- 4.20\t10'], out
    # texts which all fill their column (to_char (x, '9.999EEEE')): the leading spaces are data
    out = conv([' numeric    ', '------------', '  0.000e+00', ' -4.200e+00', '(2 rows)'])
    assert out == ['numeric', ' 0.000e+00', '-4.200e+00'], out
    # one row, wider than its header: the value fills the column, its spaces at the end are kept
    assert conv(['  json  ', '--------', '  true  ', '(1 row)']) == ['json', ' true '], conv(['  json  ', '--------', '  true  ', '(1 row)'])
    # one row under a wider header: the padding is dropped
    assert conv([' ?column? ', '----------', ' t        ', '(1 row)']) == ['?column?', 't']
    # a text under a wider header
    assert conv([' to_char ', '---------', '  485', '(1 row)']) == ['to_char', ' 485']


@test
def string_literals_of_values():
    """Iteration 21: in a column of VALUES whose other entries are casts to one type, a string literal of
    PostgreSQL is of this type."""
    out = translate('PostgreSQL', {'a': (
        "WITH v(x) AS (VALUES('0'::numeric),('4.2')) SELECT x FROM v;\nx\n0\n4.2\n")})['a']
    c = case(out, 'a:0')
    assert c.count('fn "cast_numeric"') == 2, c
    # number literals in a column of numerics (window.sql: VALUES (1, 1::numeric), (2, 2), (3, 'NaN'))
    out = translate('PostgreSQL', {'a': "SELECT b FROM (VALUES (1::numeric), (2), ('NaN')) t(b);\nb\n1\n2\nNaN\n"})['a']
    assert '(fn "cast_numeric" [(str "NaN")])' in case(out, 'a:0'), out
    # not with a column of texts
    out = translate('PostgreSQL', {'a': "SELECT b FROM (VALUES ('x'::text), (2), ('y')) t(b);\nb\nx\n2\ny\n"})['a']
    assert '(fn "cast_text" [(str "y")])' not in case(out, 'a:0'), out


@test
def split_of_a_file_of_cases():
    """Iteration 21: a file over the time limit is compiled again case by case (compile_spec.sh): each file
    written by split_cases.py has the header, one case and the evaluation; summary.py counts as not run only
    the cases over the limit."""
    sys.path.insert(0, HERE)
    import split_cases
    import summary
    out = translate('TiDB', {'a': "select 1;\n1\n1\nselect 2;\n2\n2\nselect 3;\n3\n3\n"})['a']
    with tempfile.TemporaryDirectory() as d:
        spec = os.path.join(d, 'Spec_a.v')
        with open(spec, 'w') as f:
            f.write(out)
        files = split_cases.split(spec, os.path.join(d, 'split'))
        assert len(files) == 3, files
        one = open(files[1]).read()
        assert one.count('mk_case') == 1 and 'mk_case "a:1"' in one, one
        assert one.startswith(out.split('Definition cases_a')[0]), one
        assert 'Eval vm_compute in (diagnose TiDB cases_a).' in one, one
        assert '"a:1" false' in one and not re.search(r'\);\n\]', one), one
        log = os.path.join(d, 'log')
        with open(log, 'w') as f:
            f.write('{"translated": 3}\n== testing/x/Spec_a.v\nSPLIT testing/x/Spec_a.v\nTIMEOUT_CASE a:2\n'
                    '     = ["a:1 | select 2; | expected [2] | got [3]"]\n')
        n, fails, timeouts, unfinished = summary.read(log, True)
        assert (n, sorted(fails), unfinished) == (3, ['a:1'], 1), (n, fails, unfinished)


@test
def queries_of_another_connection():
    """Iteration 23: the queries run under a connection other than the default one are not translated."""
    out = translate('MariaDB', {'a': (
        "select 1;\n1\n1\nconnect  u1,'localhost',u1,,;\nconnection u1;\nselect 2;\n2\n2\n"
        "disconnect u1;\nconnection default;\nselect 3;\n3\n3\n")})['a']
    assert 'select 1;' in out and 'select 3;' in out and 'select 2;' not in out, out


@test
def order_of_the_ordered_aggregates():
    """Audit after PR 74: json_object_agg, array_agg, ... over the rows of a FROM keep the scan order, which is
    implementation defined; with DISTINCT, or without FROM, the result is determined."""
    out = translate('PostgreSQL', {'a': (
        "SELECT json_object_agg(a, b) FROM (VALUES (1, 2), (3, 4)) t(a, b);\njson_object_agg\n{ \"1\" : 2, \"3\" : 4 }\n"
        "SELECT json_object_agg(1, 2);\njson_object_agg\n{ \"1\" : 2 }\n"
        "select array_agg(distinct a) from (values (1),(2)) v(a);\narray_agg\n{1,2}\n")})['a']
    assert case(out, 'a:0') == '' and case(out, 'a:1') != '' and case(out, 'a:2') != '', out


@test
def window_without_order():
    """Audit after PR 74: ROW_NUMBER, NTILE, LAG, ... over a window without ORDER BY are implementation defined;
    RANK and the aggregates are not; a query which the engine rejects is still a case."""
    out = translate('MariaDB', {'a': (
        "create table t1 (pk int, a int);\ninsert into t1 values (1, 1), (2, 2);\n"
        "select pk, row_number() over () from t1;\npk\trow_number() over ()\n1\t1\n2\t2\n"
        "select pk, rank() over () from t1;\npk\trank() over ()\n1\t1\n2\t1\n"
        "select pk, row_number() over (order by pk) from t1;\npk\trow_number() over (order by pk)\n1\t1\n2\t2\n"
        "select pk, lag(pk, 1) over () from t1;\n"
        "ERROR HY000: No order list in window specification for 'lag'\n")})['a']
    assert case(out, 'a:2') == '', out
    assert case(out, 'a:3') != '' and case(out, 'a:4') != '', out
    assert case(out, 'a:5').startswith('mk_case_error'), out
    # among peers: two rows with the same key of the ORDER BY
    out = translate('MariaDB', {'a': (
        "create table t1 (pk int, a int);\ninsert into t1 values (1, 1), (2, 1), (3, 2);\n"
        "select pk, row_number() over (order by a) from t1;\npk\tr\n1\t1\n2\t2\n3\t3\n"
        "select pk, row_number() over (order by pk) from t1;\npk\tr\n1\t1\n2\t2\n3\t3\n"
        "select pk, rank() over (order by a) from t1;\npk\tr\n1\t1\n2\t1\n3\t3\n")})['a']
    assert case(out, 'a:2') == '' and case(out, 'a:3') != '' and case(out, 'a:4') != '', out


@test
def dates_before_the_common_era():
    """Audit after PR 74: a date literal of a table '2040-04-10 BC' is a date of the year -2039 (it was read as
    2040-04-10)."""
    sys.path.insert(0, HERE)
    import sql2coq
    import datetime
    assert sql2coq.temporal_value('1970-01-01', 'date') == '(NullValues.VDate (0))'
    assert sql2coq.temporal_value('2040-04-10', 'date') == '(NullValues.VDate (%d))' % (
        datetime.date(2040, 4, 10) - datetime.date(1970, 1, 1)).days
    # 0001-01-01 is 719162 days before the epoch; 1 BC (year 0) is a leap year of 366 days
    assert sql2coq.temporal_value('0001-01-01 BC', 'date') == '(NullValues.VDate (%d))' % (-719162 - 366)
    # a timestamp of 1 BC: the day of the date, and the seconds of the time
    assert sql2coq.temporal_value('0001-01-01 00:00:01 BC', 'timestamp') == '(NullValues.VTs (%d) 0)' % (
        (-719162 - 366) * 86400 * 1000000 + 1000000)
    try:
        sql2coq.temporal_value('1997-02-29', 'date')
        assert False, 'not a date'
    except sql2coq.Skip:
        pass


@test
def prepared_statement_after_a_result():
    """Audit after PR 74: a PREPARE after a result is a statement, not a row (TiDB executor/jointest/join)."""
    out = translate('TiDB', {'a': (
        "select 2;\n2\n2\nprepare stmt1 from 'select 1';\nset @a = 1;\nexecute stmt1 using @a;\n1\n1\n")})['a']
    assert '[["2"]]' in case(out, 'a:0'), out


@test
def sorted_result():
    """Audit after PR 74: under --sorted_result, mysqltest sorts the rows before recording them: the case is
    unordered, even with an ORDER BY (TiDB executor/jointest/join recorded ORDER BY a DESC as 1, 2, 2)."""
    with tempfile.TemporaryDirectory() as d:
        script = ("create table t1 (a int);\ninsert into t1 values (1),(2),(2);\n--sorted_result\n"
                  "select * from t1 order by a desc;\nselect * from t1 order by a desc;\n")
        result = ("create table t1 (a int);\ninsert into t1 values (1),(2),(2);\n"
                  "select * from t1 order by a desc;\na\n1\n2\n2\nselect * from t1 order by a desc;\na\n2\n2\n1\n")
        open(os.path.join(d, 'a.test'), 'w').write(script)
        open(os.path.join(d, 'a.result'), 'w').write(result)
        out = os.path.join(d, 'out')
        subprocess.run([sys.executable, TOOL, '--dialect', 'TiDB', '--lenient', '--outdir', out, os.path.join(d, 'a.result')],
                       check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        text = open(os.path.join(out, 'Spec_a.v')).read()
        assert re.search(r'mk_case "a:2" false', text) and re.search(r'mk_case "a:3" true', text), text


@test
def unfollowed_changes():
    """Audit after PR 74 (TODO 8.28): statements which change tables and which the translator does not follow make
    them unreliable: EXPLAIN ANALYZE of a change, TiDB's BATCH DML, INSERT IGNORE into a table with a foreign key,
    a temporary table."""
    out = translate('TiDB', {'a': (
        "create table t (a int);\ninsert into t values (1);\nexplain analyze insert into t values (2);\n"
        "select * from t;\na\n1\n2\n"
        "create table p (i int primary key);\ncreate table c (i int, foreign key (i) references p (i));\n"
        "insert into p values (1);\ninsert ignore into c values (1), (2);\nselect * from c;\ni\n1\n"
        "create table u (a int);\ninsert into u values (1);\nselect * from u;\na\n1\n")})['a']
    assert 'select * from t;' not in out and 'select * from c;' not in out and 'select * from u;' in out, out


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
