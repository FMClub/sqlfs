#!/usr/bin/env python3
"""PostgreSQL regression tests in the format of the result files of mysqltest (TODO 5.3).

A file `expected/NAME.out` of `src/test/regress` echoes each statement of `sql/NAME.sql` followed by
its output: a table printed by psql (a header, a line of dashes, the rows, `(N rows)`), a command
tag (`CREATE TABLE`, `INSERT 0 3`), or an error. This script writes NAME.result where each statement
is followed by its rows separated by tabs (the format which `sql2coq.py` reads):

- the command tags, notices and errors are dropped (an error is written `ERROR ...`, so that the
  statement is not translated);
- psql prints NULL and the empty string the same way (an empty cell): a result with an empty cell
  is written as an error (`ERROR ambiguous empty cell`), and the statement is not checked;
- a cell continued on the next line (`+`) and the expanded display (`\\x`) are not read: the result
  is dropped the same way;
- the psql meta-commands (`\\set`, `\\pset`, ...) are dropped; a file which uses `\\pset` or `\\x`
  changes the display, and is skipped as a whole.

The data of the regression database (`onek`, `tenk1`, `int4_tbl`, ...) are created by `test_setup.sql`
and `create_table.sql` from files which `COPY` reads: the tables which no statement of the file creates
are unknown to the translator, and the queries on them are skipped.

Usage: pg2result.py REGRESS_DIR OUTDIR NAME...
"""
import os
import re
import sys

TAG = re.compile(r'^(CREATE|DROP|ALTER|INSERT|UPDATE|DELETE|SET|RESET|BEGIN|COMMIT|ROLLBACK|ANALYZE|VACUUM|'
                 r'COPY|GRANT|REVOKE|COMMENT|TRUNCATE|SELECT \d+|DO|PREPARE|EXECUTE|DEALLOCATE|DECLARE|'
                 r'FETCH|MOVE|CLOSE|SAVEPOINT|RELEASE|LOCK|DISCARD|EXPLAIN|LISTEN|NOTIFY|CHECKPOINT|CALL|'
                 r'REFRESH|CLUSTER|REINDEX|SECURITY|IMPORT|MERGE \d+|START TRANSACTION)\b')


def complete(s):
    """A statement ends with ';' outside quotes, comments and dollar quotes."""
    inq = None
    i = 0
    depth = 0
    while i < len(s):
        c = s[i]
        if inq:
            if s.startswith(inq, i):
                i += len(inq)
                inq = None
                continue
        elif s.startswith('--', i):
            j = s.find('\n', i)
            i = len(s) if j < 0 else j
            continue
        elif s.startswith('/*', i):
            j = s.find('*/', i)
            if j < 0:
                return False
            i = j + 2
            continue
        elif c in "'\"":
            inq = c
        elif c == '$':
            m = re.match(r'\$[A-Za-z_]*\$', s[i:])
            if m:
                inq = m.group(0)
                i += len(inq)
                continue
        elif c == '(':
            depth += 1
        elif c == ')':
            depth -= 1
        i += 1
    last = s.rstrip().split('\n')[-1]
    last = re.sub(r'\s--[^\']*$', '', ' ' + last)
    return inq is None and (s.rstrip().endswith(';') or last.rstrip().endswith(';'))


def literal_spans_lines(s):
    """a string literal (outside comments) which contains a newline"""
    inq = False
    i = 0
    while i < len(s):
        c = s[i]
        if inq:
            if c == "'":
                if s.startswith("''", i):
                    i += 2
                    continue
                inq = False
            elif c == '\n':
                return True
        elif s.startswith('--', i):
            j = s.find('\n', i)
            i = len(s) if j < 0 else j
            continue
        elif c == "'":
            inq = True
        i += 1
    return False


def parse_out(lines):
    """[(statement, output lines)]"""
    items = []
    i = 0
    n = len(lines)
    while i < n:
        l = lines[i]
        if l.strip() == '' or l.lstrip().startswith('--') or l.startswith('\\'):
            i += 1
            continue
        stmt = l
        while not complete(stmt) and i + 1 < n:
            i += 1
            stmt += '\n' + lines[i]
        i += 1
        out = []
        # the output: until a blank line after a table, or a line which is not output
        if i < n and i + 1 < n and re.match(r'^-+(\+-+)*$', lines[i + 1].strip()) and '|' in lines[i] or \
           (i + 1 < n and re.match(r'^-+$', lines[i + 1].strip()) and lines[i].strip()):
            while i < n and not re.match(r'^\(\d+ rows?\)$', lines[i]):
                out.append(lines[i])
                i += 1
            if i < n:
                out.append(lines[i])
                i += 1
        else:
            # (the regression tests run psql with -q: no command tags are printed)
            while i < n and (re.match(r'^(ERROR|WARNING|NOTICE|DETAIL|HINT|LINE \d+|CONTEXT|INFO|'
                                                              r'\s*\^|QUERY|server closed)', lines[i])):
                out.append(lines[i])
                i += 1
        items.append((stmt, out))
    return items


def iso_cell(c):
    """The regression database runs with DateStyle 'Postgres, MDY': a date is printed 04-09-1957 and a
    timestamp Mon Feb 23 00:00:00.5 2004. The runner evaluates the cases with this DateStyle too (the dialect
    PostgreSQL_regress, and its client in SpecRunner.v), so the cell is kept as it is: a date inside a text
    (concat (..., d)) is in this style as well. A timestamp with a time zone (the database is in PST8PDT, the
    model in UTC) and an interval in the postgres_verbose style give None."""
    if re.search(r'\b(PST|PDT|UTC|GMT|LMT)\b', c) or c.startswith('@ '):
        return None
    # a timestamp of the Postgres style followed by a time zone ('Thu Jan 01 00:00:00 1001 LMT')
    if re.match(r'(Mon|Tue|Wed|Thu|Fri|Sat|Sun) \w{3} \d\d \d\d:\d\d', c) and not \
       re.fullmatch(r'(Mon|Tue|Wed|Thu|Fri|Sat|Sun) \w{3} \d\d \d\d:\d\d:\d\d(\.\d+)? \d{4}( BC)?', c):
        return None
    return c


STATEMENT = re.compile(r'^(select|insert|update|delete|create|drop|alter|set|show|explain|truncate|replace|with|'
                       r'commit|rollback|use|analyze|call|start|begin)\b', re.I)


def aligned_cells(header, rule, raw):
    """The cells of a psql table. psql aligns the numbers on the right and the other values on the left, so
    the spaces at the start of a cell are padding in a column of numbers and data in a column of texts
    (to_char (485, '999') is ' 485'). A column is aligned on the left if a cell has padding at its end: the
    cells keep their leading spaces. If no cell has, either the column is aligned on the right or every value
    fills it; the cells are kept as they are too, and the comparison of a number ignores its leading spaces
    (SpecRunner.v, cell_ok). The spaces at the end of a value cannot be told from the padding: they are
    dropped, but in a column of one row wider than its header, which the value fills."""
    widths = [len(seg) - 2 for seg in rule.split('+')]
    if len(widths) != len(header):
        return [[c.strip() for c in r] for r in raw]
    cols = []
    for j, w in enumerate(widths):
        contents = [r[j][1:].ljust(w)[:w] for r in raw]
        # a column wider than its header has a value of its width; with one row, it is the cell, whose spaces at
        # the end are then data (' true '::json)
        if len(contents) == 1 and w > len(header[j]):
            cols.append(contents)
        else:
            cols.append([c.rstrip() for c in contents])
    return [list(r) for r in zip(*cols)] if cols and raw else []


def convert_output(out):
    if not out:
        return []
    if out[0].startswith('ERROR'):
        return ['ERROR ' + out[0][6:].strip()]
    if DATESTYLE_CHANGED:
        return ['ERROR DateStyle changed by the test']
    if len(out) < 3 or not re.match(r'^\(\d+ rows?\)$', out[-1]):
        return []
    header = [c.strip() for c in out[0].split('|')]
    for l in out[2:-1]:
        if l.endswith('+') or (len(l.split('|')) != len(header)):
            return ['ERROR multi-line cell']
    table = aligned_cells(header, out[1], [l.split('|') for l in out[2:-1]])
    rows = []
    for cells in table:
        if any(c == '' for c in cells):
            return ['ERROR ambiguous empty cell']
        cells = [iso_cell(c) for c in cells]
        if any(c is None for c in cells):
            return ['ERROR time zone or interval style']
        if STATEMENT.match(cells[0]):
            return ['ERROR a row which reads as a statement']
        rows.append('\t'.join(cells))
    if len(header) == 1 and header[0] == '':
        return ['ERROR unnamed column']
    return ['\t'.join(header)] + rows


MAX_ROWS = 1000
DATESTYLE_CHANGED = False


def sql_lit(v):
    if v == '\\N':
        return 'NULL'
    if re.fullmatch(r'-?\d+(\.\d+)?', v):
        return v
    return "'" + v.replace("'", "''") + "'"


def setup_statements(regress):
    """The tables of test_setup.sql: its CREATE TABLE and INSERT statements, and its COPY of a data file
    as INSERT statements (the tables of more than MAX_ROWS rows are left out: tenk1, tenk2)."""
    text = open(os.path.join(regress, 'sql', 'test_setup.sql'), encoding='utf-8').read()
    lines = [l for l in text.split('\n') if not l.lstrip().startswith('--')]
    out, skipped = [], set()
    filename = None
    i = 0
    while i < len(lines):
        l = lines[i]
        if not l.strip():
            i += 1
            continue
        m = re.match(r"^\\set filename :abs_srcdir '(/data/[^']+)'", l)
        if m:
            filename = m.group(1)
            i += 1
            continue
        if l.startswith('\\'):
            i += 1
            continue
        st = l
        while not complete(st) and i + 1 < len(lines):
            i += 1
            st += '\n' + lines[i]
        i += 1
        st = re.sub(r'\s*\n\s*', ' ', st.strip())
        m = re.match(r'^COPY (\w+) FROM', st, re.I)
        if m:
            rows = open(regress + filename, encoding='utf-8').read().split('\n')
            rows = [r for r in rows if r]
            if len(rows) > MAX_ROWS:
                skipped.add(m.group(1).lower())
                continue
            for k in range(0, len(rows), 100):
                vals = ', '.join('(' + ', '.join(sql_lit(v) for v in r.split('\t')) + ')' for r in rows[k:k + 100])
                out.append('INSERT INTO %s VALUES %s;' % (m.group(1), vals))
            continue
        m = re.match(r'^CREATE TABLE (\w+) AS SELECT \* FROM (\w+);$', st, re.I)
        if m:
            if m.group(2).lower() in skipped:
                skipped.add(m.group(1).lower())
                continue
            # a copy: the same columns and rows
            base = [x for x in out if re.match(r'^CREATE TABLE %s\b' % m.group(2), x, re.I)]
            if base:
                out.append(re.sub(r'^CREATE TABLE %s\b' % m.group(2), 'CREATE TABLE ' + m.group(1), base[0], flags=re.I))
                out += [re.sub(r'^INSERT INTO %s\b' % m.group(2), 'INSERT INTO ' + m.group(1), x, flags=re.I)
                        for x in out if re.match(r'^INSERT INTO %s\b' % m.group(2), x, re.I)]
            continue
        if re.match(r'^(CREATE TABLE|INSERT INTO)\b', st, re.I) and not re.search(r'\bINHERITS\b', st, re.I):
            out.append(st)
    return out


def main():
    global DATESTYLE_CHANGED
    regress, outdir = sys.argv[1], sys.argv[2]
    os.makedirs(outdir, exist_ok=True)
    global SETUP
    SETUP = setup_statements(regress)
    for name in sys.argv[3:]:
        src = os.path.join(regress, 'expected', name + '.out')
        text = open(src, encoding='utf-8', errors='replace').read()
        if re.search(r'^\\(pset|x|a|f|C|t)\b', text, re.M):
            sys.stderr.write('%s: skipped (psql display settings)\n' % name)
            continue
        lines = text.split('\n')
        if lines and lines[-1] == '':
            lines.pop()
        DATESTYLE_CHANGED = False
        copies = []
        sql_path = os.path.join(regress, 'sql', name + '.sql')
        if os.path.exists(sql_path):
            sql_lines = open(sql_path, encoding='utf-8', errors='replace').read().split('\n')
            j = 0
            while j < len(sql_lines):
                if re.match(r'^\s*copy\s+\w+.*\bfrom\s+stdin', sql_lines[j], re.I):
                    j += 1
                    block = []
                    while j < len(sql_lines) and sql_lines[j] != '\\.':
                        block.append(sql_lines[j])
                        j += 1
                    copies.append(block)
                j += 1
        res = list(SETUP)
        for stmt, out in parse_out(lines):
            # one statement per line group, comments removed (sql2coq reads the statement up to ';')
            if literal_spans_lines(stmt):
                continue  # a literal on several lines: joining the lines would change it
            st = re.sub(r'(?m)--.*$', '', stmt).strip()
            st = re.sub(r'\s*\n\s*', ' ', st)
            if not st:
                continue
            if re.match(r'^(set|reset)\s+(session\s+)?datestyle\b', st, re.I):
                DATESTYLE_CHANGED = not st.lower().startswith('reset')
                continue
            if re.match(r'^explain\b', st, re.I):
                continue
            m = re.match(r'^copy\s+(\w+)(\s*\([^)]*\))?\s+from\s+stdin', st, re.I)
            if m:
                # the data of COPY ... FROM stdin is in the .sql file only (psql does not echo it)
                rows = copies.pop(0) if copies else []
                cols = m.group(2) or ''
                for k in range(0, len(rows), 100):
                    vals = ', '.join('(' + ', '.join(sql_lit(v) for v in r.split('\t')) + ')' for r in rows[k:k + 100])
                    res.append('INSERT INTO %s%s VALUES %s;' % (m.group(1), cols, vals))
                continue
            res.append(st)
            res += convert_output(out)
        with open(os.path.join(outdir, name + '.result'), 'w') as f:
            f.write('\n'.join(res) + '\n')


if __name__ == '__main__':
    main()
