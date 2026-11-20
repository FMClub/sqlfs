#!/usr/bin/env python3
"""The examples of the Oracle-mode documentation of OceanBase as result files (TODO 5.5).

The documentation (oceanbase-doc, en-US) shows the statements of its examples after an `obclient>` prompt, and the
result of a query as the table which the client prints. Each page with such examples becomes one result file: the
statements of its code blocks in order (CREATE, INSERT, ..., the queries), each query followed by its rows, which
tools/spec/sql2coq.py --dialect OceanBaseOracle --lenient translates. A query whose printed output is not a table
(an error, `Empty set`, a plan) is kept without rows only when the page says `Empty set`; otherwise it is left out.

  tools/spec/oradoc2result.py DOC_CHECKOUT OUTDIR
"""
import glob
import os
import re
import sys

PROMPT = re.compile(r'\s*obclient(?: \[[^\]]*\])?>\s?(.*)')


def table_rows(lines, k):
    """the rows of the table printed from line k (a border +---+), and the line after it"""
    if k >= len(lines) or not lines[k].strip().startswith('+-'):
        return None, k
    rows, borders = [], 0
    while k < len(lines):
        l = lines[k].strip()
        if l.startswith('+-'):
            borders += 1
            k += 1
            if borders == 3:
                break
            continue
        if not l.startswith('|'):
            break
        cells = [c.strip() for c in l.strip('|').split('|')]
        rows.append(cells)
        k += 1
    if not rows:
        return None, k
    return rows[1:], k  # without the header


def page_cases(text):
    out = []
    for blk in re.findall(r'```[^\n]*\n(.*?)```', text, re.S):
        lines = blk.split('\n')
        i = 0
        while i < len(lines):
            m = PROMPT.match(lines[i])
            if not m:
                i += 1
                continue
            st, j = m.group(1), i
            while not st.rstrip().endswith(';') and j + 1 < len(lines) and not PROMPT.match(lines[j + 1]):
                j += 1
                st += ' ' + lines[j].strip()
            st = st.strip()
            if not st.endswith(';'):
                i = j + 1
                continue
            if re.match(r'(?is)\s*(select|with)\b', st):
                rows, k = table_rows(lines, j + 1)
                if rows is not None:
                    out.append((st, rows))
                elif j + 1 < len(lines) and lines[j + 1].strip().lower().startswith('empty set'):
                    out.append((st, []))
                i = max(k, j + 1)
            else:
                out.append((st, None))
                i = j + 1
    return out


def main():
    doc, outdir = sys.argv[1], sys.argv[2]
    os.makedirs(outdir, exist_ok=True)
    pages = [f for f in glob.glob(os.path.join(doc, 'en-US', '**', '*.md'), recursive=True) if 'oracle' in f.lower()]
    nq = nf = 0
    for f in sorted(pages):
        cases = page_cases(open(f, errors='replace').read())
        if not any(rows is not None for _, rows in cases):
            continue
        lines = []
        for st, rows in cases:
            lines.append(st)
            if rows is not None:
                n = len(rows[0]) if rows else 1
                lines.append('\t'.join('c%d' % c for c in range(n)))
                lines += ['\t'.join(r) for r in rows]
                nq += 1
        name = re.sub(r'\W', '_', os.path.splitext(os.path.basename(f))[0])[:60]
        with open(os.path.join(outdir, 'oradoc_%s.result' % name), 'w') as o:
            o.write('\n'.join(lines) + '\n')
        nf += 1
    print('%d pages, %d queries with their results' % (nf, nq))


if __name__ == '__main__':
    main()
