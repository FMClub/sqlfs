#!/usr/bin/env python3
"""Split a file of conformance cases (written by sql2coq.py) into one file per case.

A file of cases is compiled as one vm_compute: when it goes over the time limit of the runner, the
results of all its cases are lost. compile_spec.sh then calls this script and compiles the cases one
by one, so that only the slow ones are lost.

Usage: split_cases.py SPEC_FILE OUTDIR    (prints the paths of the files written, one per line)

The file is: a header (Require ...), "Definition cases_NAME : list spec_case := [", the cases (each
starts on a line "  mk_case..." or "  with_dialect ..."), "].", and "Eval vm_compute in (diagnose DIALECT cases_NAME)."
"""
import os
import re
import sys


def split(path, outdir):
    lines = open(path, encoding='utf-8').read().split('\n')
    start = next(i for i, l in enumerate(lines) if re.match(r'Definition cases_\w+ : list spec_case := \[$', l))
    end = next(i for i in range(start, len(lines)) if lines[i] == '].')
    name = re.match(r'Definition (cases_\w+)', lines[start]).group(1)
    ev = next(l for l in lines[end:] if l.startswith('Eval vm_compute in (diagnose'))
    header = '\n'.join(lines[:start])
    cases = []
    for l in lines[start + 1:end]:
        if l.startswith('  mk_case') or l.startswith('  with_dialect'):
            cases.append(l)
        elif cases:
            cases[-1] += '\n' + l
    os.makedirs(outdir, exist_ok=True)
    base = os.path.basename(path)[:-2]
    out = []
    for k, c in enumerate(cases):
        c = c.rstrip()
        if c.endswith(';'):
            c = c[:-1]
        p = os.path.join(outdir, '%s_%d.v' % (base, k))
        with open(p, 'w', encoding='utf-8') as f:
            f.write('%s\nDefinition %s : list spec_case := [\n%s\n].\n%s\n' % (header, name, c, ev))
        out.append(p)
    return out


if __name__ == '__main__':
    for p in split(sys.argv[1], sys.argv[2]):
        print(p)
