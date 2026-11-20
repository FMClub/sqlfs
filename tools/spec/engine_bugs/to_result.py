#!/usr/bin/env python3
"""Logic bugs of the engines as regression cases (TODO 5.6).

logic_bugs.json lists confirmed logic bugs (wrong results) with their reproducer and the CORRECT result, as
stated by the report, the developers or the test of the fix (field correct_source). This script writes one
result file per engine (statements, then the correct rows), which tools/spec/suite_run.sh replays against the
dialect: the model must give the correct result, not the engine's wrong one.

Usage: to_result.py logic_bugs.json OUTDIR
"""
import json
import os
import sys

bugs = json.load(open(sys.argv[1]))
out = sys.argv[2]
os.makedirs(out, exist_ok=True)
by = {}
for b in bugs:
    by.setdefault(b['engine'], []).append(b)
for eng, bs in by.items():
    lines = []
    for b in bs:
        for st in b['setup']:
            if st.lower().startswith('create unique index') or st.lower().startswith('create index'):
                continue  # indexes do not change the rows
            lines.append(st)
        lines.append(b['query'])
        n = len(b['correct'][0]) if b['correct'] else 1
        lines.append('\t'.join('c%d' % i for i in range(n)))
        lines += ['\t'.join(r) for r in b['correct']]
        lines.append('DROP TABLE IF EXISTS t, t1;')
    open(os.path.join(out, 'bugs_%s.result' % eng.lower()), 'w').write('\n'.join(lines) + '\n')
    print(eng, len(bs))
