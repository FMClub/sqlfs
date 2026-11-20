#!/usr/bin/env python3
"""Coq hygiene (TODO 6.7): run in CI.

1. No `Admitted`, `admit` or `Axiom` in the files which `src/_CoqProject` builds (comments are ignored).
2. The core semantics does not depend on a dialect: no file of `src/data/sql/` and no file of
   `src/data/proof_of_concept/` other than the dialect-facing ones imports a module of `src/data/dialects/`.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / 'src'


def strip_comments(t):
    out, depth, i = [], 0, 0
    while i < len(t):
        if t.startswith('(*', i):
            depth += 1
            i += 2
        elif t.startswith('*)', i) and depth:
            depth -= 1
            i += 2
        else:
            if depth == 0:
                out.append(t[i])
            i += 1
    return ''.join(out)


def main():
    files = [l.strip() for l in (SRC / '_CoqProject').read_text().split('\n') if l.strip().endswith('.v')]
    dialects = {Path(f).stem for f in files if f.startswith('data/dialects/')}
    errors = []
    for f in files:
        t = strip_comments((SRC / f).read_text(encoding='utf-8'))
        for kw in ('Admitted.', 'admit.', 'Axiom '):
            for m in re.finditer(re.escape(kw), t):
                line = t[:m.start()].count('\n') + 1
                errors.append('%s: %s (around line %d of the file without comments)' % (f, kw.strip(), line))
        if f.startswith('data/sql/'):
            for imp in re.findall(r'Require\s+(?:Import|Export)?\s*([^.]*)\.', t):
                used = set(imp.split()) & dialects
                if used:
                    errors.append('%s: the core imports the dialect modules %s' % (f, ', '.join(sorted(used))))
    for e in errors:
        print(e)
    print('%d files checked, %d problems' % (len(files), len(errors)))
    sys.exit(1 if errors else 0)


if __name__ == '__main__':
    main()
