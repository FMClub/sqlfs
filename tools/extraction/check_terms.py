#!/usr/bin/env python3
"""Check the translation of terms to OCaml (term2ml.py) on compiled conformance files (TODO 6.6): every case of
each Spec_*.v file is translated, linked with the library of build_lib.sh and checked with [diagnose]; the
failing cases are printed per file, and must be those of the Coq run.

  tools/extraction/check_terms.py LIBDIR DIALECT SPEC_FILES...
"""
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import term2ml  # noqa: E402


def main():
    lib, dialect, files = os.path.abspath(sys.argv[1]), sys.argv[2], sys.argv[3:]
    total = bad = 0
    for f in files:
        text = Path(f).read_text()
        m = re.search(r':= \[\n(.*)\n\]\.', text, re.S)
        if not m:
            continue
        cases = [c.strip().rstrip(';') for c in m.group(1).split('\n') if c.strip()]
        try:
            body = ';\n'.join(term2ml.to_ml(c) for c in cases)
        except ValueError as e:
            print('== %s: not translated: %s' % (f, e))
            bad += 1
            continue
        with tempfile.TemporaryDirectory() as d:
            ml = Path(d) / 'cases.ml'
            ml.write_text('open Sqlfs_lib\nlet () =\n  match dialect_named %s with\n'
                          '  | None -> exit 2\n'
                          '  | Some dl -> List.iter print_endline (diagnose dl [%s])\n'
                          % (term2ml.ml_string(dialect), body))
            exe = Path(d) / 'cases'
            r = subprocess.run(['ocamlopt', '-I', lib, os.path.join(lib, 'sqlfs_lib.cmx'),
                                os.path.join(lib, 'prelude.cmx'), str(ml), '-o', str(exe)],
                               capture_output=True, text=True, cwd=d)
            if r.returncode != 0:
                print('== %s: does not compile\n%s' % (f, (r.stdout + r.stderr)[-600:]))
                bad += 1
                continue
            r = subprocess.run(['sh', '-c', 'ulimit -s unlimited; exec "$0"', str(exe)], capture_output=True,
                               text=True, timeout=600)
            fails = [x for x in r.stdout.split('\n') if x]
            total += len(cases)
            print('== %s: %d cases, %d failing' % (Path(f).name, len(cases), len(fails)))
            for x in fails:
                print('  ' + x)
    print('files not run: %d; cases run: %d' % (bad, total))


if __name__ == '__main__':
    main()
