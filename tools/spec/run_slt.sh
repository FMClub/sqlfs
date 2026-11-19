#!/bin/sh
# Conformance of a dialect with sqllogictest.
#
#   tools/spec/run_slt.sh SLT_CHECKOUT ENGINE DIALECT [MAX_QUERIES_PER_FILE] [FILES...]
#
# SLT_CHECKOUT is a clone of https://github.com/gregrahn/sqllogictest, ENGINE the name which its
# directives use for the engine (sqlite, mysql, postgresql, oracle), DIALECT a dialect of
# src/data/dialects. By default the scripts of test/evidence are run. One Coq file is generated for each
# script in src/testing/spec_slt/ (not tracked) and compiled.
set -e
SLT="$1"; E="$2"; D="$3"; MAX="${4:-0}"; shift 4 2>/dev/null || shift $#
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
if [ "$#" -eq 0 ]; then set -- "$SLT"/test/evidence/*.test; fi
rm -rf "$ROOT/src/testing/spec_slt"
python3 "$ROOT/tools/spec/slt2coq.py" --engine "$E" --dialect "$D" --max "$MAX" --outdir "$ROOT/src/testing/spec_slt" "$@"
cd "$ROOT/src"
coqc -R . SQLFS testing/SltRunner.v
ls testing/spec_slt/Slt_*.v | xargs -P "${JOBS:-4}" -I{} sh -c 'echo "== {}"; coqc -R . SQLFS {} 2>&1 | grep -v "^ *: " | head -${LINES_MAX:-30}'
