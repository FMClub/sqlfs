#!/bin/sh
# Conformance of a dialect with the recorded results of a mysqltest suite (TODO 5.2): MariaDB
# (mysql-test/main), MySQL (mysql-test/r), TiDB (tests/integrationtest/r).
#
#   tools/spec/suite_run.sh DIALECT NAME RESULT_FILES...
#
# The cases are translated with sql2coq.py --lenient into src/testing/suite_NAME/ (not tracked: data of the
# engines' test suites) and each file is compiled alone, with at most MEM_KB of memory and FILE_TIMEOUT
# seconds; every file prints its failing cases.
set -e
D="$1"; NAME="$2"; shift 2
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
OUT="$ROOT/src/testing/suite_$NAME"
rm -rf "$OUT"
python3 "$ROOT/tools/spec/sql2coq.py" --dialect "$D" --lenient --outdir "$OUT" "$@"
cd "$ROOT/src"
for f in testing/suite_$NAME/Spec_*.v; do
  echo "== $f"
  ( ulimit -v "${MEM_KB:-5000000}"; timeout "${FILE_TIMEOUT:-600}" coqc -R . SQLFS "$f" 2>&1 ) | grep -v "^ *: " || true
done
