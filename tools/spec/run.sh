#!/bin/sh
# Conformance of a dialect with the recorded results of a test suite.
#
#   tools/spec/run.sh OCEANBASE_CHECKOUT DIALECT [FILES...]
#
# OCEANBASE_CHECKOUT is a clone of https://github.com/oceanbase/oceanbase; DIALECT is the name of a
# dialect of src/data/dialects (for instance OceanBaseMySQL). One Coq file is generated for each result
# file, in src/testing/spec/ (not tracked: it contains data from the test suite of OceanBase), and
# compiled; every file prints the identifiers of the cases which fail.
set -e
OB="$1"; D="$2"; shift 2
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
SUITE="$OB/tools/deploy/mysql_test"
if [ "$#" -eq 0 ]; then
  set -- "$SUITE"/r/mysql/*.result "$SUITE"/test_suite/*/r/mysql/*.result
fi
rm -rf "$ROOT/src/testing/spec"
python3 "$ROOT/tools/spec/sql2coq.py" --dialect "$D" --outdir "$ROOT/src/testing/spec" "$@"
cd "$ROOT/src"
coqc -R . SQLFS testing/SpecRunner.v
# a file which takes more than FILE_TIMEOUT seconds (a join of dozens of tables: the tuples of the
# model are lists, and a row of 200 columns is slow to build) is reported as TIMEOUT
ls testing/spec/Spec_*.v | xargs -P "${JOBS:-4}" -I{} sh -c 'echo "== {}"; timeout ${FILE_TIMEOUT:-600} coqc -R . SQLFS {} > /tmp/spec_$$.out 2>&1; [ $? -eq 124 ] && echo "TIMEOUT {}"; grep -v "^ *: " /tmp/spec_$$.out | head -${LINES_MAX:-30}; rm -f /tmp/spec_$$.out'
