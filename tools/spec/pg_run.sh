#!/bin/sh
# Conformance of the PostgreSQL dialect with the PostgreSQL regression tests (TODO 5.3).
#
#   tools/spec/pg_run.sh POSTGRES_CHECKOUT [NAMES...]
#
# NAMES are tests of src/test/regress (select, union, ...). The results are converted by pg2result.py,
# translated by sql2coq.py --dialect PostgreSQL --lenient into src/testing/pgspec/ (not tracked: data of
# the PostgreSQL test suite) and compiled; every file prints its failing cases.
set -e
PG="$1"; shift
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
if [ "$#" -eq 0 ]; then
  set -- select aggregates window with join subselect union numeric strings text float8 date timestamp json jsonb arrays groupingsets
fi
T="$(mktemp -d)"
python3 "$ROOT/tools/spec/pg2result.py" "$PG/src/test/regress" "$T" "$@"
rm -rf "$ROOT/src/testing/pgspec"
python3 "$ROOT/tools/spec/sql2coq.py" --dialect PostgreSQL --lenient --outdir "$ROOT/src/testing/pgspec" "$T"/*.result
rm -rf "$T"
cd "$ROOT/src"
ls testing/pgspec/Spec_*.v | xargs -P "${JOBS:-3}" -I{} sh -c 'echo "== {}"; timeout ${FILE_TIMEOUT:-900} coqc -R . SQLFS {} > /tmp/pgspec_$$.out 2>&1; [ $? -eq 124 ] && echo "TIMEOUT {}"; grep -v "^ *: " /tmp/pgspec_$$.out; rm -f /tmp/pgspec_$$.out'
