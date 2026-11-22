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
# the cases are evaluated with the DateStyle of the regression database (PostgreSQL_regress)
python3 "$ROOT/tools/spec/sql2coq.py" --dialect PostgreSQL --eval-dialect PostgreSQL_regress --lenient --outdir "$ROOT/src/testing/pgspec" "$T"/*.result
rm -rf "$T"
cd "$ROOT/src"
# a file over FILE_TIMEOUT is compiled again case by case (compile_spec.sh); the outputs of the files are not
# interleaved: each is printed when it is done
ls testing/pgspec/Spec_*.v | xargs -P "${JOBS:-3}" -I{} sh -c 'o=$(echo "== {}"; "$0" {}); echo "$o"' "$ROOT/tools/spec/compile_spec.sh"
