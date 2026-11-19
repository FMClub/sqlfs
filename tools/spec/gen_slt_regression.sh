#!/bin/sh
# Regenerates the regression tests which are copied from sqllogictest into src/testing/slt/.
#
#   tools/spec/gen_slt_regression.sh SLT_CHECKOUT
#
# sqllogictest is released under CC0 / MIT / BSD (any of them): the queries and their results can be
# copied. The files are checked as part of the build (src/_CoqProject): each one asserts that the
# formal semantics of a dialect gives the results which the engine recorded.
set -e
SLT="$1"
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
OUT="$ROOT/src/testing/slt"
T="$SLT/test"
rm -rf "$OUT"; mkdir -p "$OUT"
EXPR=$(ls "$T"/random/expr/slt_good_*.test | head -6)
gen() { # engine dialect max files...
  e="$1"; d="$2"; m="$3"; shift 3
  python3 "$ROOT/tools/spec/slt2coq.py" --engine "$e" --dialect "$d" --max "$m" --assert 1 --outdir "$OUT/$d" "$@"
}
gen sqlite     SQLite          150 "$T"/evidence/*.test $EXPR
gen postgresql PostgreSQL      150 "$T"/evidence/*.test $EXPR
gen mysql      MySQL           150 "$T"/evidence/*.test $EXPR
gen mysql      OceanBaseMySQL  150 "$T"/evidence/*.test $EXPR
# the project file lists the generated tests
( cd "$ROOT/src" && ls testing/slt/*/Slt_*.v ) > "$OUT/FILES"
