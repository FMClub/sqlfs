#!/bin/sh
# Compile one file of conformance cases (run from src/) and print its failing cases.
#
#   tools/spec/compile_spec.sh FILE
#
# FILE_TIMEOUT (seconds, default 900) bounds the compilation of the file. A file which goes over it is
# reported as "SPLIT FILE" and its cases are compiled one by one (split_cases.py), each within
# CASE_TIMEOUT seconds (default 120): a case which goes over it is reported as "TIMEOUT_CASE ID", and
# the failing cases of the others are printed as usual. With CASE_TIMEOUT=0 the file is reported as
# "TIMEOUT FILE" and not split. LINES_MAX limits the lines printed per file (default: all).
F="$1"
HERE="$(cd "$(dirname "$0")" && pwd)"
OUT="$(mktemp)"
timeout "${FILE_TIMEOUT:-900}" coqc -R . SQLFS "$F" > "$OUT" 2>&1
st=$?
if [ "$st" -eq 124 ]; then
  if [ "${CASE_TIMEOUT:-120}" -eq 0 ]; then
    echo "TIMEOUT $F"
  else
    echo "SPLIT $F"
    D="$(mktemp -d "$(dirname "$F")/split_XXXXXX")"
    for c in $(python3 "$HERE/split_cases.py" "$F" "$D"); do
      timeout "${CASE_TIMEOUT:-120}" coqc -R . SQLFS "$c" > "$OUT" 2>&1
      if [ $? -eq 124 ]; then
        echo "TIMEOUT_CASE $(grep -o 'mk_case[a-z_]* "[^"]*"' "$c" | head -1 | sed 's/.*"\(.*\)"/\1/')"
      else
        grep -v "^ *: " "$OUT" | grep -v '^ *= \[\]$'
      fi
    done
    rm -rf "$D"
  fi
else
  grep -v "^ *: " "$OUT" | head -"${LINES_MAX:-100000}"
fi
rm -f "$OUT"
