#!/bin/sh
# Regenerates docs/closeouts/ENGINE.md: tools/functions/closeout.sh ENGINE SOURCE "description of the source"
set -e
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
T="$(mktemp -d)"
python3 "$ROOT/tools/functions/catalogue.py" extract "$1" "$2" > "$T/names.txt"
python3 "$ROOT/tools/functions/catalogue.py" coq "$1" "$T/names.txt" > "$T/Catalogue.v"
(cd "$ROOT/src" && coqc -R . SQLFS "$T/Catalogue.v") > "$T/out.txt"
python3 "$ROOT/tools/functions/catalogue.py" report "$1" "$2" "$T/names.txt" "$T/out.txt" "$3"
rm -rf "$T"
