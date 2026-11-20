#!/bin/sh
# The logic bugs of logic_bugs.json as regression cases (TODO 5.6): tools/spec/engine_bugs/run.sh
set -e
ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
T="$(mktemp -d)"
python3 "$ROOT/tools/spec/engine_bugs/to_result.py" "$ROOT/tools/spec/engine_bugs/logic_bugs.json" "$T"
for e in TiDB:tidb MariaDB:mariadb MySQL:mysql; do
  D=${e%%:*}; n=${e##*:}
  [ -f "$T/bugs_$n.result" ] && "$ROOT/tools/spec/suite_run.sh" "$D" "bugs_$n" "$T/bugs_$n.result"
done
rm -rf "$T"
