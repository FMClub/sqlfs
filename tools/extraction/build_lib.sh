#!/bin/sh
# The extracted interpreter as a library (TODO 6.6): the semantics, the dialects, [run_rows], [result_text] and
# the constructors of queries that tools/spec/sql2coq.py emits (vocab.txt) are extracted once to OCaml and
# compiled; tools/sqlfs_run.py --extracted OUTDIR then translates each query to OCaml (term2ml.py), links it
# with the library and runs it natively, without Coq.
#
#   tools/extraction/build_lib.sh OUTDIR
set -e
OUT="$1"
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
mkdir -p "$OUT"
{
  echo 'Require Import List String ZArith NArith QArith.'
  echo 'Require Import FiniteSet Values TuplesImpl GenericInstance SqlSyntax SqlFull SqlFullSyntax Dialects'
  echo '        PostgreSQL MySQL SQLite OceanBase MariaDB TiDB Percona PolarDB SpecRunner ResultText.'
  echo 'Definition dialect_named (s : string) : option vsem :='
  echo '  match s with'
  echo '  | "PostgreSQL" => Some PostgreSQL.PostgreSQL | "MySQL" => Some MySQL.MySQL | "SQLite" => Some SQLite.SQLite'
  echo '  | "OceanBase" | "OceanBaseMySQL" => Some OceanBaseMySQL | "OceanBaseOracle" => Some OceanBaseOracle'
  echo '  | "MariaDB" => Some MariaDB.MariaDB | "TiDB" => Some TiDB.TiDB | "Percona" => Some Percona.Percona'
  echo '  | "PolarDB" => Some PolarDB.PolarDB | _ => None'
  echo '  end.'
  echo 'Require Extraction. Require Import ExtrOcamlBasic ExtrOcamlNativeString.'
  printf 'Extraction "sqlfs_lib.ml" run_rows result_text diagnose dialect_named Z.add Z.mul Z.opp %s.\n' "$(tr '\n' ' ' < "$HERE/vocab.txt")"
} > "$OUT/ExtractLib.v"
cd "$OUT"
coqc -R "$ROOT/src" SQLFS ExtractLib.v > extract.log 2>&1
python3 "$HERE/fix_weak.py" sqlfs_lib.ml
rm -f sqlfs_lib.mli
cp "$HERE/prelude.ml" .
ulimit -s unlimited
ocamlopt -c sqlfs_lib.ml
ocamlopt -c prelude.ml
echo "library built in $OUT"
