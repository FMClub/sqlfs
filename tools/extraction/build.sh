#!/bin/sh
# The extracted interpreter (TODO 6.6): the semantics, the dialects and SpecRunner.diagnose are extracted to
# OCaml together with the conformance cases already compiled in src/testing/spec (tools/spec/run.sh), compiled
# with ocamlopt, and run: it prints the failing cases of each file, which must be those that vm_compute gives.
#
#   tools/extraction/build.sh DIALECT OUTDIR
set -e
D="$1"; OUT="$2"
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
mkdir -p "$OUT"
cd "$ROOT/src"
MODS=$(ls testing/spec/Spec_*.vo | sed 's#.*/##;s#\.vo$##')
{
  echo 'Require Import List String SpecRunner Dialects PostgreSQL MySQL SQLite OceanBase MariaDB TiDB.'
  echo 'Import ListNotations. Open Scope string_scope.'
  for m in $MODS; do echo "Require SQLFS.testing.spec.$m."; done
  echo 'Require Extraction. Require Import ExtrOcamlBasic ExtrOcamlNativeString.'
  printf 'Definition all_cases := ['
  sep=''
  for m in $MODS; do n=$(echo $m | sed 's/^Spec_//'); printf '%s("%s", SQLFS.testing.spec.%s.cases_%s)' "$sep" "$n" "$m" "$n"; sep='; '; done
  echo '].'
  echo "Definition run_all := map (fun p => (fst p, diagnose $D (snd p))) all_cases."
  echo 'Extraction "sqlfs_cases.ml" run_all.'
} > "$OUT/ExtractCases.v"
coqc -R . SQLFS "$OUT/ExtractCases.v" > "$OUT/extract.log" 2>&1
mv sqlfs_cases.ml "$OUT/"; rm -f sqlfs_cases.mli
python3 "$ROOT/tools/extraction/fix_weak.py" "$OUT/sqlfs_cases.ml"
cat > "$OUT/driver.ml" <<'ML'
(* the cases are evaluated when the module Sqlfs_cases is initialised; this prints the failures *)
let () =
  List.iter (fun (name, fails) ->
      Printf.printf "== %s: %d failing\n" name (List.length fails);
      List.iter (fun s -> Printf.printf "  %s\n" s) fails) Sqlfs_cases.run_all
ML
cd "$OUT"
# the extracted terms are deep: the compiler and the program need a large stack
ulimit -s unlimited
ocamlopt sqlfs_cases.ml driver.ml -o run_cases
./run_cases
