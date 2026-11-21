# Legacy experiments

Files of the original development which are not part of the build (`src/_CoqProject` does not list them) and are
kept for reference. They compile with `coqc -R . SQLFS testing/legacy/<file>.v` from `src`, after `make`.

- `Test_NaturalJoin.v`, `Test_SqlExt.v`: examples for `SqlExt.v` / `SqlAlgebraExt.v` (natural joins); they print
  their results and check nothing.
- `Pokus2_Radim.v`: a scratch file; it contains an `Admitted` (an ordering on `N` used to try `Fset`), which is why
  it must stay out of the build (`tools/check_hygiene.py` checks the files of `_CoqProject`).
