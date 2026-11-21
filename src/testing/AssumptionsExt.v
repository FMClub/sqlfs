(** * The assumptions of the congruence and of the refinement between dialects (TODO 6.2, 6.4, 6.7)

    These results (and the scoping of whole queries) rewrite under the binders of the evaluation with functional extensionality, the only axiom
    which they use: CI checks it ([tools/check_axioms.py]). *)
Require Import SqlCongruence Refinement SqlScopeQuery.
Print Assumptions SqlCongruence.eval_congruence.
Print Assumptions Refinement.dialect_refinement.
Print Assumptions Refinement.percona_refines_mysql.
Print Assumptions Refinement.percona_known.
Print Assumptions SqlScopeQuery.scope_query.
Print Assumptions SqlScopeQuery.cols_atts.
