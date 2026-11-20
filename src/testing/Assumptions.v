(** * The assumptions of the main results (TODO 6.7)

    Each result is closed under the global context (no axiom): CI checks the output of this file
    ([tools/check_hygiene.py] fails on [Axioms:]). *)
Require Import SqlFullFacts FreshAttr Versions Oracles.
Print Assumptions SqlFullFacts.order_by_nothing.
Print Assumptions SqlFullFacts.inner_join_spec.
Print Assumptions SqlFullFacts.inner_join_where.
Print Assumptions SqlFullFacts.union_all_comm.
Print Assumptions SqlFullFacts.union_all_assoc.
Print Assumptions FreshAttr.fresh_attr_is_fresh.
Print Assumptions Versions.at_version_sub.
Print Assumptions Oracles.tlp_partition.
Print Assumptions Oracles.tlp_sum.
Print Assumptions Oracles.norec.
Print Assumptions SqlFullFacts.dedup_idem.
Print Assumptions SqlFullFacts.cube_sets_length.
Print Assumptions SqlFullFacts.rollup_sets_length.
Print Assumptions SqlFullFacts.frame_running.
Print Assumptions SqlFullFacts.frame_whole_partition.
