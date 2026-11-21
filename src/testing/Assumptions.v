(** * The assumptions of the main results (TODO 6.7)

    Each result is closed under the global context (no axiom): CI checks the output of this file
    ([tools/check_hygiene.py] fails on [Axioms:]). *)
Require Import SqlFullFacts FreshAttr Versions Oracles SqlRelate SqlGroupFacts SqlScoping SqlSorts SqlRelateSelect SqlRelateAlg.
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
Print Assumptions SqlFullFacts.frame_rows_bounded.
Print Assumptions SqlFullFacts.frame_current_row.
Print Assumptions SqlFullFacts.frame_to_end.
Print Assumptions SqlFullFacts.frame_exclude_no_others.
Print Assumptions SqlFullFacts.frame_range_whole.
Print Assumptions SqlFullFacts.frame_groups_whole.
Print Assumptions SqlFullFacts.frame_range_current_peers.
Print Assumptions SqlFullFacts.frame_groups_current_peers.
Print Assumptions SqlFullFacts.dedup_on_rec.
Print Assumptions SqlFullFacts.rec_loop_fuel.
Print Assumptions SqlRelate.sql_full_agree.
Print Assumptions SqlFullFacts.msort_stable_sort.
Print Assumptions SqlGroupFacts.group_on_spec.
Print Assumptions SqlFullFacts.frame_range_zero_offsets.
Print Assumptions SqlFullFacts.tlp_join.
Print Assumptions SqlFullFacts.norec_join.
Print Assumptions SqlFullFacts.pqs_join.
Print Assumptions SqlFullFacts.containment_and.
Print Assumptions SqlFullFacts.containment_or.
Print Assumptions SqlFullFacts.containment_distinct.
Print Assumptions Oracles.max_filter_le.
Print Assumptions Oracles.min_filter_ge.
Print Assumptions Oracles.sum_filter_le.
Print Assumptions SqlScoping.scope_e.
Print Assumptions SqlScoping.scope_c.
Print Assumptions SqlScoping.wf_set_op.
Print Assumptions SqlGroupFacts.rollup_groupings.
Print Assumptions Versions.version_eval.
Print Assumptions Versions.version_accepted.
Print Assumptions SqlGroupFacts.rollup_as_grouping_sets.
Print Assumptions SqlFull.eval_select.
Print Assumptions SqlSorts.eval_sorts.
Print Assumptions SqlRelateSelect.sql_full_agree2.
Print Assumptions SqlRelateAlg.sql_full_alg.
Print Assumptions SqlRelateSelect.select_agree_grp.
