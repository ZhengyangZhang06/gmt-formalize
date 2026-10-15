# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_count-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_count-a1.jacobian_upper-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent step 6 (second half). Notation as in the statement: w(x) := |p_{T_x}(Ax)|, Z' := Z(s, s'), c := ofReal(1/(1 − 2s')).
1. (Reduction.) ∫⁻_{Z'} c dμ = c·μ(Z') (`setLIntegral_const`). Since the constant c is measurable, `setLIntegral_mono_ae` reduces the claim to a pointwise statement: for μ-a.e. x, if x ∈ Z' then ofReal(J(x)) ≤ c. No measurability of Z' or J is needed.
2. (Good points.) By hypothesis μ-a.e. x lies in S. Fix x ∈ S ∩ Z'. Then ⟨x, a⟩ > 0, ||x| − 1| < s', |f(x)| < s' and |x − πx| < s|x|, so the localization hypothesis gives |x − πx| < (s'/4)|x|. Also |x| > 1 − s', from ||x| − 1| < s'.
3. (Lower bound for |πx|.) By the triangle inequality, |x| = |πx + (x − πx)| ≤ |πx| + |x − πx|, so |πx| ≥ |x| − |x − πx| > (1 − s'/4)|x|. Since 0 < s' ≤ 1/4, we have 1 − s'/4 > 0, and |x| > 1 − s' gives (1 − s'/4)|x| > (1 − s'/4)(1 − s') = 1 − 2s' + (3s'/4 + s'²/4) ≥ 1 − 2s'. Hence |πx| > 1 − 2s' ≥ 1/2 > 0.
4. (Bound for J.) By sibling `Submission.idtp_cse_fc_planar_fibre_geometry`, part (a), with T := T_x: w(x) ≤ |πx|. Since |πx| > 0, J(x) = w(x)/|πx|² ≤ |πx|/|πx|² = 1/|πx| ≤ 1/(1 − 2s'). The last step uses step 3 and 1 − 2s' > 0. As ofReal is monotone, ofReal(J(x)) ≤ c.
5. (Conclusion.) By steps 1–4, ∫⁻_{Z'} ofReal(J) dμ ≤ ∫⁻_{Z'} c dμ = ofReal(1/(1 − 2s'))·μ(Z'). ∎

## Key steps

1. Reduce to the a.e. pointwise bound ofReal(J) ≤ ofReal(1/(1 − 2s')) on Z(s, s') (setLIntegral_mono_ae, setLIntegral_const).
2. For x ∈ S ∩ Z(s, s'), localization gives |x − πx| < (s'/4)|x|, so |πx| > (1 − s'/4)(1 − s') ≥ 1 − 2s' > 0.
3. w ≤ |πx| (planar_geometry (a)) gives J ≤ 1/|πx| ≤ 1/(1 − 2s').

## Reference use

### local-project

Queries:
- `python3 scan of dag.json (key 'nodes'): lean_statement/status of fibre_count-a1 and its siblings stationary_radial-a1, fibre_area-a1, sector_points-a1, flux_density-a1, and of the accepted cross-branch lemma imrep_represents_support_eq_inter_measure_support`
- `python3 scan of dag.json lean_name for idtp_cse_fc_planar_fibre_geometry|idtp_cse_fc_tsum_count_arith|idtp_cse_fc_fibre_pointwise|idtp_cse_fc_square_lintegral_lower|idtp_cse_fc_jacobian_upper (no match); grep -rl idtp_cse_fc run dir and nodes/*/decomposition-v*.json (no match); rg -c 'idtp_cse_' local-references/123e8435b4a2469b/project (no match)`
- `python3 scan of accepted DAG lemmas for reusable planar/arctan/starProjection or tsum-counting facts (none applicable); search for an a.e.-support lemma (only imrep_represents_support_eq_inter_measure_support / dor_imrep_massOn_eq_measure_and_support, accepted)`
- `rg -n 'theorem (eq_starProjection_of_mem_of_inner_eq_zero|starProjection_eq_self_iff|mem_iff_norm_starProjection|norm_starProjection_apply_le|finrank_span_eq_card|eq_of_le_of_finrank_eq|sum_lt_sum_of_nonempty|finite_const_le_of_tsum_ne_top|two_le_pi|arctan_tan|cos_arctan|sin_arctan|setLIntegral_mono_ae|setLIntegral_const|lintegral_indicator_le|ae_restrict_neBot)' local-references/123e8435b4a2469b/mathlib`
- `rg -n 'support_mem_ae|mem_span_range_iff_exists_fun|lintegral_add_left|lintegral_indicator_const|volume_Ioo|prod_prod|volume_eq_prod' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -rn 'mul_lt_mul_right|mul_le_mul_iff_left|mul_lt_mul_iff_left|mul_left_inj' .lake/packages/mathlib/Mathlib/Basic/ENNReal/Operations.lean; grep pi_gt_three (only in Mathlib/Analysis/Real/Pi/Bounds.lean, not imported by the contract)`
- `diff GMT/Ch07/Submission.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean (identical)`
- `lake env lean /tmp/fc_split_check/Stmts.lean (5 child types elaborate, sorry warnings only)`
- `lake env lean /tmp/fc_split_check/Final.lean (5 children proved: axioms propext, Classical.choice, Quot.sound; parent idtp_cse_fibre_count_bound proved from the children plus verbatim stubs of the 4 siblings and the accepted support lemma)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-2bc2cca051/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-2bc2cca051/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-18ac87081c/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/BigOperators.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Arctan.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Analysis/Real/Pi/Bounds.lean`
- `/tmp/fc_split_check/Stmts.lean`
- `/tmp/fc_split_check/Final.lean`

Pins and contract match. The workspace GMT/Ch07/Submission.lean is byte-identical to the snapshot project copy (project b4d606db1, mathlib 25730c7c). All Mathlib names cited in the child proofs exist at this pin. Real.pi_gt_three is not reachable from the contract imports, so Real.two_le_pi is used. mul_le_mul_right' is absent, so gcongr is used. No accepted DAG lemma already provides the planar projection/arctan facts, the ENNReal fibre-counting lemma, the rectangle lower bound or the Jacobian bound, so the 5 children are new. Their idtp_cse_fc_* names occur nowhere in dag.json, nodes/, GMT/ or the snapshot. The only cross-branch lemma used is the accepted Submission.imrep_represents_support_eq_inter_measure_support, in the parent assembly. All 5 child types elaborate in the frozen context and were fully proved with standard axioms only. The selected parent type was compiled from these children plus verbatim stubs of its 4 sibling prerequisites and the accepted support lemma.
