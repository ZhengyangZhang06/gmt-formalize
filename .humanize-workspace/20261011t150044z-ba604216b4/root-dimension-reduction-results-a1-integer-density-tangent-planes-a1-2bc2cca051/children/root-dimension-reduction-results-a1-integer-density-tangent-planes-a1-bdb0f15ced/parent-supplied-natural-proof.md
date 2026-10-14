# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_count-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_count-a1.fibre_pointwise-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent steps 1, 3 and 4 at a single point p. Notation as in the statement; put t := p₁, α := p₂ and x₀ := x_Q(p) = t(cos α·a + sin α·e).
1. (Ranges.) From |t − 1| < s ≤ 1/4 we get t > 1 − s ≥ 3/4 > 0. From |α| < s ≤ 1/4 and Real.pi ≥ 2 (`Real.two_le_pi`) we get |α| < 1/4 < 1 ≤ Real.pi/2.
2. (Planar facts.) Apply sibling `Submission.idtp_cse_fc_planar_fibre_geometry` to Q, a, e. Part (a): for every subspace T (p_T := T.starProjection) and every x, |p_T(Ax)| ≤ |πx| ≤ |x|. With t > 0 and |α| < Real.pi/2 (step 1), part (b) gives ⟨x₀, a⟩ > 0, |x₀| = t, f(x₀) = α, πx₀ = x₀ and |π(Ax₀)| = t. Part (c): every x with ⟨x, a⟩ > 0, |x| = t, f(x) = α and x ≠ x₀ has |πx| < t.
3. (Fibre points.) Let x ∈ X(p). Then x ∈ M; x ∈ Z_s, in particular ⟨x, a⟩ > 0; and F̃(x) = p, i.e. |x| = t and f(x) = α. By (a) with T := T_x: w(x) ≤ |πx| ≤ |x| = t.
4. (Claim m ≤ N(p).) Apply sibling `Submission.idtp_cse_fc_tsum_count_arith` with ι := X(p) (the subtype), θ(x) := R.mult x, w as above, t and m. Its hypotheses hold: t > 0 (step 1); w(x) ≤ t for all x ∈ X(p) (step 3); and Σ'_{x ∈ X(p)} θ(x)·ofReal(w(x)) = H(p) = ofReal(m·t) (hypothesis). Its first conclusion is m ≤ N(p).
5. (x₀ lies in the fibre.) Assume x₀ ∈ M, θ(x₀) = k and T_{x₀} = Q. By (b): ⟨x₀, a⟩ > 0; ||x₀| − 1| = |t − 1| < s; |f(x₀)| = |α| < s; and |x₀ − πx₀| = |0| = 0 < s·t = s|x₀| since s, t > 0. So x₀ ∈ Z_s. Also F̃(x₀) = (|x₀|, f(x₀)) = (t, α) = p. Hence x₀ ∈ X(p); let i₀ be the corresponding element of the subtype.
6. (Hypotheses of the second conclusion.) θ(i₀) = k. Next, w(i₀) = |p_{T_{x₀}}(Ax₀)| = |π(Ax₀)| = t, using T_{x₀} = Q and (b). Every i ∈ X(p) lies in M, so θ(i) ≥ 1 (`R.mult_pos`). If i ≠ i₀ in the subtype, then i ≠ x₀ as points of ℝ^P. By step 3, ⟨i, a⟩ > 0, |i| = t and f(i) = α, so (c) gives |πi| < t, and therefore w(i) ≤ |πi| < t by (a).
7. (Conclusion.) The second conclusion of `Submission.idtp_cse_fc_tsum_count_arith` (with i₀ and k) gives k ≤ m, and k < m ⟹ m + 1 ≤ N(p). Together with step 4 this proves the statement. ∎

## Key steps

1. |p₁ − 1| < s ≤ 1/4 and |p₂| < s give t = p₁ > 0 and |α| = |p₂| < Real.pi/2.
2. Fibre points x satisfy |x| = t, f(x) = α and ⟨x,a⟩ > 0, so w(x) ≤ |πx| ≤ t (planar_geometry (a)).
3. count_arith (i) with H(p) = ofReal(m t) gives m ≤ N(p).
4. If x_Q(p) ∈ M, θ = k and T = Q, then x_Q(p) ∈ Z_s ∩ F̃⁻¹{p} with w = t, and every other fibre point has w < t (planar_geometry (b), (c)).
5. count_arith (ii) gives k ≤ m, and k < m ⟹ m + 1 ≤ N(p).

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
