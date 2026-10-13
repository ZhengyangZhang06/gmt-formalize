# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_count-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_count-a1.count_arith-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent steps 1(iv), 3 and 4, abstracted from the fibre. Notation: τ := ofReal(t), H := Σ'_i θ(i)·ofReal(w(i)) and N := Σ'_i θ(i), all in [0, ∞].
1. (Normalization.) Since t > 0, τ ∈ (0, ∞). Since m ≥ 0, ofReal(m·t) = ofReal(m)·ofReal(t) = m·τ. So the hypothesis reads H = m·τ.
2. (Claim (i).) For every i, w(i) ≤ t gives ofReal(w(i)) ≤ τ, hence θ(i)·ofReal(w(i)) ≤ θ(i)·τ. Summing (tsums in [0, ∞] are monotone) and pulling out the constant factor (`ENNReal.tsum_mul_right`) gives H ≤ N·τ. Thus m·τ ≤ N·τ. Cancelling the factor τ ∈ (0, ∞) (`ENNReal.mul_le_mul_iff_left`) gives m ≤ N.
3. (k ≤ m.) Let i₀ and k satisfy the hypotheses of (ii). The single term at i₀ is at most the whole sum (`ENNReal.le_tsum`): k·τ = θ(i₀)·ofReal(w(i₀)) ≤ H = m·τ. Cancelling τ gives k ≤ m in [0, ∞], hence in ℕ.
4. (k < m, infinite case.) Assume k < m. If N = ∞, then m + 1 ≤ N trivially.
5. (k < m, ι is finite.) Otherwise N < ∞. Since θ(i) ≥ 1 for every i, the set {i : 1 ≤ θ(i)} is all of ι, and a [0, ∞]-valued sum with finite value has only finitely many terms ≥ 1 (`ENNReal.finite_const_le_of_tsum_ne_top`). So ι is finite and both tsums are finite sums.
6. (Splitting off i₀.) Let E := ι ∖ {i₀}, n := Σ_{i∈E} θ(i) ∈ ℕ and H' := Σ_{i∈E} θ(i)·ofReal(w(i)). Then N = θ(i₀) + n = k + n and H = θ(i₀)·ofReal(w(i₀)) + H' = k·τ + H'. By step 1, k·τ + H' = m·τ.
7. (E is nonempty.) If E = ∅, then H' = 0, so k·τ = m·τ, and cancelling τ ∈ (0, ∞) gives k = m, contradicting k < m. Hence E ≠ ∅.
8. (Strict comparison.) For i ∈ E we have i ≠ i₀, so w(i) < t, and since t > 0 this gives ofReal(w(i)) < τ. Moreover θ(i) ≥ 1 is a nonzero finite factor, so θ(i)·ofReal(w(i)) < θ(i)·τ. Summing these strict inequalities over the nonempty finite set E (`ENNReal.sum_lt_sum_of_nonempty`) gives H' < n·τ.
9. (Conclusion.) m·τ = k·τ + H' < k·τ + n·τ = (k + n)·τ, using k·τ < ∞. Cancelling τ ∈ (0, ∞) gives m < k + n in ℕ, hence m + 1 ≤ k + n = N. ∎

## Key steps

1. Termwise H ≤ N·ofReal(t), and ofReal(m t) = m·ofReal(t), so m ≤ N.
2. The i₀ term gives k·ofReal(t) ≤ H = m·ofReal(t), so k ≤ m.
3. If N < ∞ then, because θ ≥ 1, ι is finite; splitting off i₀ gives N = k + n and k·τ + H' = m·τ.
4. k < m forces E = ι ∖ {i₀} ≠ ∅, and each remaining term is strictly below θ(i)·τ, so H' < n·τ.
5. Then m·τ < (k + n)·τ, so m < k + n, i.e. m + 1 ≤ N.

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
