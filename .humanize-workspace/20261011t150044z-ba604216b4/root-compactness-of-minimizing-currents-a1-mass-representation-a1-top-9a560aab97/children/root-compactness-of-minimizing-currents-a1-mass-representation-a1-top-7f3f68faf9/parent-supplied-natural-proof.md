# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.top_dim_null-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.top_dim_null-a1.null_of_average_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, steps 5(i) and 6 (dominated convergence along smooth cut-offs, then the error term tends to 0). The parent's step-3 bound rΛ + λ(B_r)⁻¹‖h‖₁∫a is abstracted to ε + C∫a. The cut-offs come from the sibling lemma cmr_tdn_null_set_cutoffs.
Notation: λ := volume on ℝⁿ = Euclid n, and F(a) := ∫ h(x)a(q x) dν(x).
1. (Cut-offs.) Fix a compact K with λ(K) = 0. The sibling lemma cmr_tdn_null_set_cutoffs gives functions a_k : ℝⁿ → ℝ (k ∈ ℕ) with these properties:
 - each a_k is C^∞ with compact support and 0 ≤ a_k ≤ 1;
 - a_k = 1 on K for every k;
 - for every y ∉ K, a_k(y) = 0 for all large k;
 - ∫ a_k dλ → 0.
2. (The target integral.) K is compact in the Hausdorff space ℝⁿ, hence closed and Borel. Since q is measurable, E := q⁻¹(K) is measurable. Put I := ∫_E h dν. By integral_indicator, I = ∫ 1_E(x)h(x) dν(x).
3. (Dominated convergence.) Let F_k(x) := h(x)a_k(q x).
 - Each F_k is AE-strongly measurable: h is, and a_k ∘ q is measurable because a_k is continuous (being C^∞) and q is measurable.
 - Since 0 ≤ a_k ≤ 1, |F_k(x)| ≤ |h(x)|, and |h| is ν-integrable.
 - Pointwise convergence: if q x ∈ K, then F_k(x) = h(x) = 1_E(x)h(x) for every k. If q x ∉ K, then F_k(x) = 0 = 1_E(x)h(x) for all large k. Hence F_k(x) → 1_E(x)h(x) for every x.
 By dominated convergence (tendsto_integral_of_dominated_convergence with bound |h|), F(a_k) = ∫ F_k dν → I.
4. (ε-bound.) Fix ε > 0 and let C be given by the hypothesis. Every a_k is admissible, so |F(a_k)| ≤ ε + C∫ a_k dλ for every k. As k → ∞, the left side tends to |I| (continuity of |·|, Tendsto.abs) and the right side tends to ε + C·0 = ε. Limits preserve non-strict inequalities (le_of_tendsto_of_tendsto), so |I| ≤ ε.
5. (Conclusion.) |I| ≤ 0 + ε for every ε > 0, so |I| ≤ 0 (le_of_forall_pos_le_add). Hence |I| = 0 (abs_nonpos_iff), and ∫_{q⁻¹(K)} h dν = I = 0.

## Key steps

1. Take the cut-offs a_k of K from cmr_tdn_null_set_cutoffs.
2. q⁻¹(K) is measurable, and dominated convergence (majorant |h|) gives F(a_k) → ∫_{q⁻¹(K)} h dν.
3. For each ε > 0: |F(a_k)| ≤ ε + C∫a_k → ε, so |∫_{q⁻¹(K)} h dν| ≤ ε.
4. Since ε > 0 is arbitrary, the integral is 0.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical); git -C lake-packages-25730c7c/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d, matches manifest)`
- `rg -n 'lemma trace_smulRight|theorem integral_integral_swap|lemma intervalIntegral_integral_swap|theorem integral_eq_sub_of_hasDerivAt|theorem integral_mul_left_eq_self|structure ContDiffBump|theorem zero_of_le_dist|theorem one_of_mem_closedBall|theorem exists_contDiff_support_eq_eq_one_iff|theorem tendsto_measure_cthickening_of_isCompact|theorem closure_eq_iInter_cthickening|theorem tendsto_integral_of_dominated_convergence|theorem Integrable.mul_prod|theorem Integrable.integral_prod_left|theorem Integrable.prod_right_ae|lemma Integrable.comp_snd|theorem hasFDerivAt_comp_add_right|instance isFiniteMeasure_restrict_Ioc|theorem eLpNorm_le_eLpNorm_fderiv_one' local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean'`
- `lake env lean /tmp/tdn2/Scope.lean (#check of the cited lemmas and #synth HasContDiffBump (Euclid 3) after import GMT.Ch07.Submission in the replayed contract scope; eLpNorm_le_eLpNorm_fderiv_one reports unknown identifier)`
- `lake env lean /tmp/tdn2/Stmts.lean (four child types + frozen parent type; instance checks IsAddHaarMeasure, SFinite, IsAddLeftInvariant, IsAddRightInvariant, IsFiniteMeasureOnCompacts, IsOpenPosMeasure, BorelSpace, ProperSpace, HasContDiffBump on Euclid n; (⊤ : ℕ∞) coerces to smooth order ∞ ≠ ω; ∫ y, a y and volume K are volume on Euclid n by rfl)`
- `lake env lean /tmp/tdn2/Assembly.lean (parent_from_children, D_from_C, #print axioms)`
- `lake env lean /tmp/tdn2/A/A.lean /tmp/tdn2/B/B.lean /tmp/tdn2/C/C.lean /tmp/tdn2/C/S.lean /tmp/tdn2/E2E/EndToEnd.lean /tmp/tdn2/final/Recheck.lean (#print axioms)`
- `python3 scan of dag.json lean_name for cmr_tdn_directional_bound, cmr_tdn_ball_average_bound, cmr_tdn_null_set_cutoffs, cmr_tdn_null_of_average_bound (no hits among 739 nodes); grep -rn cmr_tdn GMT/ local-references/123e8435b4a2469b/project lake-packages-25730c7c/simongmt lake-packages-25730c7c/mathlib/Mathlib (no match)`
- `sed -n 1388,1552p and 1801,1920p /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py; grep -n 'def _existing_lean_name_problem' -A 40 runtime.py; sed -n 545,612p verifier/gmt-compare.py (child scope replay); read this node's decomposition-v1.json, decomposition-audit-v1.json, decomposition-review-receipt-v1.json, decomposition-scope-v1.json and its dag.json entry (status decomposing, attempt 2, children [])`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-top-9a560aab97/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-top-9a560aab97/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-top-9a560aab97/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/tdn2/Scope.lean`
- `/tmp/tdn2/Stmts.lean`
- `/tmp/tdn2/Assembly.lean`
- `/tmp/tdn2/A/A.lean`
- `/tmp/tdn2/B/B.lean`
- `/tmp/tdn2/C/C.lean`
- `/tmp/tdn2/C/S.lean`
- `/tmp/tdn2/E2E/EndToEnd.lean`
- `/tmp/tdn2/final/Recheck.lean`

Pinned sources. The manifest pins project b4d606db and mathlib 25730c7c, and the active lake mathlib is at 25730c7c. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

Import closure. Every lemma cited by the child proofs is in the import closure of GMT.Ch07.Submission, for example:
- trace_smulRight (LinearAlgebra/Trace.lean:272);
- integral_integral_swap and intervalIntegral_integral_swap (Integral/Prod.lean:478 and :483);
- integral_eq_sub_of_hasDerivAt (IntervalIntegral/FundThmCalculus.lean:1148);
- ContDiffBump with one_of_mem_closedBall and zero_of_le_dist (BumpFunction/Basic.lean:70, :137, :163);
- exists_contDiff_support_eq_eq_one_iff (Geometry/Manifold/PartitionOfUnity.lean:789);
- tendsto_measure_cthickening_of_isCompact (BorelSpace/Metric.lean:185);
- closure_eq_iInter_cthickening (Thickening.lean:511);
- tendsto_integral_of_dominated_convergence (DominatedConvergence.lean:57).
The Sobolev inequality (SobolevInequality.lean:439) is not in the closure, as the handoff states.

Names. No cmr_tdn_ name exists in the 739-node DAG or in the project, SimonGMT or Mathlib sources.

Lean checks, in the comparator's replayed child scope:
- all four child types elaborate, with the relevant volume, bump and smoothness instances verified;
- complete proofs of all four children check;
- an end-to-end proof of the byte-identical frozen parent type checks with axioms [propext, Classical.choice, Quot.sound] only.

Retry context. The node's attempt-1 split had the same structure and passed audit, but its children were never activated. The DAG shows attempt 2, no children and no feedback.
