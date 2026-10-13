# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.convergence_tools-a1.slice_majorant-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.convergence_tools-a1.slice_majorant-a1.monotone_majorant-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 4-7 and 9 of the parent proof of `cbr_slice_mass_majorant` (MM): "Bound at differentiability points", "Exceptional null set", "Definition and measurability of g", "The a.e. bound" and "Fatou". The strip masses S_j(t, h) are replaced here by their upper bounds ofReal(F_j(t) − F_j(t − h)). This is the integrated form of Simon Ch. 6, 4.9-4.10 and the sentence between them (book/chapter-06.txt lines 1356-1377). It is stated as a sequence (liminf over j, Fatou's lemma) because Remark 8.3(1) needs that form (lines 2311-2316, "for some subsequence {j'}").

The proof uses two sibling results:
- cbr_smm_liminf_left_slope_le_deriv: for every H : ℝ → ℝ differentiable at t, liminf_{h→0⁺} ofReal(h⁻¹)·ofReal(H(t) − H(t − h)) ≤ ofReal(deriv H t).
- cbr_smm_lintegral_ofReal_deriv_le: for every monotone H : ℝ → ℝ and all a, b, ∫⁻_{(a,b)} ofReal(deriv H) ≤ ofReal(H(b) − H(a)).
Values lie in [0, ∞], L is finite, and ofReal := ENNReal.ofReal.

1. Densities. For j ∈ ℕ put d_j(t) := ofReal(deriv F_j t). For every F_j, the function deriv F_j : ℝ → ℝ is Borel measurable (measurable_deriv), so d_j is measurable (Measurable.ennreal_ofReal).

2. Definition and measurability of g. Put g(t) := L · liminf_{j→∞} d_j(t). The pointwise liminf of the measurable sequence (d_j) is measurable (Measurable.liminf), and multiplying by the constant L keeps it measurable (Measurable.const_mul). So g is measurable.

3. Exceptional null set. Each F_j is monotone, hence differentiable at Lebesgue-a.e. t by Lebesgue's theorem (Monotone.ae_differentiableAt). Since ℕ is countable, for a.e. t every F_j is differentiable at t (ae_all_iff).

4. The a.e. bound. Let t be in the full-measure set of step 3 with t ∈ (a, b), and let j ∈ ℕ. The sibling cbr_smm_liminf_left_slope_le_deriv, applied to F_j at t, gives liminf_{h→0⁺} ofReal(h⁻¹)·ofReal(F_j(t) − F_j(t − h)) ≤ d_j(t). Multiplication by L is monotone on [0, ∞] (in this Mathlib, mul_le_mul_right h L : L * x ≤ L * y for h : x ≤ y; gcongr also works). With the hypothesis this gives Z_j(t) ≤ L · d_j(t) for every j. Therefore
liminf_j Z_j(t) ≤ liminf_j (L · d_j(t)) = L · liminf_j d_j(t) = g(t).
The inequality is liminf_le_liminf, applied to an inequality that holds everywhere and hence eventually; its boundedness side conditions are automatic in the complete lattice [0, ∞]. The equality is ENNReal.liminf_const_mul_of_ne_top with L ≠ ∞ (ENNReal.coe_ne_top) on the nontrivial filter atTop. This proves ∀ᵐ t, t ∈ (a, b) → liminf_j Z_j(t) ≤ g(t).

5. Integral bound. Integrate over (a, b), i.e. with respect to Lebesgue measure restricted to (a, b).
(i) ∫⁻_{(a,b)} g = L · ∫⁻_{(a,b)} liminf_j d_j, by lintegral_const_mul and the measurability of liminf_j d_j from step 2.
(ii) This is at most L · liminf_j ∫⁻_{(a,b)} d_j, by Fatou's lemma (lintegral_liminf_le for the measurable d_j) and monotonicity of multiplication by L.
(iii) For each j, ∫⁻_{(a,b)} d_j ≤ ofReal(F_j(b) − F_j(a)), by the sibling cbr_smm_lintegral_ofReal_deriv_le applied to the monotone F_j. With liminf_le_liminf and monotonicity of multiplication by L, the bound in (ii) is at most L · liminf_j ofReal(F_j(b) − F_j(a)).

6. Conclusion. Steps 2, 4 and 5 show that g is measurable, dominates liminf_j Z_j almost everywhere on (a, b), and satisfies the integral bound. This proves the statement. ∎

## Key steps

1. d_j := ofReal ∘ deriv F_j is measurable (measurable_deriv), and so is g := L · liminf_j d_j (Measurable.liminf, Measurable.const_mul).
2. For a.e. t, every F_j is differentiable at t (Monotone.ae_differentiableAt, ae_all_iff).
3. At such t ∈ (a, b), the left_slope sibling gives Z_j(t) ≤ L·d_j(t), so liminf_j Z_j(t) ≤ L·liminf_j d_j(t) = g(t) (ENNReal.liminf_const_mul_of_ne_top).
4. ∫⁻ g = L·∫⁻ liminf_j d_j ≤ L·liminf_j ∫⁻ d_j (lintegral_const_mul; Fatou, lintegral_liminf_le) ≤ L·liminf_j ofReal(F_j(b) − F_j(a)) (lintegral_deriv sibling).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `grep -rn in snapshot mathlib/Mathlib: 'theorem Monotone.ae_differentiableAt', 'theorem Monotone.ae_hasDerivAt', 'theorem measurable_deriv', 'theorem lintegral_liminf_le', liminf_const_mul, 'theorem measure_inter_add_sdiff', 'theorem HasDerivAt.tendsto_slope_zero_left', 'theorem Filter.Tendsto.liminf_eq', 'theorem Measurable.liminf', 'theorem ae_all_iff', 'theorem withDensity_apply_le', 'theorem withDensity_rnDeriv_le', 'theorem measure_Ioo', 'theorem lintegral_const_mul'; grep mul_le_mul_left/mul_le_mul_right in Algebra/Order/Monoid/Unbundled/Basic.lean`
- `lake env lean /tmp/mm-decomp-7c1/lean/Avail.lean: #check of 40 cited lemmas after import GMT.Ch07.Submission. MonotoneOn.intervalIntegrable_deriv and tendsto_neg_nhdsGT_zero are unknown; mul_le_mul_left' is unknown, and this Mathlib's mul_le_mul_right : b ≤ c → a * b ≤ a * c`
- `python3 scan of dag.json (983, later 1033 nodes) for lean_names and statements with deriv / Monotone / 𝓝[>] 0 / liminf / ∫⁻. Found accepted cmcs_smi_lintegral_ofReal_deriv_le (identical type to the lintegral_deriv child), cmcs_smi_lintegral_left_dini_le, cmcs_smi_lintegral_left_density_le and cmcs_smp_liminf_bound, plus cmcs_slice_mass_integral (comparing; needs MeasurableSet W). No cbr_smm_* names. Cross-parent lean_name reuse in 2353 earlier proposals: 0. Duplicated statements under fresh names: 54`
- `git show 6efe397f1 (accepted Submission.cmcs_smi_lintegral_ofReal_deriv_le: Stieltjes/rnDeriv route, no imports, no helpers) and git show 2168e6089 (accepted cmcs_smi_lintegral_left_dini_le: tendsto_neg_nhdsGT with HasDerivAt.tendsto_slope_zero_left)`
- `git grep -l cbr_smm_ over all 4223 refs -- 'GMT/*.lean': no match (control: cmcs_smi_lintegral_ofReal_deriv_le is found in 19 refs). grep -rl cbr_smm_ in the simongmt package and the snapshot project: no match`
- `verifier/gmt-compare.py contract_scope and child_modules. Replayed scope: open Filter Function Set MeasureTheory Metric; open scoped ENNReal Topology; namespace GMT.Ch07; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (...); noncomputable section; end. verifier/lean_contract.py validate_lean_statement on the four child strings and the parent: all pass`
- `lake env lean /tmp/mm-decomp-7c1/lean/Challenges.lean, Assembly.lean and Proofs.lean: all exit 0. asm_core, asm_parent, asm_total and NodeSolution0-4 depend only on propext, Classical.choice and Quot.sound`
- `python3 regex search of other nodes' decomposition-audit-v1.json and parent-supplied-natural-proof.md for the import policy: 'leaf_verification.check_source_delta forbids new declarations and imports in leaf proofs'`
- `sed -n 1350,1380p and 2310,2350p book/chapter-06.txt (4.9, the sentence before 4.10, 4.10, Remark 8.3(1), 8.2 (2))`
- `independent reviewer subagent over /tmp/mm-decomp-7c1/draft/subproblems.json and the three Lean files. VERDICT: ACCEPT; it also compiled verifier-generated NodeChallenge/NodeSolution files against a copy of Submission.lean with the theorems inserted before main_theorem. Its non-blocking notes were applied`
- `WebSearch: increasing function derivative integrable f(b) - f(a) Lebesgue theorem (mathonline.wikidot.com, 'The Lebesgue Integral of the Derivative of an Increasing Function')`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/PROBLEM.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-9047af112c/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-9047af112c/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-9047af112c/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0d752561a6/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Stieltjes.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/mm-decomp-7c1/lean/Avail.lean`
- `/tmp/mm-decomp-7c1/lean/Full.lean`
- `/tmp/mm-decomp-7c1/lean/Challenges.lean`
- `/tmp/mm-decomp-7c1/lean/Assembly.lean`
- `/tmp/mm-decomp-7c1/lean/Proofs.lean`
- `/tmp/mm-decomp-7c1/draft/subproblems.json`

The snapshot contract (project b4d606db1, Mathlib 25730c7c) is identical to the workspace Contract.lean and Submission.lean. Every lemma cited in the four child proofs exists in the frozen import closure. The supplied proof's MonotoneOn.intervalIntegrable_deriv and MonotoneOn.intervalIntegral_deriv_mem_uIcc do not: they live in Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean, which is not imported, and leaf proofs may not add imports. The import-free route uses Monotone.stieltjesFunction, StieltjesFunction.measure_Ioo, Monotone.ae_hasDerivAt, withDensity_apply_le and Measure.withDensity_rnDeriv_le. It is the route of the accepted Submission.cmcs_smi_lintegral_ofReal_deriv_le (commit 6efe397f1), whose type is identical to the lintegral_deriv child. In this Mathlib mul_le_mul_left' is gone; mul_le_mul_right : b ≤ c → a * b ≤ a * c is the left-multiplication monotonicity lemma. tendsto_neg_nhdsGT handles the substitution h ↦ −h. No accepted DAG node proves MM itself. cmcs_slice_mass_integral requires MeasurableSet W and a single measure, so it does not apply. The proposed cbr_smm_* names are unused everywhere. The four exact child types elaborate in the comparator scope and are fully proved without new imports or helpers, and they imply the frozen parent type with standard axioms only. Book anchors in chapter-06.txt: lines 1356-1377 (4.9-4.10), 2311-2316 (Remark 8.3(1)) and 2345-2347 (8.2 (2)).
