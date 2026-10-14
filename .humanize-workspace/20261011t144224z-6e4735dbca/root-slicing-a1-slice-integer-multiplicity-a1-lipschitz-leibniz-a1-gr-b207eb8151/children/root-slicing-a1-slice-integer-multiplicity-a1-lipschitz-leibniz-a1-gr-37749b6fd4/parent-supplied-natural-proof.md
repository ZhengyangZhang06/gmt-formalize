# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.gradient_weak_star-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.gradient_weak_star-a1.smooth_tendsto-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝⁿ = Eucl n; Lⁿ = volume; Df(w) = fderiv ℝ f w (0 where f is not differentiable). Integrals are Bochner integrals for Lⁿ. In Lean the sequence u_k is `ug k`. Source: parent proof, step 5.
1. (Weak divergence of b.) Apply the sibling theorem `slicing_im_ll_gws_lipschitz_ibp` to n, Ω and b; its hypotheses hold because Ω is open, b is C¹ with compact support, and tsupport b ⊆ Ω. It gives g : ℝⁿ → ℝ, Lⁿ-integrable, with the following property: for every L ≥ 0 and every f that is L-Lipschitz on Ω, f·g is integrable on Ω and ∫_Ω Df(w)(b(w)) dw = −∫_Ω f(w)g(w) dw. Apply this with (L, f) = (C, u) and with (L, f) = (C, u_k) for every k; all of these functions are C-Lipschitz on Ω by hypothesis.
2. (Difference formula.) For every k, u·g and u_k·g are integrable on Ω by step 1. By step 1 and linearity of the integral (`integral_sub`), ∫_Ω Du_k(w)(b(w)) dw − ∫_Ω Du(w)(b(w)) dw = −∫_Ω u_k g + ∫_Ω u g = ∫_Ω (u(w) − u_k(w))·g(w) dw.
3. (Choice of N.) Put A := ∫_Ω |g(w)| dw ≥ 0, which is finite because g is integrable and hence integrable on Ω. Let ε > 0 and η := ε/(2(A + 1)) > 0. Since u_k → u uniformly on Ω (`Metric.tendstoUniformlyOn_iff`), there is N ∈ ℕ with |u(w) − u_k(w)| < η for all k ≥ N and all w ∈ Ω.
4. (Estimate.) Let k ≥ N. For all w ∈ Ω, |(u(w) − u_k(w))·g(w)| ≤ η|g(w)|, and η|g| is integrable on Ω. Hence |∫_Ω (u − u_k) g| ≤ ∫_Ω η|g| = ηA = εA/(2(A + 1)) < ε (`norm_integral_le_of_norm_le`, `integral_const_mul`).
5. (Conclusion.) By steps 2 and 4, |∫_Ω Du_k(w)(b(w)) dw − ∫_Ω Du(w)(b(w)) dw| < ε for all k ≥ N. Since ε > 0 was arbitrary, ∫_Ω Du_k(b) → ∫_Ω Du(b) as k → ∞ (`Metric.tendsto_atTop`). ∎

## Key steps

1. The sibling slicing_im_ll_gws_lipschitz_ibp gives one integrable g with f·g integrable on Ω and ∫_Ω Df(b) = −∫_Ω f g, for f = u and for f = u_k.
2. ∫_Ω Du_k(b) − ∫_Ω Du(b) = ∫_Ω (u − u_k)·g.
3. By uniform convergence, |u − u_k| < η on Ω for k ≥ N, so |∫_Ω (u − u_k) g| ≤ η∫_Ω |g| < ε.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `python3 -I: verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') and child_modules(..., 'contract'). Replay: open MeasureTheory Filter Set Metric; open scoped ENNReal NNReal Topology; namespace GMT.Ch06; open Poincare.SimonGMT.Chapter06 / Chapter03 (...) / Chapter01 (...); noncomputable section; end`
- `python3 scan of dag.json (544 nodes): lean_statements containing fderiv with LipschitzOnWith/LipschitzWith, ContDiff with HasCompactSupport and IntegrableOn, or lineDeriv; lean_names containing gws/ibp/dense/weak_star (only the selected node itself)`
- `rg -n 'slicing_im_ll_gws' over local-references/197bdd4b88278494, lake-packages-25730c7c/simongmt, GMT/, dag.json (no match)`
- `grep -n 'theorem' mathlib/Mathlib/Analysis/Normed/Lp/SmoothApprox.lean (MemLp.exist_eLpNorm_sub_le, HasCompactSupport.exist_eLpNorm_sub_le_of_continuous, Lp.dense_hasCompactSupport_contDiff)`
- `sed -n 1,240p mathlib/Mathlib/Analysis/Calculus/Rademacher.lean (memLp_lineDeriv, integral_lineDeriv_mul_eq, ae_lineDeriv_sum_eq); grep LipschitzWith.ae_differentiableAt`
- `grep ContinuousMapDense.lean (Integrable.exists_hasCompactSupport_integral_sub_le); grep PartitionOfUnity.lean (exists_contDiff_support_eq_eq_one_iff)`
- `#check after import GMT.Ch06.Submission: LipschitzWith.integral_lineDeriv_mul_eq, LipschitzWith.ae_differentiableAt, LipschitzOnWith.extend_real, norm_fderiv_le_of_lipschitzOn, measurable_fderiv, ContDiff.lipschitzWith_of_hasCompactSupport, DifferentiableAt.lineDeriv_eq_fderiv, IsOpen.exists_iUnion_isClosed, exists_compact_between, tendsto_setIntegral_of_monotone, tsupport_fderiv_subset, EuclideanSpace.basisFun_apply, setIntegral_eq_integral_of_forall_compl_eq_zero (all available); MemLp.exist_eLpNorm_sub_le, Integrable.exists_hasCompactSupport_integral_sub_le and ContDiffBump.dist_normed_convolution_le are unknown without an extra import`
- `grep API names: ContinuousLinearMap.aestronglyMeasurable_comp₂, Integrable.bdd_mul, norm_fderiv_le_of_lipschitz, EuclideanSpace.proj, PiLp CoeFun, tsupport_smul_subset_left, HasCompactSupport.smul_right, setIntegral_indicator, setIntegral_sdiff, Set.indicator_compl, eLpNorm_one_eq_lintegral_enorm, integral_norm_eq_lintegral_enorm, ENNReal.toReal_le_of_le_ofReal`
- `git show <candidate_commit>:GMT/Ch06/Submission.lean for accepted nodes: layout is theorem Submission.X inside namespace GMT.Ch06; accepted candidates add SimonGMT imports`
- `grep candidate_inputs/relevant in verifier/gmt-compare.py (no import restriction on Submission.lean); ls shared lake-packages-25730c7c Mathlib oleans for SmoothApprox and Rademacher`
- `cmp snapshot mathlib/<file> vs workspace .lake/packages/mathlib/<file> for every cited file, and snapshot project/GMT/Ch06/Contract.lean vs workspace Contract.lean (all identical)`
- `lake env lean /tmp/gws_split/NodeChallenges.lean, Stmts.lean, Assembly.lean, C1.lean, C2.lean, C4.lean, EndToEnd.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Lp/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Group/Indicator.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-gr-b207eb8151/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-gr-b207eb8151/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-gr-b207eb8151/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/gws_split/NodeChallenges.lean`
- `/tmp/gws_split/Stmts.lean`
- `/tmp/gws_split/Assembly.lean`
- `/tmp/gws_split/C1.lean`
- `/tmp/gws_split/C2.lean`
- `/tmp/gws_split/C4.lean`
- `/tmp/gws_split/EndToEnd.lean`

The snapshot is project d8d46c95 with Mathlib 25730c7c, byte-identical to the shared package tree for every cited file and for Contract.lean. It supplies every tool the four children need: Rademacher (LipschitzWith.ae_differentiableAt), integration by parts for Lipschitz functions (LipschitzWith.integral_lineDeriv_mul_eq), McShane extension (LipschitzOnWith.extend_real), the derivative bound (norm_fderiv_le_of_lipschitzOn / norm_fderiv_le_of_lipschitz), measurability (measurable_fderiv, ContinuousLinearMap.aestronglyMeasurable_comp₂), Lipschitz bounds for C¹ functions with compact support (ContDiff.lipschitzWith_of_hasCompactSupport), density of C_c^∞ in L¹ (MemLp.exist_eLpNorm_sub_le, which needs import Mathlib.Analysis.Normed.Lp.SmoothApprox), a smooth Urysohn function (exists_contDiff_support_eq_eq_one_iff), and exhaustion lemmas (IsOpen.exists_iUnion_isClosed, exists_compact_between). No accepted DAG node or SimonGMT lemma already states integration by parts for Lipschitz-on-Ω functions, convergence against test fields, or density of C_c^∞(Ω) in L¹(Ω), so nothing is reused. The new names slicing_im_ll_gws_{pairing_bound,lipschitz_ibp,smooth_tendsto,smooth_dense} occur nowhere in the snapshot, SimonGMT, GMT sources or dag.json. Scratch Lean checks in the exact comparator scope show: all four child types elaborate; the parent follows from three of them and smooth_tendsto from lipschitz_ibp; complete proofs of all four children and an end-to-end Submission-style file compile using only propext, Classical.choice and Quot.sound.
