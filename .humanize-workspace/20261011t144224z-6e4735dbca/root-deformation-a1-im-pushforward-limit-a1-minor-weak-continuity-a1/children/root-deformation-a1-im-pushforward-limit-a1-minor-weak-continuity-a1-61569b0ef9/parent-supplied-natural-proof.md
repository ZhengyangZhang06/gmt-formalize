# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1`
- Child DAG node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.lipschitz_smooth_approx-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step (3.2)(iii) of the parent proof (“Let ρ_δ (0 < δ < d) be a standard mollifier … and v_δ := ρ_δ * ṽ componentwise. Then v_δ is C^∞; v_δ → ṽ uniformly on ℝ^k as δ → 0 …; ∂_bv_δ = ρ_δ * ∂_bṽ (differentiate under the integral sign …), hence |∂_bv_δ^a| ≤ C; and ∂_bv_δ → ∂_bṽ a.e. along any sequence δ_m → 0 (Lebesgue differentiation for mollifiers)”), for one scalar coordinate function g = ṽ^a and δ_m = 1/(m+1). The three analytic facts are supplied by the reused, comparator-accepted siblings ae_mollifier (kernels and Lebesgue differentiation), mollify_close (uniform error) and mollify_fderiv (differentiation under the integral sign).

Notation. λ = Lebesgue measure on ℝ^k (volume); e_b := EuclideanSpace.single b 1; Dg(w) := fderiv ℝ g w; for f, ψ : ℝ^k → ℝ, (f ∗ ψ)(x) := ∫ f(t)ψ(x − t) dλ(t) = convolution f ψ (ContinuousLinearMap.lsmul ℝ ℝ) volume x.

1. (Kernels.) Let ψ_m (m ∈ ℕ) be the functions given by the sibling ae_mollifier for n := k: each ψ_m is C^∞ with compact support, tsupport ψ_m ⊆ closedBall 0 (1/(m+1)), ψ_m ≥ 0, ∫ ψ_m dλ = 1, and for every locally integrable f : ℝ^k → ℝ, (f ∗ ψ_m)(x) → f(x) as m → ∞ for λ-a.e. x. If ‖y‖ ≥ 2/(m+1) then y ∉ closedBall 0 (1/(m+1)) ⊇ tsupport ψ_m, so ψ_m(y) = 0 (image_eq_zero_of_notMem_tsupport).

2. (Definition.) Put G_m(x) := ∫ ψ_m(y)·g(x − y) dλ(y). For each x the integrand is continuous and vanishes where ψ_m does, so it has compact support and is integrable. By the definition of the convolution (convolution_def; lsmul ℝ ℝ a c = a·c), G_m = convolution ψ_m g (lsmul ℝ ℝ) volume.

3. (Smoothness.) g is continuous (being Lipschitz), hence locally integrable; ψ_m is C^∞ with compact support. Mathlib HasCompactSupport.contDiff_convolution_left (λ is invariant under translations and under negation) shows that ψ_m ⋆ g = G_m is C^∞, i.e. ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G_m.

4. (Lipschitz constant L.) For x, x′ ∈ ℝ^k, by linearity G_m(x) − G_m(x′) = ∫ ψ_m(y)(g(x − y) − g(x′ − y)) dλ(y), and |ψ_m(y)(g(x − y) − g(x′ − y))| ≤ ψ_m(y)·L‖(x − y) − (x′ − y)‖ = ψ_m(y)·L‖x − x′‖ because ψ_m ≥ 0. Integrating this bound (norm_integral_le_of_norm_le) and using ∫ψ_m = 1 gives |G_m(x) − G_m(x′)| ≤ L‖x − x′‖. So G_m is L-Lipschitz (LipschitzWith.of_dist_le_mul).

5. (Uniform convergence.) Apply the sibling mollify_close with P := k, F := g, ρ := ψ_m and σ := 2/(m+1): ρ is continuous with compact support, ρ ≥ 0, ρ(y) = 0 whenever σ ≤ ‖y‖ (Step 1), and ∫ρ = 1. It yields |G_m(x) − g(x)| ≤ L·2/(m+1) for every x ∈ ℝ^k. Since 2L/(m+1) → 0, G_m → g uniformly on ℝ^k (Metric.tendstoUniformly_iff).

6. (Derivative of G_m.) Apply the sibling mollify_fderiv with P := k, F := g, ρ := ψ_m (continuous, compact support): for every x, G_m has Fréchet derivative ∫ ψ_m(y)·Dg(x − y) dλ(y) at x (a Bochner integral in ℝ^k →L[ℝ] ℝ); hence fderiv ℝ G_m x = ∫ ψ_m(y)·Dg(x − y) dλ(y) (HasFDerivAt.fderiv). The integrand y ↦ ψ_m(y)·Dg(x − y) is a.e.-strongly measurable (measurable_fderiv composed with y ↦ x − y), has norm ≤ L·ψ_m(y) (‖Dg‖ ≤ L by norm_fderiv_le_of_lipschitz) and vanishes outside tsupport ψ_m, so it is integrable; therefore evaluation at a fixed vector e commutes with the integral (ContinuousLinearMap.integral_apply). With h_e(t) := Dg(t)(e) and the measure-preserving substitution t = x − y (integral_sub_left_eq_self):
 fderiv ℝ G_m x (e) = ∫ ψ_m(y)·h_e(x − y) dλ(y) = ∫ h_e(t)·ψ_m(x − t) dλ(t) = (h_e ∗ ψ_m)(x).

7. (a.e. convergence of the partial derivatives.) h_e is measurable (measurable_fderiv_apply_const) and |h_e| ≤ L‖e‖, so h_e is locally integrable. By ae_mollifier, (h_e ∗ ψ_m)(x) → h_e(x) = Dg(x)(e) for λ-a.e. x. Apply this to the finitely many vectors e = e_b (b ∈ Fin k) and intersect the full-measure sets (ae_all_iff): for λ-a.e. x, fderiv ℝ G_m x (e_b) → Dg(x)(e_b) for every b ∈ Fin k.

8. (Operator-norm convergence.) For T : ℝ^k →L[ℝ] ℝ and z ∈ ℝ^k write z = Σ_b z_b e_b with |z_b| ≤ ‖z‖ (PiLp.norm_apply_le); then |Tz| ≤ Σ_b |z_b||Te_b| ≤ (Σ_b |Te_b|)‖z‖, so ‖T‖ ≤ Σ_b |Te_b| (ContinuousLinearMap.opNorm_le_bound). For x as in Step 7 and T := fderiv ℝ G_m x − Dg(x) this gives ‖fderiv ℝ G_m x − Dg(x)‖ ≤ Σ_b |fderiv ℝ G_m x (e_b) − Dg(x)(e_b)| → 0. Hence fderiv ℝ G_m x → fderiv ℝ g x for λ-a.e. x.

9. (Conclusion.) The sequence (G_m) has the four required properties (Steps 3, 4, 5 and 8). ∎ (For k = 0 every step applies verbatim: ℝ⁰ is a point, and ae_mollifier covers n = 0.)

Formalization notes. Available under the frozen import (checked; do not add imports): HasCompactSupport.contDiff_convolution_left, convolution_def, convolution_eq_swap, integral_sub_left_eq_self, measurable_fderiv, measurable_fderiv_apply_const, norm_fderiv_le_of_lipschitz, ContinuousLinearMap.integral_apply, ContinuousLinearMap.opNorm_le_bound, norm_integral_le_of_norm_le, PiLp.norm_apply_le, Metric.tendstoUniformly_iff. NOT available: ContDiffBump.normed and Mathlib's BumpFunction/Convolution file (ae_convolution_tendsto_right_of_locallyIntegrable, dist_normed_convolution_le); the siblings replace them.

## Key steps

1. Kernels ψ_m from ae_mollifier (C^∞, ≥ 0, ∫ = 1, support in the closed 1/(m+1)-ball, a.e. convergence of f ∗ ψ_m for locally integrable f).
2. G_m := ∫ψ_m(y)g(· − y)dy = ψ_m ⋆ g is C^∞ (HasCompactSupport.contDiff_convolution_left) and L-Lipschitz (average of translates of g).
3. Uniform convergence |G_m − g| ≤ 2L/(m+1) from mollify_close with σ = 2/(m+1).
4. mollify_fderiv: DG_m(x)e_b = ∫ψ_m(y)Dg(x−y)e_b dy = (∂_bg ∗ ψ_m)(x).
5. ae_mollifier for the bounded measurable ∂_bg (b ∈ Fin k) and ‖T‖ ≤ Σ_b|Te_b| give DG_m → Dg a.e.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886 = git HEAD; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean; cmp GMT/Ch06/Contract.lean local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean (both byte-identical)`
- `python3 -I over dag.json: this node (depth 3, status decomposing, attempt 1, depends_on root.compactness_mass_bounds-a1.covector_expansion-a1) and the parent's decomposition-v3.json (format of reused children)`
- `python3 -I regex over dag.json titles/statements/lean statements: mollif|Piola|dense in|density of|C_c|integration by parts|weak-*|weak star|cofactor|convolution|minors|smooth approximation|ContDiffBump`
- `python3 -I over dag.json: status, candidate_commit, title/statement/lean_statement equality with the handoff for constancy_mdc_smooth_approx_identity_ae_tendsto, slicing_mb_sa_mollify_lipschitz_hasFDerivAt, slicing_mb_sa_mollify_lipschitz_close, cmb_covector_eq_sum_coord_smul_wedge (all accepted, equal); lean_name collisions for deformation_ipl_mwc_* (none)`
- `grep -rn deformation_ipl_mwc over GMT/, the snapshot project, simongmt/Poincare and the snapshot Mathlib (no match)`
- `rg -n 'abbrev Covector|SimonMultiIndex|def wedgeCovectors|theorem wedgeCovectors_apply_det|def euclideanCovectorCoordinate' simongmt/Poincare/SimonGMT`
- `rg -n 'theorem norm_fderiv_le_of_lipschitzOn|LipschitzOnWith.extend_real|extend_finite_dimension|lipschitzExtensionConstant' snapshot Mathlib`
- `rg -n '^theorem' Mathlib/Analysis/Calculus/Rademacher.lean and Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean; sed ContinuousMapDense.lean 135-240, LineDeriv/IntegrationByParts.lean 215-245, ContDiff/Convolution.lean 50-100 and 415-435, Matrix/AbsoluteValue.lean det_le, ContDiff/RCLike.lean lipschitzWith_of_hasCompactSupport, FDeriv/Mul.lean finsetProd`
- `git log --all -G'^import' -- GMT/Ch06/Submission.lean; git show cdfc95dc (leaf gate rejects added imports); git show 2219dd32 (accepted ae-mollifier proof uses IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub)`
- `lake env lean /tmp/mwc_decomp/build/Avail.lean, build_v2/Avail2.lean, build_v2/Avail3.lean, build_v2/Small2.lean (#check availability under import GMT.Ch06.Submission)`
- `python3 -I /tmp/mwc_decomp/gen.py (verifier lean_contract.validate_lean_statement + gmt-compare child_modules, contract mode) and lake env lean on the eleven /tmp/mwc_decomp/build_final/*_challenge.lean (all exit 0, sorry warnings only)`
- `lake env lean /tmp/mwc_decomp/build/Assembly.lean, build_v2/F_from_E.lean, build_v2/E_from_AD.lean, build_v2/RefImpl.lean (#print axioms: propext, Classical.choice, Quot.sound)`
- `grep 'Your solution is okay' in comparator-v1.log and isolated-comparator-result.json (passed: true) of the four reused nodes`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1/speculative-prompt-v4.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-covector-expansion-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-local-on-balls-a1-density-constancy-a1-smooth-appro-6a720fda87/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-local-on-balls-a1-density-constancy-a1-smooth-appro-6a720fda87/comparator-v1.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-smooth-approx-a1-mollify-fderiv-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-smooth-approx-a1-mollify-close-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Matrix/AbsoluteValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/mwc_decomp/build_final`
- `/tmp/mwc_decomp/build/Assembly.lean`
- `/tmp/mwc_decomp/build_v2/F_from_E.lean`
- `/tmp/mwc_decomp/build_v2/E_from_AD.lean`
- `/tmp/mwc_decomp/build_v2/RefImpl.lean`
- `/tmp/mwc_decomp/build/Avail.lean`
- `/tmp/mwc_decomp/build_v2/Avail2.lean`
- `/tmp/mwc_decomp/build_v2/Avail3.lean`

Pinned revisions are confirmed (HEAD = project_commit), and Contract = Submission = the snapshot Contract byte-for-byte.
No existing proof: neither Mathlib, SimonGMT nor any accepted DAG node proves weak continuity of Jacobian minors, the Piola identity or L¹-density by smooth functions. (The r = 1 analogue slicing_im_ll_gradient_weak_star and the density node slicing_im_ll_gws_smooth_dense are not accepted.) Hence seven new children; their names deformation_ipl_mwc_* collide with nothing.
Reused, with byte-identical types and comparator-passed: cmb_covector_eq_sum_coord_smul_wedge, constancy_mdc_smooth_approx_identity_ae_tendsto, slicing_mb_sa_mollify_lipschitz_hasFDerivAt, slicing_mb_sa_mollify_lipschitz_close.
Import closure: the leaf gate forbids new imports (commit cdfc95dc).
- Available in the frozen closure: SimonGMT wedgeCovectors_apply_det; Mathlib norm_fderiv_le_of_lipschitzOn, LipschitzOnWith.extend_real, extend_finite_dimension, LipschitzOnWith.ae_differentiableWithinAt_of_mem, LipschitzWith.integral_lineDeriv_mul_eq, HasCompactSupport.contDiff_convolution_left/right, ContDiffAt.isSymmSndFDerivAt, HasFDerivAt.finsetProd, Matrix.det_succ_row_zero, Matrix.det_apply, measurable_fderiv(_apply_const), tendsto_integral_filter_of_dominated_convergence, IsCompact.exists_cthickening_subset_open, ContDiff.lipschitzWith_of_hasCompactSupport.
- Not available: ContDiffBump.normed and BumpFunction/Convolution, ContinuousMapDense, LineDeriv/IntegrationByParts, Matrix.det_le. The children replace them by the reused siblings or by short arguments.
Lean checks:
- All eleven statements validate and elaborate in the exact comparator scope.
- Three links compile with only propext, Classical.choice and Quot.sound: parent ⇐ coeff_minor_continuity + covector expansion; coeff_minor_continuity ⇐ minor_weak_star; minor_weak_star ⇐ test_density + minor_ibp_lipschitz.
