# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_approx-a1`
- Child DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_approx-a1.mollify-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 (the mollifier and its facts (a) smoothness, (b) locality, (c) local Lipschitz, derivative and closeness bounds, (d) global bounds) of the supplied proof of dph_lipschitz_smooth_approx, packaged for one scale σ and one L-Lipschitz map F; the parent applies it with F = Ĝ, the globally Lipschitz extension of G from thickening δ A built in the parent's step 1, and σ = σ_j. The mollifier ϕ_σ of the supplied proof (C^∞, ≥ 0, compact support, ϕ_σ(w) = 0 for |w| ≥ σ/2, ∫ϕ_σ = 1) is provided directly by the sibling slicing_mb_sa_mollifier_exists at radius σ/2, as the supplied proof suggests; no rescaling is needed.

Notation. ℝ^p = Eucl p with Euclidean norm |·|; λ = volume is Lebesgue measure on ℝ^m, an additive Haar measure (so it is invariant under translations and under w ↦ −w). B(x, s) = ball x s = {y : |y − x| < s}. For v ∈ ℝ^{m′} and i ∈ Fin m′, v_i (Lean: v i) is the i-th coordinate. ∫ is the Bochner integral over ℝ^m with respect to λ, and a • v is scalar times vector.

1. (Mollifier.) Apply the sibling slicing_mb_sa_mollifier_exists with P = m and radius σ/2 > 0. It gives ρ : ℝ^m → ℝ which is C^∞, has compact support, satisfies ρ(w) ≥ 0 for every w, ρ(w) = 0 whenever σ/2 ≤ |w|, and ∫ρ dλ = 1. In particular ρ is continuous, and being continuous with compact support it is λ-integrable (Continuous.integrable_of_hasCompactSupport); hence so is w ↦ ρ(w)·a for every constant a ∈ ℝ, and w ↦ ρ(w) • v for every constant v ∈ ℝ^{m′}.

2. (Definition and integrability.) F is L-Lipschitz, hence continuous. For x ∈ ℝ^m define
   F_σ(x) := ∫ ρ(w) • F(x − w) dλ(w) ∈ ℝ^{m′}.
   For fixed x the integrand w ↦ ρ(w) • F(x − w) is continuous (product of the continuous ρ and the continuous w ↦ F(x − w)) and vanishes wherever ρ vanishes, so it has compact support (HasCompactSupport.smul_right) and is λ-integrable.

3. (Vanishing outside B(0, σ/2).) If |w| ≥ σ/2 then ρ(w) = 0, so ρ(w) • u = 0 and ρ(w)·a = 0 for all u, a. Therefore, to bound or evaluate an integrand of this form at w, only the points with |w| < σ/2 need to be examined.

4. (Smoothness: property (1).) With the bilinear map lsmul ℝ ℝ (scalar times vector), the convolution satisfies (ρ ⋆[lsmul ℝ ℝ, λ] F)(x) = ∫ lsmul(ρ(w))(F(x − w)) dλ(w) = ∫ ρ(w) • F(x − w) dλ(w) = F_σ(x) (convolution_lsmul), so F_σ = ρ ⋆[lsmul ℝ ℝ, λ] F. Here ρ is C^∞ with compact support, F is continuous and therefore locally integrable, and λ is add-left-invariant and neg-invariant. HasCompactSupport.contDiff_convolution_left with smoothness order n = ⊤ : ℕ∞ therefore shows ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F_σ.

5. (Difference estimate (E).) Claim: let U ⊆ ℝ^m and Λ′ ∈ ℝ≥0 be such that F is Λ′-Lipschitz on U, and let y, y′ ∈ ℝ^m satisfy y − w ∈ U and y′ − w ∈ U for every w with |w| < σ/2. Then |F_σ(y) − F_σ(y′)| ≤ Λ′|y − y′|.
   Proof. Both integrands are integrable (step 2), so by linearity of the integral and ρ(w) • a − ρ(w) • b = ρ(w) • (a − b),
   F_σ(y) − F_σ(y′) = ∫ ρ(w) • (F(y − w) − F(y′ − w)) dλ(w).
   We bound the norm of the integrand at every w by ρ(w)Λ′|y − y′|. If |w| ≥ σ/2 the integrand is 0 (step 3) and the bound is ≥ 0. If |w| < σ/2 then y − w, y′ − w ∈ U, so, as ρ(w) ≥ 0,
   |ρ(w) • (F(y − w) − F(y′ − w))| = ρ(w)|F(y − w) − F(y′ − w)| ≤ ρ(w)Λ′|(y − w) − (y′ − w)| = ρ(w)Λ′|y − y′|.
   The bound w ↦ ρ(w)Λ′|y − y′| is integrable (step 1), so norm_integral_le_of_norm_le gives
   |F_σ(y) − F_σ(y′)| ≤ ∫ ρ(w)Λ′|y − y′| dλ(w) = (∫ρ dλ)·Λ′|y − y′| = Λ′|y − y′|.

6. (Closeness estimate (C).) Claim: let U and Λ′ be as in step 5, and let x ∈ U satisfy x − w ∈ U for every w with |w| < σ/2. Then |F_σ(x) − F(x)| ≤ Λ′σ.
   Proof. ∫ ρ(w) • F(x) dλ(w) = (∫ρ dλ) • F(x) = F(x) (integral_smul_const and ∫ρ = 1). By linearity (both integrands integrable),
   F_σ(x) − F(x) = ∫ ρ(w) • (F(x − w) − F(x)) dλ(w).
   At w with |w| ≥ σ/2 the integrand is 0. At w with |w| < σ/2 we have x − w ∈ U and x ∈ U, so
   |ρ(w) • (F(x − w) − F(x))| ≤ ρ(w)Λ′|(x − w) − x| = ρ(w)Λ′|w| ≤ ρ(w)Λ′σ.
   Integrating the bound as in step 5: |F_σ(x) − F(x)| ≤ (∫ρ dλ)·Λ′σ = Λ′σ.

7. (Global properties (2) and (3).) Take U = ℝ^m and Λ′ = L; F is L-Lipschitz on ℝ^m and every membership condition holds trivially. Step 5 gives |F_σ(y) − F_σ(y′)| ≤ L|y − y′| for all y, y′, so F_σ is L-Lipschitz (LipschitzWith.of_dist_le_mul, dist = norm of the difference). Step 6 gives |F_σ(x) − F(x)| ≤ Lσ for every x.

8. (Local properties (4).) Let x ∈ ℝ^m and Λ′ ∈ ℝ≥0 be such that F is Λ′-Lipschitz on U := B(x, 2σ).
   (a) Lipschitz on B(x, σ): let y, y′ ∈ B(x, σ) and |w| < σ/2. Then |(y − w) − x| ≤ |y − x| + |w| < σ + σ/2 < 2σ, so y − w ∈ U; likewise y′ − w ∈ U. By step 5, |F_σ(y) − F_σ(y′)| ≤ Λ′|y − y′|. Hence F_σ is Λ′-Lipschitz on B(x, σ) (LipschitzOnWith.of_dist_le_mul).
   (b) Derivative bound: B(x, σ) is a neighbourhood of x because σ > 0 (Metric.ball_mem_nhds). A map that is Λ′-Lipschitz on a neighbourhood of x satisfies ‖fderiv ℝ F_σ x‖ ≤ Λ′ (norm_fderiv_le_of_lipschitzOn). Concretely, F_σ is differentiable at x by step 4, and for a unit vector v, |DF_σ(x)v| = lim_{h→0} |F_σ(x + hv) − F_σ(x)|/|h| ≤ Λ′ because x + hv ∈ B(x, σ) for small |h|.
   (c) Closeness at x: x ∈ U since |x − x| = 0 < 2σ, and for |w| < σ/2, |(x − w) − x| = |w| < σ/2 < 2σ, so x − w ∈ U. Step 6 gives |F_σ(x) − F(x)| ≤ Λ′σ.

9. (Locality of coordinates: property (5).) Let x ∈ ℝ^m, i ∈ Fin m′ and c ∈ ℝ with F(y)_i = c for every y ∈ B(x, σ). The coordinate map v ↦ v_i is the continuous linear map EuclideanSpace.proj i, and a continuous linear map commutes with the Bochner integral of an integrable function (ContinuousLinearMap.integral_comp_comm). Hence, by step 2,
   F_σ(x)_i = ∫ (ρ(w) • F(x − w))_i dλ(w) = ∫ ρ(w)·F(x − w)_i dλ(w).
   For every w the integrand equals ρ(w)·c: if |w| ≥ σ/2 both are 0 because ρ(w) = 0; if |w| < σ/2 then |(x − w) − x| = |w| < σ/2 < σ, so x − w ∈ B(x, σ) and F(x − w)_i = c. Therefore F_σ(x)_i = ∫ ρ(w)·c dλ(w) = (∫ρ dλ)·c = c (integral_mul_const).

10. (Conclusion.) The map F_σ of step 2 satisfies (1) by step 4, (2) and (3) by step 7, (4) by step 8 and (5) by step 9. ∎

## Key steps

1. ρ from slicing_mb_sa_mollifier_exists at radius σ/2 (C^∞, ≥ 0, compact support, ρ = 0 for |w| ≥ σ/2, ∫ρ = 1); F_σ(x) := ∫ ρ(w) • F(x − w) dw, the integrand being continuous with compact support.
2. F_σ = ρ ⋆[lsmul ℝ ℝ, volume] F is C^∞ by HasCompactSupport.contDiff_convolution_left (F continuous, hence locally integrable).
3. (E) If F is Λ′-Lipschitz on U and y − w, y′ − w ∈ U for |w| < σ/2, then |F_σ(y) − F_σ(y′)| = |∫ρ(w)•(F(y − w) − F(y′ − w))| ≤ ∫ρ(w)Λ′|y − y′| = Λ′|y − y′|.
4. (C) If moreover x, x − w ∈ U for |w| < σ/2, then |F_σ(x) − F(x)| = |∫ρ(w)•(F(x − w) − F(x))| ≤ ∫ρ(w)Λ′|w| ≤ Λ′σ.
5. U = ℝ^m gives (2) and (3); U = B(x, 2σ) with y, y′ ∈ B(x, σ) gives the local Lipschitz bound, then norm_fderiv_le_of_lipschitzOn on the neighbourhood B(x, σ) and (C) at x give (4).
6. EuclideanSpace.proj i commutes with the integral and F(x − w)_i = c wherever ρ(w) ≠ 0, so F_σ(x)_i = c∫ρ = c, which is (5).

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `read nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-approx-a1/{parent-child-handoff.json,parent-supplied-natural-proof.json,parent-supplied-plan.md}: frozen type, supplied proof, depends_on = []; nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1/decomposition-v2.json (encoding of reused accepted children)`
- `python3 over dag.json (662 nodes): subtree of pushforward_homotopy-a1 (this node depth 4, status decomposing); regex 'molli|convol|mcshane|extend_real|bump|alternat|tangential|norm_fderiv|smooth_approx|smoothing' over lean_names/titles and 'McShane|Kirszbraun|extend_real|extend_pi|eq_smul_basis_det|alternating|convolution|lsmul' over statements; printed statements of slicing_mb_sa_mollifier_exists, slicing_mb_sa_mollify_lipschitz_close, slicing_mb_sa_mollify_lipschitz_hasFDerivAt, slicing_mb_smooth_approx, deformation_ipl_mwc_lipschitz_smooth_approx, slicing_im_ll_mollify, rpn_pe_convolution_contDiff_fderiv, smr_ci_covector_eq_zero_of_coord, cmb_covector_eq_sum_coord_smul_wedge, slicing_ru_covector_expansion, polyhedral_approx_pairing_covector_ext, ltg_covector_separating, lpf_rsn_covector_separating_family`
- `nodes/root-slicing-a1-slice-mass-bound-a1-smooth-approx-a1-mollifier-a1/{parent-child-handoff.json,isolated-comparator-result.json} (passed = true); git show 9735e2124d87ab3acc03bb8f199805df921599c5:GMT/Ch06/Submission.lean (accepted Lean proof of slicing_mb_sa_mollifier_exists); git show e9af228dd670dfa9a25505d00d9f3c1dab59b04d:GMT/Ch06/Submission.lean (this node's proof base: declaration absent)`
- `grep simongmt Chapter06/{Forms,Currents,FormsDuality}.lean: Covector E n = E [⋀^Fin n]→L[ℝ] ℝ, DifferentialForm E n = E → Covector E n, TestFormOn = testFormOnSubmodule, SimonMultiIndex n p = Fin n ↪o Fin p`
- `grep pinned Mathlib: LipschitzOnWith.extend_real (Topology/MetricSpace/Lipschitz.lean:308), LipschitzOnWith.extend_pi (:344), LipschitzOnWith.extend_finite_dimension (Analysis/Normed/Module/FiniteDimension.lean:207), HasCompactSupport.contDiff_convolution_left (Analysis/Calculus/ContDiff/Convolution.lean:427, order n : ℕ∞), convolution_lsmul (Analysis/Convolution.lean:423), norm_fderiv_le_of_lipschitzOn (Analysis/Calculus/FDeriv/Basic.lean:939), AlternatingMap.eq_smul_basis_det (LinearAlgebra/Determinant.lean:650), ContinuousAlternatingMap.compContinuousLinearMap and map_eq_zero_of_not_injective (Topology/Algebra/Module/Alternating/Basic.lean:314,137), ContinuousLinearMap.integral_comp_comm and integral_smul_const (MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean:70,219), Continuous.integrable_of_hasCompactSupport (MeasureTheory/Function/LocallyIntegrable.lean:622), norm_integral_le_of_norm_le (MeasureTheory/Integral/Bochner/Basic.lean:985), image_eq_one_of_notMem_mulTSupport (Topology/Algebra/Support.lean:111, additive form image_eq_zero_of_notMem_tsupport), Metric.mem_thickening_iff (Topology/MetricSpace/Thickening.lean:143), Metric.tendstoUniformly_iff (Topology/MetricSpace/Pseudo/Basic.lean:157), Filter.EventuallyEq.fderiv_eq (Analysis/Calculus/FDeriv/Congr.lean:260), EuclideanSpace.dist_eq/equiv/proj (Analysis/InnerProductSpace/PiL2.lean:158,276,285), PiLp.dist_apply_le (Analysis/Normed/Lp/PiLp.lean:652); no LipschitzOnWith.congr exists`
- `name uniqueness: python3 over dag.json lean_names; rg 'dph_sa_|mollify_lipschitz|covector_comp_eq_zero' over GMT/, .lake/packages/simongmt, .lake/packages/mathlib/Mathlib; git log --all -S 'dph_sa_' (no match anywhere)`
- `read /runtime/flows/*/_recursive_lean/runtime.py: _existing_lean_name_problem (accepted cross-branch reuse requires an identical lean_statement), child activation by lean_name, accepted reused children skip handoff installation`
- `python3 -I: verifier/lean_contract.py validate_lean_statement and verifier/gmt-compare.py contract_scope(GMT/Ch06/Contract.lean, GMT.Ch06.main_theorem) + child_modules on the 3 child statements and the parent statement`
- `lake env lean /tmp/dphsa/lean/{Stmts,Alt,Mol,Combined2}.lean and /tmp/dphsa-review/lean/IfaceNoExt.lean (parent from the two new child statements as hypotheses): statements elaborate; complete proofs of both new children; exact frozen parent proved from them; EXIT 0; axioms propext, Classical.choice, Quot.sound`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-approx-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-approx-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-approx-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-smooth-approx-a1-mollifier-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-smooth-approx-a1-mollifier-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/dphsa/lean/Combined2.lean`
- `/tmp/dphsa-review/lean/IfaceNoExt.lean`

Neither the pinned project nor SimonGMT has a vector-valued mollification with local Lipschitz, derivative and closeness bounds and locality of coordinates, or a lemma killing pulled-back covectors with image in span{e_α}. The DAG's accepted mollification lemmas are scalar-valued and/or global, and its accepted covector lemmas state different facts. So mollify (dph_sa_mollify_lipschitz) and covector_vanish (dph_sa_covector_comp_eq_zero) are new obligations, and both names are globally unique. The accepted slicing_mb_sa_mollifier_exists (candidate 9735e212, comparator passed) is exactly the mollifier of supplied step 2. It is reused by name with a byte-identical type, title and statement. This node's proof base e9af228d lacks it, so it must be a declared sibling. Mathlib's LipschitzOnWith.extend_finite_dimension covers supplied step 1, so there is no extension child. Every Mathlib lemma cited in the child proofs exists at the pinned commit. In Lean, both new children are fully proved, and the exact frozen parent is proved from them, with standard axioms only.
