# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1`
- Child DAG node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_ibp_lipschitz-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step (3.2)(iii) of the parent proof (“Extend each coordinate v^a|_Ω to a C-Lipschitz function ṽ^a on ℝ^k (McShane extension, Mathlib LipschitzOnWith.extend_real) … Apply (ii) to v_{δ_m} and let m → ∞: on K the integrands … converge a.e. … and are bounded by r!C^r|φ| and (sup_K|ṽ| + 1)(r−1)!C^{r−1}|∂_{b(q)}φ| … dominated convergence gives (P) for ṽ. Since ṽ = v on Ω and Dṽ = Dv a.e. on K ⊆ Ω, (P) holds for v.”). The smoothing v_{δ_m} is done coordinatewise by the sibling lipschitz_smooth_approx, and (ii) is the sibling minor_ibp_smooth applied to the smoothed coordinate rows. (The parent's r is our r+1.)

Notation. λ = Lebesgue measure (volume); K := tsupport φ, compact with K ⊆ Ω; for scalar f, ∂_if(w) := fderiv ℝ f w (e_i); dφ_q := ∂_{b(q)}φ. For a family of scalar rows V : Fin (r+1) → (ℝ^k → ℝ) put M[V](w) := det(∂_{b(s)}V_t(w))_{t,s ∈ Fin (r+1)} and C_q[V](w) := (−1)^q det(∂_{b(q.succAbove s)}V_{t.succ}(w))_{t,s ∈ Fin r}.

1. (Coordinate extensions.) For c ∈ Fin Q, v^c is C-Lipschitz on Ω: |v^c(x) − v^c(y)| = |(v(x) − v(y))_c| ≤ ‖v(x) − v(y)‖ (PiLp.norm_apply_le). By McShane's extension (Mathlib LipschitzOnWith.extend_real) there is ṽ^c : ℝ^k → ℝ, C-Lipschitz on all of ℝ^k, with ṽ^c = v^c on Ω.

2. (Smoothing.) Apply the sibling lipschitz_smooth_approx to each ṽ^c (with L := C): there are G^c_m : ℝ^k → ℝ (m ∈ ℕ) that are C^∞ — in particular C² (ContDiff.of_le; the term `(hG m).of_le (WithTop.coe_le_coe.2 le_top)` proving ContDiff ℝ 2 from ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) was compiled against the frozen import) — C-Lipschitz, with G^c_m → ṽ^c uniformly on ℝ^k and fderiv ℝ G^c_m w → fderiv ℝ ṽ^c w for every w outside a λ-null set N_c. Let N := ⋃_c N_c, a finite union of null sets (ae_all_iff). Since G^c_m and ṽ^c are C-Lipschitz on ℝ^k, ‖fderiv ℝ G^c_m w‖ ≤ C and ‖fderiv ℝ ṽ^c w‖ ≤ C for all w (norm_fderiv_le_of_lipschitz); hence every entry satisfies |∂_iG^c_m(w)| ≤ ‖fderiv ℝ G^c_m w‖·‖e_i‖ ≤ C, and likewise for ṽ^c.

3. (Smooth identity.) For m ∈ ℕ let V^m_t := G^{a(t)}_m (t ∈ Fin (r+1)), C² functions. The sibling minor_ibp_smooth (rows V^m, the same b and φ) gives, with integrals over ℝ^k,
 ∫ φ·M[V^m] dλ = −Σ_q ∫ V^m_0·C_q[V^m]·dφ_q dλ.  (S_m)
 Let Ṽ_t := ṽ^{a(t)}.

4. (Limits, bounds and measurability of the integrands.)
 (a) For w ∉ N, each entry ∂_{b(s)}V^m_t(w) = fderiv ℝ G^{a(t)}_m w (e_{b(s)}) tends to ∂_{b(s)}Ṽ_t(w) (evaluation at e_{b(s)} is continuous). The determinant is a continuous function of the entries (Continuous.matrix_det), so M[V^m](w) → M[Ṽ](w) and C_q[V^m](w) → C_q[Ṽ](w). Moreover V^m_0(w) → Ṽ_0(w) for every w (uniform convergence).
 (b) By the Leibniz formula and the triangle inequality, an n×n matrix whose entries are bounded by C in absolute value has |det| ≤ n!·C^n (prove this from Matrix.det_apply; Matrix.det_le is not imported). Hence |M[V^m](w)| ≤ (r+1)!C^{r+1} and |C_q[V^m](w)| ≤ r!C^r for all m and w. Choose m₀ with |G^{a(0)}_m(w) − ṽ^{a(0)}(w)| ≤ 1 for all w and all m ≥ m₀. For m ≥ m₀ and all w: |φ·M[V^m]| ≤ (r+1)!C^{r+1}·|φ| and |V^m_0·C_q[V^m]·dφ_q| ≤ (|Ṽ_0| + 1)·r!C^r·|dφ_q|. Both majorants are continuous and vanish outside K (dφ_q vanishes off tsupport φ by support_fderiv_subset), so they are integrable.
 (c) Measurability: for every function f, w ↦ fderiv ℝ f w (e_i) is measurable (measurable_fderiv_apply_const); G^c_m, ṽ^c, φ and dφ_q are continuous. So all integrands are a.e.-strongly measurable.

5. (Passage to the limit.) By dominated convergence (Mathlib tendsto_integral_filter_of_dominated_convergence, with the eventual bounds of 4(b) and the a.e. limits of 4(a)), the left side of (S_m) tends to ∫ φ·M[Ṽ] dλ and, for each q, ∫ V^m_0·C_q[V^m]·dφ_q dλ → ∫ Ṽ_0·C_q[Ṽ]·dφ_q dλ (then sum over the finitely many q, tendsto_finsetSum). Since (S_m) holds for every m, uniqueness of limits (tendsto_nhds_unique) gives
 ∫ φ·M[Ṽ] dλ = −Σ_q ∫ Ṽ_0·C_q[Ṽ]·dφ_q dλ.  (S)

6. (Back to v on Ω.)
 (a) Let w ∈ Ω. Since Ω is an open neighbourhood of w on which ṽ^c = v^c, the two functions agree near w, so fderiv ℝ ṽ^c w = fderiv ℝ v^c w (Filter.EventuallyEq.fderiv_eq) and ṽ^c(w) = v^c(w).
 (b) By Rademacher's theorem on Ω (Mathlib LipschitzOnWith.ae_differentiableWithinAt_of_mem; for w in the open set Ω, differentiability within Ω at w is differentiability at w, DifferentiableWithinAt.differentiableAt), v is differentiable at λ-a.e. w ∈ Ω. At such w the chain rule for the continuous linear map EuclideanSpace.proj c gives fderiv ℝ v^c w = (EuclideanSpace.proj c).comp (fderiv ℝ v w) (fderiv_comp), hence ∂_iṽ^c(w) = EuclideanSpace.proj c (fderiv ℝ v w (e_i)) = ∂_iv^c(w).
 Consequently, for λ-a.e. w ∈ Ω: M[Ṽ](w) = M(w), C_q[Ṽ](w) = C_q(w) and Ṽ_0(w) = v^{a(0)}(w); so the integrands of (S) agree λ-a.e. on Ω with φ·M and v^{a(0)}·C_q·dφ_q.
 (c) Outside K ⊆ Ω we have φ = 0 and dφ_q = 0, so the integrands of (S) vanish outside Ω. Therefore each integral over ℝ^k in (S) equals the integral of the same integrand over Ω (setIntegral_eq_integral_of_forall_compl_eq_zero), and by (b) that integral equals the corresponding integral over Ω in the statement (setIntegral_congr_ae; Ω is measurable since it is open).
 Hence ∫_Ω φ·M dλ = −Σ_q ∫_Ω v^{a(0)}·C_q·dφ_q dλ, which is the claim (in Lean, EuclideanSpace.proj (a 0) (v w) * ((-1 : ℝ) ^ (q : ℕ) * Matrix.det (…)) * fderiv ℝ φ w (EuclideanSpace.single (b q) 1)). ∎ (For k = 0 there is no b : Fin (r+1) → Fin 0, so the statement is vacuous.)

Formalization notes. Available under the frozen import (checked; do not add imports): LipschitzOnWith.extend_real, LipschitzOnWith.extend_finite_dimension, norm_fderiv_le_of_lipschitz, norm_fderiv_le_of_lipschitzOn, LipschitzOnWith.ae_differentiableWithinAt_of_mem, Filter.EventuallyEq.fderiv_eq, fderiv_comp, measurable_fderiv_apply_const, Continuous.matrix_det, tendsto_integral_filter_of_dominated_convergence, setIntegral_eq_integral_of_forall_compl_eq_zero, setIntegral_congr_ae, support_fderiv_subset, Matrix.det_apply, Finset.abs_sum_le_sum_abs, Finset.abs_prod. A compiled proof of |det A| ≤ n!·c^n from Matrix.det_apply is contained in the reference implementation of the sibling minor_weak_star (the local fact abs_det_le).

## Key steps

1. McShane: extend each coordinate v^c|_Ω to a C-Lipschitz ṽ^c on ℝ^k.
2. lipschitz_smooth_approx: C^∞ (hence C²), C-Lipschitz G^c_m → ṽ^c uniformly with DG^c_m → Dṽ^c a.e.
3. minor_ibp_smooth for the rows V^m_t = G^{a(t)}_m gives the identity (S_m) on ℝ^k.
4. Dominated convergence (entries bounded by C, |G^{a(0)}_m| ≤ |ṽ^{a(0)}| + 1, supports in tsupport φ) gives (S) for ṽ.
5. On Ω, Dṽ^c = Dv^c (local equality) = proj_c ∘ Dv a.e. (Rademacher); integrands vanish off tsupport φ ⊆ Ω, so (S) becomes the claim over Ω.

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
