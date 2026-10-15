# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1`
- Child DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 of the parent proof (Simon 5.1, (27)–(28)). Hypothesis (H) supplies the mass formula and the support-null property. The parent instantiates (H) from MF with U = W = univ (M ∩ univ = M; X.mass is by definition X.massOn univ) and from the sibling support_null.

Notation.
- n = m + 1, E := Eucl n, L := volume on E. By EuclideanSpace.euclideanHausdorffMeasure_eq_volume n, μHE[n] = L on E.
- e = (e_0, …, e_m) with e_i = EuclideanSpace.single i 1 = EuclideanSpace.basisFun (Fin n) ℝ i.
- b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis, so b_i = e_i.
- For an n-form ω, ω_e(x) := ω(x)(e).

1. (Triple.) Since X is integer multiplicity, choose M, θ, ξ with:
   - IsRectifiableTriple univ n M θ ξ;
   - θ(x) ∈ ℕ for every x ∈ M;
   - X(ω) = tauAction n M θ ξ ω = ∫_M θ(x) ξ(x)(ω(x)) dμHE[n] for all ω.
   Applying (H) to this triple gives:
   (H1) M(X) = ∫⁻_M ofReal θ dμHE[n];
   (H2) μHE[n](M ∖ spt X) = 0.

2. (Measurable core.) M is μHE[n]-null-measurable (IsRectifiableTriple.nullMeasurableSet), that is, L-null-measurable. Choose a measurable M' ⊆ M with M' = M L-a.e. (NullMeasurableSet.exists_measurable_subset_ae_eq). Then L⌞M' = L⌞M (Measure.restrict_congr_set).

3. (Determinant covector.) Let Δ := wedgeCovectors n (fun j => EuclideanSpace.proj j) ∈ Covector E n. By wedgeCovectors_apply_det, Δ(v) = det(Matrix.of fun i j => (v j) i). This equals b.det v (Module.Basis.det_apply), because the (i, j) entry of b.toMatrix v is the i-th coordinate of v_j. Consequently:
   (a) Δ(e) = b.det b = 1 (Module.Basis.det_self).
   (b) Every α ∈ Covector E n satisfies α(v) = α(e) Δ(v) for all v. Indeed, AlternatingMap.eq_smul_basis_det, applied to the alternating map underlying α and the basis b, gives α = α(b) • b.det.
   (c) If τ : Fin n → E is orthonormal, then Δ(τ) = 1 or Δ(τ) = −1. τ is linearly independent with n = finrank E elements, so it spans E (LinearIndependent.span_eq_top_of_card_eq_finrank) and forms an orthonormal basis (OrthonormalBasis.mk). By OrthonormalBasis.det_to_matrix_orthonormalBasis_real, its determinant with respect to the orthonormal basis EuclideanSpace.basisFun is ±1, that is, Δ(τ) = b.det τ = ±1.
   Alternative to (c): the accepted Submission.fiw_ims_frame_sign (commit c90a40505abdbff33b9174acf9b20037eb2cb2a1), with τ := e and τ' := τ, gives simpleNVector τ = ±simpleNVector e. Hence Δ(τ) = ±Δ(e) = ±1. Its Lean proof may be copied inside this proof.

4. (Signs.) Put s(x) := ξ(x)(Δ) ∈ ℝ.
   - For every x and every covector α, step 3(b) gives α = α(e) • Δ as covectors. By linearity of the continuous linear map ξ(x), ξ(x)(α) = α(e) s(x). In particular ξ(x)(ω(x)) = ω_e(x) s(x) for every ω and every x.
   - For L-a.e. x ∈ M, IsRectifiableTriple.orients (with μHE[n]⌞M = L⌞M) gives ξ(x) = ±simpleNVector τ for an orthonormal τ. Then s(x) = ±Δ(τ) ∈ {1, −1} by simpleNVector_apply and 3(c).

5. (Measurability.)
   - θ is a.e.-strongly measurable for L⌞M. Write M = ⋃_{k ∈ ℕ} (M ∩ closedBall(0, k)) (iUnion_closedBall_nat). θ is integrable on each M ∩ closedBall(0, k) by IsRectifiableTriple.integrableOn with the compact set closedBall(0, k) ⊆ univ. Then aestronglyMeasurable_iUnion_iff glues the pieces.
   - s is a.e.-strongly measurable for L⌞M: ξ is (IsRectifiableTriple.aestronglyMeasurable), and evaluation at the fixed covector Δ is a continuous linear map NVector E n → ℝ (ContinuousLinearMap.apply composed with ξ).
   - Since L⌞M' = L⌞M and M' is measurable, u₀ := M'.indicator (fun x => θ(x) s(x)) is L-a.e.-strongly measurable (aestronglyMeasurable_indicator_iff).

6. (Integer values a.e.) For L-a.e. x, u₀(x) ∈ ℤ. If x ∈ M' (⊆ M), then θ(x) ∈ ℕ and s(x) = ±1 by step 4, so u₀(x) ∈ ℤ. If x ∉ M', then u₀(x) = 0. (Use ae_restrict_iff' with M' measurable.)

7. (Borel integer-valued representative.) Let u₁ be the strongly measurable modification of u₀ (AEStronglyMeasurable.mk), so u₁ = u₀ L-a.e. Define u(x) := u₁(x) if u₁(x) ∈ range(Int.cast : ℤ → ℝ), and u(x) := 0 otherwise.
   - range(Int.cast) is countable, hence measurable, so u is measurable (Measurable.ite).
   - u(x) ∈ ℤ for every x.
   - u = u₀ L-a.e., by step 6.

8. (Absolute value and mass.)
   - For L-a.e. x ∈ M', |u(x)| = |θ(x) s(x)| = θ(x), since θ > 0 on M ⊇ M' and |s| = 1 a.e. on M.
   - For x ∉ M', u(x) = u₀(x) = 0 a.e.
   Hence ofReal|u| = M'.indicator (ofReal ∘ θ) L-a.e., and
   ∫⁻ ofReal|u| dL = ∫⁻ M'.indicator(ofReal ∘ θ) dL = ∫⁻_{M'} ofReal θ dL = ∫⁻_M ofReal θ dL = ∫⁻_M ofReal θ dμHE[n] = M(X).
   The steps use lintegral_congr_ae, lintegral_indicator (M' measurable), Measure.restrict_congr_set, μHE[n] = L and (H1).

9. (Integrability.) u is measurable and ∫⁻ ‖u‖ₑ dL = ∫⁻ ofReal|u| dL = M(X) < ∞ (hypothesis), so u ∈ L¹(L).

10. (Vanishing off the support.) By (H2), L(M ∖ spt X) = 0. For L-a.e. x the following hold simultaneously:
   - u(x) = u₀(x);
   - x ∉ M ∖ spt X;
   - x ∈ M ⟺ x ∈ M'.
   For such x with x ∉ spt X we get x ∉ M, so x ∉ M' and u(x) = u₀(x) = 0. This is ∀ᵐ x ∂L, x ∉ spt X → u(x) = 0.

11. (Representation.) For ω ∈ D^n(ℝ^n):
   X(ω) = ∫_M θ(x) ξ(x)(ω(x)) dμHE[n]
   = ∫_{M'} θ(x) ξ(x)(ω(x)) dL (μHE[n] = L, Measure.restrict_congr_set)
   = ∫ M'.indicator(fun x => θ(x) ξ(x)(ω(x))) dL (integral_indicator, M' measurable)
   = ∫ u₀(x) ω_e(x) dL (pointwise, since θ(x) ξ(x)(ω(x)) = θ(x) s(x) ω_e(x) by step 4)
   = ∫ u(x) ω_e(x) dL (integral_congr_ae, u = u₀ a.e.).

12. u has all asserted properties: steps 7, 9, 8, 10 and 11. ∎

Lean hint, not needed for the argument: the unaccepted speculative draft at commit 635e85e5c7656dfc05e853d89f747f0d729d9f84 (theorem Submission.br_top_dim_lattice_approximation, the block beginning `obtain ⟨u, hu_meas, hu_Z, hu_loc, hE1⟩`) formalizes steps 2–7 and 11 under the same imports and may be consulted. Caching the instance with `let _ : MeasureSpace (Eucl (m + 1)) := measureSpaceOfInnerProductSpace` lowered its heartbeat count.

## Key steps

1. Choose the integer multiplicity triple (M, θ, ξ) of X; (H) gives M(X) = ∫_M θ dH^n and H^n(M ∖ spt X) = 0.
2. Every n-covector equals α(e)·Δ with Δ the determinant covector, and orthonormal frames have Δ(τ) = ±1, so ξ(x)(α) = α(e)·s(x) with s = ξ(·)(Δ) = ±1 a.e. on M.
3. u₀ := 1_{M'}θs (M' a measurable core of M) is a.e.-strongly measurable and integer-valued a.e.; take the Borel integer-valued representative u of AEStronglyMeasurable.mk.
4. |u| = 1_{M'}θ a.e. gives ∫|u| = M(X) < ∞ (so u ∈ L¹), and H^n(M ∖ spt X) = 0 gives u = 0 a.e. off spt X.
5. X(ω) = ∫_M θ ξ(ω) dH^n = ∫ u ω_e dL by step 4 and u = u₀ a.e.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (local-project; project d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/.../project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean; cmp Contract.lean Submission.lean; git show 48003458:GMT/Ch06/Submission.lean | cmp (all identical: the node base holds only the frozen contract)`
- `sed -n 120,364p GMT/Ch06/Submission.lean (LatticeFaceIndex, latticeFace, latticeFaceAction, IsLatticeChain, IsIntegerMultiplicity, IsRectifiableTriple, tauAction)`
- `grep -n 'def covectorEuclideanNorm|def massAdmissibleOn|def GeometricCurrentOn.massOn|def GeometricCurrentOn.mass|structure GeometricCurrentOn|def TestFormOnConverges|def GeometricCurrentOn.support|def simpleNVector|def wedgeCovectors|abbrev SimonMultiIndex|instance.*GeometricCurrentOn' simongmt/Poincare/SimonGMT (GeometricCurrentOn has only a Zero instance, no Sub)`
- `grep -n 'def blowUpMap|def HasWeightedApproximateTangentSpaceAt|def CountablyRectifiable|countablyRectifiable_range|CountablyRectifiable.mono' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -rn in local-references mathlib: EuclideanSpace.euclideanHausdorffMeasure_eq_volume, AlternatingMap.eq_smul_basis_det, OrthonormalBasis.det_to_matrix_orthonormalBasis_real, aestronglyMeasurable_iUnion_iff, lintegral_iUnion₀, integral_iUnion_ae, setIntegral_eq_integral_of_forall_compl_eq_zero, lintegral_mul_left_eq_self (to_additive lintegral_add_left_eq_self), lintegral_lintegral_swap, PiLp.volume_preserving_ofLp, volume_Icc_pi, exists_least_of_bdd, tendsto_measure_iUnion_atTop, tendsto_measure_iInter_atTop, ofReal_integral_eq_lintegral_ofReal, setLIntegral_mono', mem_cthickening_of_dist_le, EuclideanSpace.dist_eq, StrictMono.eq_id, Integrable.mul_bdd, lintegral_const_mul', Int.measurable_floor, lintegral_indicator₀ (all found)`
- `python3 scan of dag.json (360 nodes): statuses, frozen lean_statement of siblings fiw_tb_rectifiable_support_null and fiw_tb_translation_estimate, accepted declarations and candidate commits; no lean_name containing 'tda'; git log --all --oneline -S fiw_tb_tda_ (no match)`
- `git cat-file -t 52afef6d 5c248501 eefd7c3e c90a4050 e8e708e4 49ba437c 3d98b187 0561b355 d57bd370 635e85e5 (all present)`
- `git show 635e85e5 -- GMT/Ch06/Submission.lean; tail speculative-process-v3.log of root-boundary-rectifiability-a1-top-dim-lattice-approx-a1 (1060-line single theorem, 178,656 of 200,000 heartbeats)`
- `sed parent-supplied-natural-proof.md of root-boundary-rectifiability-a1-top-dim-lattice-approx-a1 and root-integrality-weak-limits-a1-top-dim-a1 (related top-dimensional arguments; not duplicated)`
- `grep -n in /runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean: def _decompose, def _solve_children, def _existing_lean_name_problem, def _install_parent_supplied_child_handoff, def _overlay prerequisites (runtime.py), def check_source_delta (leaf_verification.py), def ensure (store.py)`
- `verifier/gmt-compare.py contract_scope/child_modules; python3 -I /tmp/tda-tools/check.py (validate_lean_statement on all 8 child types: pass)`
- `lean /tmp/tda-decomp/{Stmts,Comparator,Assembly2,Assembly3,Proto,Proto2}.lean with LEAN_PATH = lake-packages-25730c7c builds + workspace .lake build of d8d46c9 (0 errors; Assembly3 #count_heartbeats 10,901)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1/decomposition-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-top-dim-lattice-approx-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-top-dim-lattice-approx-a1/speculative-process-v3.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-top-dim-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/math-wiki/submission-fiw-ims-sc-continuous-of-bound.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Group/LIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Int/LeastGreatest.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Preorder/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Floor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/tda-decomp/Stmts.lean`
- `/tmp/tda-decomp/Comparator.lean`
- `/tmp/tda-decomp/Assembly2.lean`
- `/tmp/tda-decomp/Assembly3.lean`
- `/tmp/tda-decomp/Proto.lean`
- `/tmp/tda-decomp/Proto2.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) has the frozen Ch06 contract, and this node's base commit 48003458 adds no accepted declarations. Neither the project nor SimonGMT contains any of the following, so they become the 8 children:
- the top-dimensional density lemma;
- integer medians;
- the lattice-cube toolkit;
- the chain current;
- the difference-current mass bound;
- the summed Poincaré bound.

API the child proofs use:
- SimonGMT: GeometricCurrentOn (Zero instance only, so S = X − Pc is built from toCurrent subtraction), massOn/mass via massAdmissibleOn and covectorEuclideanNorm, simpleNVector_apply, wedgeCovectors_apply_det, blowUpMap, HasWeightedApproximateTangentSpaceAt, countablyRectifiable_range and CountablyRectifiable.mono.
- Mathlib: every lemma cited in the child proofs was found at the pinned revision.

Accepted declarations, cited only as adaptation pointers (all commits present locally): lpf_pic_current_of_dominated_density (52afef6d), fiw_ims_sc_continuous_of_bound (5c248501), isoperimetric_coord_box_measure (eefd7c3e), fiw_ims_frame_sign (c90a4050).

Scratch checks:
- all 8 child types elaborate in the comparator scope and pass validate_lean_statement;
- the frozen parent type is proved from them plus the two frozen sibling types (10,901 heartbeats; axioms propext, Classical.choice and Quot.sound, plus sorryAx from the stubs only);
- the riskiest child steps compile as prototypes.
