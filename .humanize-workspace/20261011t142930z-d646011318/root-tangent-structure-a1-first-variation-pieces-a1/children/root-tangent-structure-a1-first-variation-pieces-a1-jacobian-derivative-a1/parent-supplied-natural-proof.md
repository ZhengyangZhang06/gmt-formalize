# Parent-supplied natural-language proof

- Parent DAG node: `root.tangent_structure-a1.first_variation_pieces-a1`
- Child DAG node: `root.tangent_structure-a1.first_variation_pieces-a1.jacobian_derivative-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the parent proof, steps 3.2–3.3 (Jacobi's formula; Simon Ch. 2, 5.2–5.3 and Ch. 4, 2.2), carried out on the N×N matrix S_P(Λ) of the parent's conventions, whose determinant is J^P(Λ)², instead of on the n×n Gram matrix of an orthonormal basis of P (the same determinant). Working with S_P removes the need for dim P = n and for a choice of basis of P. No errata apply.

Notation. E := EuclideanSpace ℝ (Fin N); e_i := EuclideanSpace.single i 1 (i ∈ Fin N), an orthonormal basis of E (EuclideanSpace.basisFun); for ξ ∈ ℝ^N, |ξ|² := Σ_i ξ_i². p := P.starProjection is the orthogonal projection onto P, q := I − p, so q v = v − p v. Standard facts used: p is self-adjoint and idempotent, ‖p v‖ ≤ ‖v‖, and q v ⊥ P; consequently ⟨p u, p v⟩ = ⟨p u, v⟩ = ⟨u, p v⟩, ⟨q u, q v⟩ = ⟨u, v⟩ − ⟨p u, p v⟩, ‖q v‖ ≤ ‖v‖ and ‖p v‖² + ‖q v‖² = ‖v‖². For t ∈ ℝ put
S(t) := [⟨Λ(t)p e_i, Λ(t)p e_j⟩ + ⟨q e_i, q e_j⟩]_{i,j ∈ Fin N},
so the hypothesis on J says J(t) = (det S(t))^{1/2} (Real.sqrt) for every t.

0. Choice of C. Let B₁ := max(B, 1) ≥ 1, M₀ := B₁² + 1, and
C := (N!·M₀^N)^{1/2} + N!·N·B₁^{N+2}·M₀^{N−1}
(N − 1 in ℕ; the second summand is 0 if N = 0). C depends only on N and B. Now fix P, Λ, Λ', J, δ satisfying the hypotheses, and let t ∈ (−δ, δ) unless stated otherwise. From the hypotheses, ‖Λ(t)‖ ≤ B ≤ B₁, ‖Λ'(t)‖ ≤ B₁, and ‖v‖ ≤ B‖Λ(t)v‖ ≤ B₁‖Λ(t)v‖ for all v (as ‖Λ(t)v‖ ≥ 0).

1. The quadratic form of S(t). S(t) is symmetric (the real inner product is symmetric). For ξ ∈ ℝ^N let v := Σ_i ξ_i e_i, so ‖v‖² = |ξ|². By bilinearity, Σ_{i,j} ξ_i S(t)_{ij} ξ_j = ‖Λ(t)(p v)‖² + ‖q v‖². Applying the lower bound to p v gives ‖Λ(t)(p v)‖² ≥ B₁^{−2}‖p v‖², and ‖q v‖² ≥ B₁^{−2}‖q v‖² because B₁ ≥ 1. Hence
ξᵀS(t)ξ ≥ B₁^{−2}(‖p v‖² + ‖q v‖²) = B₁^{−2}|ξ|².

2. Bounds for det S(t). (a) Lower bound: S(t) is real symmetric, so by the spectral theorem it has real eigenvalues λ_1, …, λ_N with an orthonormal basis of eigenvectors, and det S(t) = Π_k λ_k (Matrix.IsHermitian.det_eq_prod_eigenvalues). For an eigenvector ξ ≠ 0 with eigenvalue λ, step 1 gives λ|ξ|² = ξᵀS(t)ξ ≥ B₁^{−2}|ξ|², so λ ≥ B₁^{−2}. Hence det S(t) ≥ B₁^{−2N} > 0. (b) Upper bound: |S(t)_{ij}| ≤ ‖Λ(t)‖²‖p e_i‖‖p e_j‖ + ‖q e_i‖‖q e_j‖ ≤ B₁² + 1 = M₀. By the Leibniz formula det S(t) = Σ_{σ ∈ Perm(Fin N)} sgn(σ) Π_k S(t)_{σ(k) k} (Matrix.det_apply), |det S(t)| ≤ N!·M₀^N.

3. Bound on J. J(t) = (det S(t))^{1/2} ≥ 0 and, by 2(b) and monotonicity of the square root, J(t) ≤ (N!·M₀^N)^{1/2} ≤ C.

4. Derivatives of the entries. Since Λ has derivative Λ'(t) at t and, for fixed w ∈ E, evaluation L ↦ L w is continuous linear, s ↦ Λ(s)w has derivative Λ'(t)w at t. By the product rule for the inner product (HasDerivAt.inner), s ↦ ⟨Λ(s)p e_i, Λ(s)p e_j⟩ has derivative ⟨Λ'(t)p e_i, Λ(t)p e_j⟩ + ⟨Λ(t)p e_i, Λ'(t)p e_j⟩ at t, and ⟨q e_i, q e_j⟩ does not depend on s. So each entry s ↦ S(s)_{ij} has derivative
S'(t)_{ij} := ⟨Λ'(t)p e_i, Λ(t)p e_j⟩ + ⟨Λ(t)p e_i, Λ'(t)p e_j⟩ at t, with |S'(t)_{ij}| ≤ 2B₁².

5. Derivative of det S. By the Leibniz formula, the product rule for finite products (HasDerivAt.finsetProd) and linearity, s ↦ det S(s) has derivative
D(t) := Σ_σ sgn(σ) Σ_k S'(t)_{σ(k) k} Π_{i ≠ k} S(t)_{σ(i) i}
at t. By 2(b) and step 4, |D(t)| ≤ N!·N·2B₁²·M₀^{N−1}.

6. Derivative of J and its bound. Since det S(t) > 0 (2(a)), HasDerivAt.sqrt gives that J = (s ↦ (det S(s))^{1/2}) has derivative d := D(t)/(2(det S(t))^{1/2}) at t. Using (det S(t))^{1/2} ≥ B₁^{−N} (2(a)),
|d| ≤ N!·N·2B₁²·M₀^{N−1}·B₁^N/2 = N!·N·B₁^{N+2}·M₀^{N−1} ≤ C.
Together with step 3 this proves the first conclusion: for every t ∈ (−δ, δ), 0 ≤ J(t) ≤ C and ∃ d, HasDerivAt J d t ∧ |d| ≤ C.

7. The value at t = 0. Note 0 ∈ (−δ, δ) since δ > 0. As Λ(0) = I, S(0)_{ij} = ⟨p e_i, p e_j⟩ + ⟨q e_i, q e_j⟩ = ⟨e_i, e_j⟩ = δ_{ij}, so S(0) = I, det S(0) = 1 and J(0) = 1. In D(0), Π_{i≠k} S(0)_{σ(i) i} = Π_{i≠k} δ_{σ(i) i} equals 1 if σ fixes every i ≠ k and 0 otherwise; a permutation fixing every i ≠ k also fixes k, so only σ = id contributes and D(0) = Σ_k S'(0)_{kk}. With L := Λ'(0) and Λ(0) = I, S'(0)_{kk} = ⟨L p e_k, p e_k⟩ + ⟨p e_k, L p e_k⟩ = 2⟨L p e_k, p e_k⟩. By step 6 at t = 0, J has derivative D(0)/(2·1) = Σ_k ⟨L p e_k, p e_k⟩ at 0.

8. Identification with the trace. By self-adjointness of p and symmetry of the real inner product, ⟨L p e_k, p e_k⟩ = ⟨e_k, (p ∘ L ∘ p) e_k⟩, so Σ_k ⟨L p e_k, p e_k⟩ = trace(p ∘ L ∘ p) (LinearMap.trace_eq_sum_inner with the orthonormal basis EuclideanSpace.basisFun). By the cyclicity of the trace (LinearMap.trace_mul_comm with the factors p and L ∘ p) and p ∘ p = p, trace(p ∘ L ∘ p) = trace(L ∘ p ∘ p) = trace(L ∘ p). Hence J has derivative LinearMap.trace ℝ E ((Λ'(0)).toLinearMap ∘ₗ p.toLinearMap) at 0, which is the second conclusion. ∎

## Key steps

1. ξᵀS(t)ξ = ‖Λ(t)pv‖² + ‖qv‖² ≥ B₁⁻²|ξ|² with B₁ = max(B, 1), so det S(t) ≥ B₁^{−2N} > 0 (eigenvalues), and |det S(t)| ≤ N!(B₁² + 1)^N (Leibniz)
2. Entries of S are differentiable with |S'_{ij}| ≤ 2B₁² (product rule for inner products)
3. Leibniz formula and product rule give the derivative of det S with an explicit bound; the chain rule for the square root bounds J' by C
4. At t = 0, S(0) = I, so (det S)'(0) = trace S'(0) = 2Σ_k⟨Λ'(0)pe_k, pe_k⟩ and J'(0) = Σ_k⟨Λ'(0)pe_k, pe_k⟩
5. Σ_k⟨Λ'(0)pe_k, pe_k⟩ = trace(p∘Λ'(0)∘p) = trace(Λ'(0)∘p) by trace_eq_sum_inner, cyclicity and p² = p

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `sha256sum GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean <snapshot>/project/GMT/Ch04/Contract.lean`
- `git -C .lake/packages/simongmt rev-parse HEAD`
- `git show 2cce809724fc09db16dc21873e5f9cd1ee6e2dfa:GMT/Ch04/Submission.lean | grep -n '^import\|^theorem'`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/ch04-fvp/olean/GMT/Ch04/Submission.olean`
- `lean /tmp/ch04-fvp/T0.lean (#check Matrix.det, Matrix.of, Matrix.gram, EuclideanSpace.single, LinearMap.trace, Submodule.starProjection, LinearMap.normDet, ContinuousLinearMap.adjoint in the frozen scope)`
- `grep -n 'theorem\|lemma\|def' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `grep -rn 'weighted_area_formula_lipschitz_injOn|euclideanHausdorffMeasure_image_le_of_lipschitzOn|def areaJacobianAt|continuous_normDet|measurable_areaJacobianAt' .lake/packages/simongmt/Poincare/SimonGMT`
- `grep -rn 'MeasurableSet.image_of_continuousOn_injOn|integral_withDensity_eq_integral_toReal_smul₀|restrict_withDensity|hasDerivAt_integral_of_dominated_loc_of_deriv_le|ContDiffAt.isSymmSndFDerivAt|inverse_continuousAt|lipschitzWith_of_nnnorm_fderiv_le|trace_eq_sum_inner|HasDerivAt.finsetProd|HasDerivAt.inner|HasDerivAt.sqrt|det_eq_prod_eigenvalues|lintegral_iUnion₀|ofReal_integral_eq_lintegral_ofReal|setIntegral_eq_integral_of_forall_compl_eq_zero|exists_measurable_superset_ae_eq|det_apply|fderiv_comp' .lake/packages/mathlib/Mathlib`
- `grep -rn 'continuous_matrix|Continuous.matrix_det|def coeLM|LinearMap.continuous_of_finiteDimensional|Continuous.clm_apply|Continuous.inner' .lake/packages/mathlib/Mathlib`
- `grep -n '^theorem\|^def' .lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DeformationFamily.lean .lake/packages/simongmt/Poincare/SimonGMT/Chapter08/JacobianBounds.lean`
- `python3 -I /tmp/ch04-fvp/scripts/gen.py (verifier gmt-compare.child_modules + lean_contract.validate_lean_statement); lean /tmp/ch04-fvp/gen/Challenge_*.lean`
- `lean /tmp/ch04-fvp/WithImports.lean (child types with the implementation imports added)`
- `lean /tmp/ch04-fvp/Assembly.lean (parent with its frozen type proved from the four sorry'd children)`
- `python3 scan of dag.json for lean_name collisions (ts_fv_*) and for nodes mentioning IsCompactVariation/imageMass`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-first-variation-pieces-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DeformationFamily.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/JacobianBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Topology/Instances/Matrix.lean`
- `/tmp/ch04-fvp/Assembly.lean`
- `/tmp/ch04-fvp/WithImports.lean`
- `/tmp/ch04-fvp/gen/Challenge_ts_fv_compact_variation_bounds.lean`
- `/tmp/ch04-fvp/gen/Challenge_ts_fv_image_mass_area_formula.lean`
- `/tmp/ch04-fvp/gen/Challenge_ts_fv_tangential_jacobian_hasDerivAt.lean`
- `/tmp/ch04-fvp/gen/Challenge_ts_fv_hasDerivAt_of_weighted_jacobian.lean`

Contract and pinned state:
- The snapshot contract (sha256 6e58e5dd…0f4770b) is byte-identical to the workspace Contract.lean and Submission.lean, and to the proof-base Submission at 2cce8097.
- SimonGMT is at the pinned revision 2b366308; Mathlib is at 25730c7c.

What child types can mention:
- In the frozen scope (`import GMT.Ch04.Submission` plus the contract opens), Matrix.det, Matrix.of, EuclideanSpace.single, LinearMap.trace and Submodule.starProjection are available.
- LinearMap.normDet, ContinuousLinearMap.adjoint and Matrix.gram are unknown constants. So no child type mentions normDet or adjoints: the tangential Jacobian is written as √det of the standard-basis matrix [⟪Λpe_i, Λpe_j⟫ + ⟪qe_i, qe_j⟫].

Cited results, each found with the stated meaning:
- SimonGMT Chapter02:
  - weighted_area_formula_lipschitz_injOn (global LipschitzWith, MeasurableSet source, InjOn, arbitrary non-measurable weight; target measure μHE[finrank]);
  - euclideanHausdorffMeasure_image_le_of_lipschitzOn (μHE[n](f '' A) ≤ K^n μHE[n] A);
  - areaJacobianAt = normDet ∘ fderiv.
- SimonGMT Chapter08.Varifold.hasDerivAt_familySpatialDerivative, with familySpatialDerivative_eq_fderiv and initialVelocity_eq_deriv. This gives ∂_t Dφ_t|_{t=0} = DX directly; the reviewer compiled it.
- Mathlib:
  - normDet: LinearMap.normDet_sq_eq_det_gram, LinearMap.normDet_comp;
  - measure theory: MeasurableSet.image_of_continuousOn_injOn, NullMeasurableSet.exists_measurable_superset_ae_eq / exists_measurable_subset_ae_eq, lintegral_iUnion₀, restrict_withDensity, integral_withDensity_eq_integral_toReal_smul₀ (no integrability of g needed), ofReal_integral_eq_lintegral_ofReal, setIntegral_eq_integral_of_forall_compl_eq_zero;
  - calculus: hasDerivAt_integral_of_dominated_loc_of_deriv_le, ContDiffAt.isSymmSndFDerivAt (minSmoothness ℝ 2 ≤ n), lipschitzWith_of_nnnorm_fderiv_le, HasDerivAt.inner, HasDerivAt.finsetProd (finset_prod is deprecated), HasDerivAt.sqrt;
  - algebra: NormedRing.inverse_continuousAt, LinearMap.trace_eq_sum_inner, Matrix.det_apply, Matrix.IsHermitian.det_eq_prod_eigenvalues;
  - continuity used by the assembly: continuous_matrix, Continuous.matrix_det, ContinuousLinearMap.coeLM, LinearMap.continuous_of_finiteDimensional.

Elaboration and assembly:
- All four child types pass validate_lean_statement.
- They compile as comparator-generated NodeChallenge files, with only the sorry warning.
- They still elaborate when the implementation imports are added.
- Assembly.lean proves Submission.ts_first_variation_of_pieces with exactly the frozen type from the four sorry'd children; the only diagnostics are the four child sorry warnings.

Name collisions: none.
- No ts_fv_* name appears in dag.json or in the pinned packages.
- The accepted compactVariation_velocity_isTestField in another branch overlaps only parts (a) and (b) of child A, under a different name and type, and it is not in this node's proof base.
