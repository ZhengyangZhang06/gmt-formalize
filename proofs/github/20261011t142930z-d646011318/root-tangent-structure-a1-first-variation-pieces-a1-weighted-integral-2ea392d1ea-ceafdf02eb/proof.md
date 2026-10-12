# Parent-supplied natural-language proof

- Parent DAG node: `root.tangent_structure-a1.first_variation_pieces-a1`
- Child DAG node: `root.tangent_structure-a1.first_variation_pieces-a1.weighted_integral_derivative-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the parent proof, step 4 ("Conclusion", 4.1–4.4: Simon Ch. 4, 2.2, differentiation under the integral sign), with the Jacobian J_t(x) replaced by an arbitrary function J satisfying the bounds established in the parent's steps 3.3–3.4. No errata apply.

Notation. E := Ambient n ℓ, Hⁿ := μHE[n], a = (M, θ) with IsRectifiablePair: M is Hⁿ-null-measurable, θ(x) > 0 for x ∈ M, and θ is Hⁿ-integrable on M ∩ K' for every compact K'. μ := (mk a).weight. Since K is compact it is closed, hence Borel. Let ν := Hⁿ⌞(M ∩ K) = (μHE[n]).restrict (a.M ∩ K), and I := (−δ, δ), an open neighbourhood of 0 (δ > 0).

1. Preliminaries on ν.
(a) θ is ν-integrable (IsRectifiablePair.locallyIntegrable applied to K); in particular θ is ν-a.e. strongly measurable.
(b) M ∩ K is Hⁿ-null-measurable, so ν-a.e. x lies in M ∩ K (ae_restrict_mem₀); hence θ(x) > 0 for ν-a.e. x.
(c) ν = (Hⁿ⌞M)⌞K (Measure.restrict_restrict, K measurable, and K ∩ M = M ∩ K). Hence a statement of the form "for Hⁿ⌞M-a.e. x, x ∈ K → R(x)" implies "for ν-a.e. x, R(x)" (ae_restrict_iff', or ae_restrict_of_ae with the implication). Applied to the pointwise hypothesis: for ν-a.e. x, J'(0, x) = g(x) and, for all t ∈ I, 0 ≤ J(t, x) ≤ B, s ↦ J(s, x) has derivative J'(t, x) at t, and |J'(t, x)| ≤ B.
(d) ν ≤ Hⁿ⌞M (Measure.restrict_mono on M ∩ K ⊆ M), so every function that is Hⁿ⌞M-a.e. strongly measurable is ν-a.e. strongly measurable (AEStronglyMeasurable.mono_measure). This applies to J(t, ·) for t ∈ I and to g.

2. The integrands. For t ∈ I let F(t, x) := θ(x)·J(t, x) and F'(t, x) := θ(x)·J'(t, x). By 1(a), 1(d), F(t, ·) is ν-a.e. strongly measurable (product). By 1(b), 1(c), for ν-a.e. x: 0 ≤ F(t, x) ≤ B·θ(x) for all t ∈ I. Since B·θ is ν-integrable, F(t, ·) is ν-integrable (Integrable.mono' with the bound B·θ). As F(t, ·) ≥ 0 ν-a.e.,
m(t) = ∫⁻ ofReal(F(t, x)) dν(x) = ofReal(∫ F(t, x) dν(x)) (ofReal_integral_eq_lintegral_ofReal),
and since ∫ F(t, ·) dν ≥ 0 (integral_nonneg_of_ae), (m t).toReal = ∫ F(t, x) dν(x) for every t ∈ I (ENNReal.toReal_ofReal).

3. Differentiation under the integral sign. Apply hasDerivAt_integral_of_dominated_loc_of_deriv_le with x₀ := 0, the neighbourhood s := I of 0, the functions F, F', and bound(x) := B·θ(x):
– for every t in the neighbourhood I of 0, F(t, ·) is ν-a.e. strongly measurable (step 2);
– F(0, ·) is ν-integrable (step 2 with t = 0);
– F'(0, ·) is ν-a.e. strongly measurable: by 1(c), F'(0, x) = θ(x)·g(x) for ν-a.e. x, and θ·g is ν-a.e. strongly measurable by 1(a), 1(d) (AEStronglyMeasurable.congr);
– for ν-a.e. x and all t ∈ I: |F'(t, x)| = θ(x)·|J'(t, x)| ≤ B·θ(x) (θ(x) > 0 by 1(b), bound by 1(c));
– bound = B·θ is ν-integrable (1(a));
– for ν-a.e. x and all t ∈ I: s ↦ F(s, x) = θ(x)·J(s, x) has derivative θ(x)·J'(t, x) = F'(t, x) at t (HasDerivAt.const_mul and 1(c)).
The lemma gives HasDerivAt (t ↦ ∫ F(t, x) dν(x)) (∫ F'(0, x) dν(x)) 0.

4. The derivative value. By 1(c), F'(0, ·) = θ·g ν-a.e., so ∫ F'(0, x) dν = ∫ θ(x)g(x) dν(x) (integral_congr_ae). Now compute ∫ g dμ. By definition of the weight on the class mk a, μ = pairWeight n M θ = (Hⁿ⌞M).withDensity(ρ) with ρ(x) := ofReal(θ(x)) (Quot.lift on Quot.mk reduces definitionally). Since g = 0 off K, ∫ g dμ = ∫_K g dμ (setIntegral_eq_integral_of_forall_compl_eq_zero). Further μ⌞K = ((Hⁿ⌞M)⌞K).withDensity(ρ) = ν.withDensity(ρ) (restrict_withDensity, K measurable, and 1(c)). The density ρ is ν-a.e. measurable (θ is, by 1(a); ENNReal.ofReal is measurable) and ρ(x) < ∞ for all x, so integral_withDensity_eq_integral_toReal_smul₀ (no integrability of g is needed) gives
∫_K g dμ = ∫ (ofReal θ(x)).toReal·g(x) dν(x) = ∫ θ(x)g(x) dν(x),
because (ofReal θ(x)).toReal = θ(x) whenever θ(x) ≥ 0, which holds ν-a.e. by 1(b). Hence ∫ F'(0, x) dν = ∫ g dμ.

5. Conclusion. By step 2 the functions t ↦ (m t).toReal and t ↦ ∫ F(t, x) dν(x) agree on the neighbourhood I of 0, so by step 3, step 4 and HasDerivAt.congr_of_eventuallyEq,
HasDerivAt (t ↦ (m t).toReal) (∫ g dμ) 0, i.e. HasDerivAt (fun t ↦ (m t).toReal) (∫ x, g x ∂(mk a).weight) 0. ∎

## Key steps

1. Work with ν := Hⁿ⌞(M ∩ K) = (Hⁿ⌞M)⌞K: θ is ν-integrable and positive ν-a.e., and the hypotheses transfer to ν
2. θJ(t, ·) is integrable and nonnegative, so (m t).toReal = ∫ θJ(t, ·) dν for |t| < δ
3. hasDerivAt_integral_of_dominated_loc_of_deriv_le with bound Bθ gives derivative ∫ θJ'(0, ·) dν = ∫ θg dν at 0
4. μ_V⌞K = ν.withDensity(ofReal ∘ θ) and g = 0 off K, so ∫ g dμ_V = ∫ θg dν (integral_withDensity_eq_integral_toReal_smul₀)
5. Transfer the derivative to t ↦ (m t).toReal by HasDerivAt.congr_of_eventuallyEq

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
