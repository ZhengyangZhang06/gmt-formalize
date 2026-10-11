# Parent-supplied natural-language proof

- Parent DAG node: `root.tangent_structure-a1`
- Child DAG node: `root.tangent_structure-a1.blowup_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the parent proof, step 5(iv) (Simon Ch. 3, Remark 1.8(2), written with closed balls and Simon's ωₙ = omega n). No errata apply.

Conventions. n ≥ 1, ℓ ≥ 0; E := Ambient n ℓ; ℝⁿ := EuclideanSpace ℝ (Fin n) with Lebesgue measure Lⁿ := volume; Hⁿ := μHE[n]; B_ρ(z) := closedBall z ρ; ω_n := omega n = Lⁿ(ball 0 1).toReal; μ.real(S) := (μ S).toReal; η_t(y) := t⁻¹(y − x). Hypotheses: μ is a (Borel) measure on E with μ(K) < ∞ for every compact K; finrank P = n; c > 0; and (H) for every f ∈ C_c(E, ℝ), (tⁿ)⁻¹∫ f(η_t(y)) dμ(y) → c·∫_P f dHⁿ as t ↓ 0.
Results used (pinned; standard axioms only): Mathlib InnerProductSpace.euclideanHausdorffMeasure_eq_volume, InnerProductSpace.volume_closedBall, InnerProductSpace.volume_ball, Isometry.map_euclideanHausdorffMeasure (as used in SimonGMT Chapter04.planeMeasure_unit_closedBall), Measure.addHaar_closedBall_eq_addHaar_ball.

Proof.
1. Balls in the plane: Hⁿ(P ∩ B_s(0)) = ω_n·sⁿ for every s ≥ 0, and in particular 0 < ω_n < ∞. Indeed, the inclusion ι: P → E is a linear isometry with range P, so Hⁿ⌞P = ι_*(Hⁿ_P) where Hⁿ_P is the n-dimensional Euclidean Hausdorff measure of the n-dimensional inner product space P (Isometry.map_euclideanHausdorffMeasure); Hⁿ_P = volume_P (InnerProductSpace.euclideanHausdorffMeasure_eq_volume, finrank P = n); ι⁻¹(B_s(0)) is the closed ball of radius s in P; and by InnerProductSpace.volume_closedBall (P is nontrivial since n ≥ 1), volume_P(closedBall 0 s) = ofReal(s)ⁿ·ofReal(√πⁿ/Γ(n/2 + 1)), while by InnerProductSpace.volume_ball for ℝⁿ (finrank n), Lⁿ(ball 0 1) = ofReal(√πⁿ/Γ(n/2 + 1)) — the same constant, whose real value is ω_n ∈ (0, ∞). Hence Hⁿ(P ∩ B_s(0)) = ofReal(ω_n sⁿ). In particular Hⁿ⌞P is finite on bounded sets, so every f ∈ C_c(E, ℝ) is Hⁿ⌞P-integrable.
2. Cut-off functions. For δ ∈ (0, 1) define f_δ⁺(y) := min(1, max(0, (1 + δ − |y|)/δ)) and f_δ⁻(y) := min(1, max(0, (1 − |y|)/δ)). Both are continuous with values in [0, 1] and vanish outside the compact set B_{1+δ}(0), so they belong to C_c(E, ℝ). Moreover f_δ⁺ = 1 on B_1(0) and f_δ⁺ = 0 outside B_{1+δ}(0); f_δ⁻ = 1 on B_{1−δ}(0) and f_δ⁻(y) = 0 whenever |y| ≥ 1. (One may instead use SimonGMT Chapter04.tangentDensityCutoff and a rescaled copy.)
3. Sandwich. Let t > 0. Since |η_t(y)| ≤ 1 ⟺ y ∈ B_t(x), we have for all y: f_δ⁻(η_t(y)) ≤ 1_{B_t(x)}(y) ≤ f_δ⁺(η_t(y)) (if f_δ⁻(η_t(y)) > 0 then |η_t(y)| < 1). All three functions are nonnegative, bounded by 1, Borel, and vanish outside the compact set B_{2t}(x), which has finite μ-measure; integrating,
∫ f_δ⁻∘η_t dμ ≤ μ(B_t(x)) ≤ ∫ f_δ⁺∘η_t dμ,   (3.1)
and μ(B_t(x)) < ∞, so μ.real(B_t(x)) = μ(B_t(x)).toReal satisfies the same inequalities.
4. Limits of the bounds. By (H), (tⁿ)⁻¹∫ f_δ^±∘η_t dμ → c·∫_P f_δ^± dHⁿ. Since 1_{B_{1−δ}(0)} ≤ f_δ⁻ and f_δ⁺ ≤ 1_{B_{1+δ}(0)}, step 1 gives ∫_P f_δ⁻ dHⁿ ≥ Hⁿ(P ∩ B_{1−δ}(0)) = ω_n(1 − δ)ⁿ and ∫_P f_δ⁺ dHⁿ ≤ Hⁿ(P ∩ B_{1+δ}(0)) = ω_n(1 + δ)ⁿ. As c > 0: c·∫_P f_δ⁻ ≥ cω_n(1 − δ)ⁿ and c·∫_P f_δ⁺ ≤ cω_n(1 + δ)ⁿ.
5. Conclusion. Let q(t) := μ.real(B_t(x))/(ω_n·tⁿ) for t > 0. Given ε' > 0 choose δ ∈ (0, 1) with c((1 + δ)ⁿ − 1) < ε'/2 and c(1 − (1 − δ)ⁿ) < ε'/2. By step 4 there is t_0 > 0 such that for 0 < t < t_0: (tⁿ)⁻¹∫ f_δ⁺∘η_t dμ < cω_n(1 + δ)ⁿ + ω_nε'/2 and (tⁿ)⁻¹∫ f_δ⁻∘η_t dμ > cω_n(1 − δ)ⁿ − ω_nε'/2. By (3.1), dividing by ω_n > 0, for 0 < t < t_0: c − ε' < c(1 − δ)ⁿ − ε'/2 < q(t) < c(1 + δ)ⁿ + ε'/2 < c + ε'. Hence q(t) → c as t ↓ 0, i.e. Tendsto (fun ρ ↦ μ.real (closedBall x ρ) / (omega n * ρ ^ n)) (𝓝[>] 0) (𝓝 c). ∎

Implementation note (not part of the argument): the statement elaborates with the frozen imports; the proof may need additional imports such as Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls and Poincare.SimonGMT.Chapter04.TangentDensity (built in the pinned packages); the frozen child types elaborate unchanged with such imports.

## Key steps

1. Hⁿ(P ∩ B_s(0)) = ω_n sⁿ via the isometry of P with an n-dimensional Euclidean space
2. Cut-offs f_δ^± ∈ C_c with f_δ^−(t⁻¹(y − x)) ≤ 1_{B_t(x)}(y) ≤ f_δ^+(t⁻¹(y − x))
3. The limits c∫_P f_δ^± lie between cω_n(1 − δ)ⁿ and cω_n(1 + δ)ⁿ
4. Let δ ↓ 0: μ(B_t(x))/(ω_n tⁿ) → c

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `sha256sum <snapshot>/project/GMT/Ch04/Contract.lean GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean`
- `git -C .lake/packages/simongmt rev-parse HEAD`
- `grep -n 'HasWeightedApproximateTangentSpaceAt\|def CountablyRectifiable\|def blowUpMap' -r .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/`
- `grep -n '^theorem\|^def' Chapter04/{WeightedBlowUp,TangentDensity,FirstVariation,Basic}.lean`
- `grep -rn 'weighted_area_formula_lipschitz_injOn|euclideanHausdorffMeasure_image_le_of_lipschitzOn|ae_dimensionalUpperDensity_eq_zero_outside|measure_toOuterMeasure_isBorelRegular|simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure|exists_isClosed_continuousOn_of_measurable|areaJacobian_comp_eq_parametrization_mul_tangential|def areaJacobianAt|planeMeasure_unit_closedBall|hausdorff_blowUp_image' .lake/packages/simongmt/Poincare/SimonGMT`
- `grep -rn 'continuous.*normDet|measurable_areaJacobianAt' .lake/packages/simongmt/Poincare/SimonGMT`
- `rg -n 'theorem .*[Ll]usin|lusin' <snapshot>/mathlib/Mathlib`
- `rg -n 'measure_eq_zero_iff_ae_notMem|ofReal_le_enorm|Regular.smul|exists_isClosed_sdiff_lt' <snapshot>/mathlib/Mathlib`
- `grep -rn 'InnerProductSpace.volume_closedBall|hasDerivAt_integral_of_dominated_loc_of_deriv_le|isSymmSndFDerivAt|inverse_continuousAt|normDet_comp|def normDet|euclideanHausdorffMeasure_eq_volume' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem integral_withDensity_eq_integral_toReal_smul₀' <snapshot>/mathlib/Mathlib`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/ch04-ts-decomp/olean/GMT/Ch04/Submission.olean`
- `LEAN_PATH=$(lake env printenv LEAN_PATH):/tmp/ch04-ts-decomp/olean lean /tmp/ch04-ts-decomp/{T0,T1,T5}.lean (statement-scope availability of LinearMap.range/normDet/adjoint; instance #synth)`
- `python3 /tmp/ch04-ts-decomp/scripts/gen.py (verifier gmt-compare.child_modules + lean_contract.validate_lean_statement); lean /tmp/ch04-ts-decomp/gen/Challenge_*.lean`
- `lean /tmp/ch04-ts-decomp/T6.lean (parent assembly from sorry'd children and sibling)`
- `lake env lean /tmp/ch04-ts-decomp/Axioms.lean (#print axioms of the cited lemmas)`
- `lean /tmp/ch04-ts-decomp/gen2/WithImports.lean /tmp/ch04-ts-decomp/gen2/Synth.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-lipschitz-pieces-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/WeightedBlowUp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/MetricSpace/CantorScheme.lean`
- `/tmp/ch04-ts-decomp/T6.lean`
- `/tmp/ch04-ts-decomp/Axioms.lean`
- `/tmp/ch04-ts-decomp/gen2/WithImports.lean`

Contract and pinned packages:
- The snapshot contract (sha256 6e58e5dd…0f4770b) is byte-identical to the workspace Contract.lean and Submission.lean.
- SimonGMT is at the pinned revision 2b3663083f3fe399b6296fb8eaee52169170e197.

What can appear in a child type:
- In the frozen statement scope (`import GMT.Ch04.Submission` plus the contract opens), LinearMap.normDet, ContinuousLinearMap.adjoint and LinearMap.adjoint are unknown constants. So no child type mentions Jacobians or adjoints.
- `LinearMap.range (fderiv ℝ F w)` does not elaborate; `LinearMap.range (fderiv ℝ F w).toLinearMap` does, and the child types use that form.

Lusin's theorem:
- The snapshot Mathlib has no Lusin theorem: `rg 'theorem .*[Ll]usin'` only hits a docstring in Topology/MetricSpace/CantorScheme.lean.
- SimonGMT Chapter01.exists_isClosed_continuousOn_of_measurable is cited instead.

Cited library results — each exists with the stated meaning, and #print axioms shows only propext, Classical.choice, Quot.sound:
- SimonGMT Chapter04: map_inverse_blowUp_carrier, hausdorff_blowUp_image, planeMeasure_unit_closedBall, tangentDensityCutoff_eq_one, RectifiableVarifold.integral_weighted_blowUp.
- SimonGMT Chapter02: continuous_normDet, measurable_areaJacobianAt, weighted_area_formula_lipschitz_injOn, euclideanHausdorffMeasure_image_le_of_lipschitzOn, simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure, areaJacobian_comp_eq_parametrization_mul_tangential.
- SimonGMT Chapter01: exists_isClosed_continuousOn_of_measurable, ae_dimensionalUpperDensity_eq_zero_outside, measure_toOuterMeasure_isBorelRegular.
- SimonGMT Chapter03: regular_euclideanHausdorffMeasure_restrict_submodule, support_euclideanHausdorffMeasure_restrict_submodule.
- Mathlib: Besicovitch.ae_tendsto_measure_inter_div, Measure.ext_of_integral_eq_on_compactlySupported, hasDerivAt_integral_of_dominated_loc_of_deriv_le, ContDiffAt.isSymmSndFDerivAt, NormedRing.inverse_continuousAt, InnerProductSpace.volume_closedBall, LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume, LinearMap.normDet_sq_eq_det_gram, LinearMap.normDet_comp, MeasurableSet.exists_isClosed_sdiff_lt, Measure.Regular.smul.
- integral_withDensity_eq_integral_toReal_smul₀ is a root-namespace lemma in MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean.

Elaboration checks:
- All seven child types pass the verifier's validate_lean_statement.
- Each compiles as a comparator-generated NodeChallenge file, with only the expected sorry warning.
- They still elaborate when the implementation imports are added, with the same instances; for example, volume on EuclideanSpace stays measureSpaceOfInnerProductSpace.

Parent assembly:
- T6.lean declares the seven children and the sibling rectifiable_lipschitz_piece_cover as sorry'd theorems, then gives a full proof of Submission.tangent_structure_first_variation with exactly the frozen type.
- It compiles with only the eight sorry warnings.
