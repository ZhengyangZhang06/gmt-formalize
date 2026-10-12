# Parent-supplied natural-language proof

- Parent DAG node: `root.tangent_structure-a1`
- Child DAG node: `root.tangent_structure-a1.blowup_weighted_tangent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the parent proof, step 5(iii) (Simon Ch. 3, 1.7 and Ch. 4, 1.3: by the change of variables y ↦ λ⁻¹(y − x), the blow-up of μ_V is Simon's ∫_{η_{x,λ}(M)} f(y)θ(x + λy) dHⁿ(y)). No errata apply.

Conventions. E := Ambient n ℓ; Hⁿ := μHE[n]; a = (M, θ) is an admissible pair (M Hⁿ-null-measurable, θ > 0 on M, θ integrable on M ∩ K for compact K); μ := (mk a).weight = pairWeight n M θ = (Hⁿ⌞M).withDensity(ofReal ∘ θ) (definitional for the class of a); η_r := Chapter03.blowUpMap x r, η_r(y) = r⁻¹(y − x). Hypotheses: finrank P = n, and (H) for every f ∈ C_c(E, ℝ): (tⁿ)⁻¹∫ f(t⁻¹(y − x)) dμ(y) → θ(x)·∫_P f dHⁿ as t ↓ 0. Goal: HasWeightedApproximateTangentSpaceAt n M θ x P, i.e. finrank P = n and for every f ∈ C_c(E, ℝ): ∫_{η_r(M)} f(y)·θ(x + r·y) dHⁿ(y) → θ(x)·∫_P f dHⁿ as r ↓ 0.
Results used (pinned; standard axioms only): SimonGMT Chapter04.blowUpHomeomorph (η_r is a homeomorphism for r > 0 with inverse y ↦ x + r·y), Chapter04.hausdorff_blowUp_image (Hⁿ(η_r(S)) = ofReal(r⁻¹)ⁿ·Hⁿ(S) for every S ⊆ E), Chapter04.map_inverse_blowUp_carrier (the image of Hⁿ⌞η_r(M) under η_r⁻¹ is ofReal(r⁻¹)ⁿ·(Hⁿ⌞M), for every set M); Mathlib MeasurableEmbedding.integral_map, integral_smul_measure, integral_withDensity_eq_integral_toReal_smul₀, aestronglyMeasurable_iUnion_iff, ae_restrict_mem₀. (SimonGMT Chapter04.RectifiableVarifold.integral_weighted_blowUp is the same computation for SimonGMT's own varifold structure and can be followed line by line.)

Proof.
1. The first conjunct finrank P = n is a hypothesis.
2. θ is a.e.-strongly measurable for Hⁿ⌞M: M = ⋃_k (M ∩ B_k(0)) with B_k(0) = closedBall 0 k compact, and θ is integrable on each M ∩ B_k(0) (aestronglyMeasurable_iUnion_iff). Hence the density ofReal∘θ is a.e.-measurable and finite, and by integral_withDensity_eq_integral_toReal_smul₀, for every h: E → ℝ,
∫ h dμ = ∫ (ofReal θ(z)).toReal·h(z) d(Hⁿ⌞M)(z) = ∫_M h(z)·θ(z) dHⁿ(z),   (2.1)
because (ofReal θ(z)).toReal = θ(z) for z ∈ M, which holds for Hⁿ⌞M-a.e. z (ae_restrict_mem₀; M null-measurable), and integral_congr_ae.
3. Change of variables. Fix r > 0 and let b := η_r (homeomorphism, inverse b⁻¹(y) = x + r·y). For every g: E → ℝ, apply MeasurableEmbedding.integral_map to the measurable embedding b⁻¹, the measure Hⁿ⌞b(M) and the function z ↦ g(b(z))·θ(z):
∫ g(b(z))θ(z) d(b⁻¹_*(Hⁿ⌞b(M)))(z) = ∫ g(b(b⁻¹(y)))·θ(b⁻¹(y)) d(Hⁿ⌞b(M))(y) = ∫_{b(M)} g(y)·θ(x + r·y) dHⁿ(y).
By Chapter04.map_inverse_blowUp_carrier, b⁻¹_*(Hⁿ⌞b(M)) = ofReal(r⁻¹)ⁿ·(Hⁿ⌞M), and integral_smul_measure turns the left side into (r⁻¹)ⁿ·∫_M g(b(z))θ(z) dHⁿ(z) (toReal of ofReal(r⁻¹)ⁿ is (r⁻¹)ⁿ since r > 0). Combining with (2.1) for h := g∘b:
∫_{η_r(M)} g(y)·θ(x + r·y) dHⁿ(y) = (r⁻¹)ⁿ·∫ g(r⁻¹(z − x)) dμ(z) = (rⁿ)⁻¹·∫ g(r⁻¹(z − x)) dμ(z).   (3.1)
(This identity holds for every r > 0 and every g, with Bochner-integral conventions on both sides: integrability is transported by the same change of variables.)
4. Conclusion. Fix f ∈ C_c(E, ℝ). By (3.1) with g := f, the functions r ↦ ∫_{η_r(M)} f(y)θ(x + r·y) dHⁿ(y) and r ↦ (rⁿ)⁻¹∫ f(r⁻¹(z − x)) dμ(z) agree on (0, ∞), which belongs to 𝓝[>] 0. By (H) the second tends to θ(x)·∫_P f dHⁿ as r ↓ 0, hence so does the first (Tendsto.congr'). Together with step 1 this is HasWeightedApproximateTangentSpaceAt n M θ x P. ∎

Implementation note (not part of the argument): the statement elaborates with the frozen imports; the proof may need additional imports such as Poincare.SimonGMT.Chapter04.WeightedBlowUp (built in the pinned packages); the frozen child types elaborate unchanged with such imports.

## Key steps

1. ∫ h dμ_V = ∫_M hθ dHⁿ for every h (withDensity, θ > 0 on M)
2. Change of variables under η_{x,r}: ∫_{η_{x,r}(M)} g(y)θ(x + ry) dHⁿ(y) = (rⁿ)⁻¹∫ g(r⁻¹(z − x)) dμ_V(z) for all r > 0
3. The two blow-up functions agree on (0, ∞), so the hypothesis gives the weighted tangent limit

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
