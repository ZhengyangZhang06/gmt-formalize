# Parent-supplied natural-language proof

- Parent DAG node: `root.coarea_and_slices-a1`
- Child DAG node: `root.coarea_and_slices-a1.gluing-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Parts 1.4 and 1.6 (decomposition and summation; Simon Ch. 3, p. 76-77, lines 376-389 and 426-433, with the erratum of (2.9): the domain is A on both sides). The parent's pieces A_{α,i} are replaced by Borel pieces; all null parts are handled by (NS) (the parent's 0.2).
1. (Borel representatives.) Choose a Borel g' with g = g' Hⁿ⌞A-a.e. (AEMeasurable.measurable_mk) and a Borel A' ⊆ A with A' = A Hⁿ-a.e. (NullMeasurableSet.exists_measurable_subset_ae_eq).
2. (Disjoint Borel pieces.) T_j := (A' ∩ S_j) \ ⋃_{i<j} S_i. The T_j are Borel, pairwise disjoint, T_j ⊆ S_j, and A'' := ⋃_j T_j = A' ∩ ⋃_j S_j ⊆ A ⊆ M ⊆ U. Z := A \ A'' ⊆ (A \ A') ∪ (M \ ⋃_j S_j) has Hⁿ(Z) = 0 by step 1 and (Cov).
3. (Left side.) Since g = g' Hⁿ⌞A-a.e., ∫_A g·w dHⁿ = ∫_A g'·w dHⁿ. Since A'' ⊆ A and Hⁿ(A \ A'') = 0, A = A'' Hⁿ-a.e., so Hⁿ⌞A = Hⁿ⌞A'' (Measure.restrict_congr_set) and ∫_A g'·w = ∫_{A''} g'·w = Σ_j ∫_{T_j} g'·w dHⁿ by countable additivity over the disjoint Borel sets T_j, valid for an arbitrary integrand (lintegral_iUnion).
4. (Pieces.) By (Loc) with B := T_j and φ := g': ∫_{T_j} g'·w dHⁿ = ∫ F_j dLᵐ with F_j(y) := ∫_{T_j∩f⁻¹{y}} g' dHᵏ, F_j a.e.-measurable. By monotone convergence for series (lintegral_tsum), Σ_j ∫ F_j dLᵐ = ∫ Σ_j F_j dLᵐ.
5. (Slices of the pieces are Borel.) For every y, U ∩ f⁻¹{y} is Borel: f is continuous on the open U, so U ∩ f⁻¹(ℝᵐ \ {y}) is open (ContinuousOn.isOpen_inter_preimage) and U ∩ f⁻¹{y} = U \ (U ∩ f⁻¹(ℝᵐ \ {y})). Since T_j ⊆ U, T_j ∩ f⁻¹{y} = T_j ∩ (U ∩ f⁻¹{y}) is Borel; these sets are pairwise disjoint with union A'' ∩ f⁻¹{y}. Hence Σ_j F_j(y) = ∫_{A''∩f⁻¹{y}} g' dHᵏ for every y (lintegral_iUnion).
6. (Exceptional slices.) Let Y := {x ∈ A : g(x) ≠ g'(x)}; then Hⁿ(Y) ≤ (Hⁿ⌞A)({g ≠ g'}) = 0 (Measure.le_restrict_apply). Z, Y ⊆ M, so by (NS), for Lᵐ-a.e. y both Hᵏ(Z ∩ f⁻¹{y}) = 0 and Hᵏ(Y ∩ f⁻¹{y}) = 0. For such y: A ∩ f⁻¹{y} and A'' ∩ f⁻¹{y} differ by a subset of Z ∩ f⁻¹{y}, so Hᵏ⌞(A∩f⁻¹{y}) = Hᵏ⌞(A''∩f⁻¹{y}); and since A''∩f⁻¹{y} is Borel, the restricted measure of {g ≠ g'} is Hᵏ({g ≠ g'} ∩ A'' ∩ f⁻¹{y}) ≤ Hᵏ(Y ∩ f⁻¹{y}) = 0, i.e. g = g' Hᵏ-a.e. there. Therefore ∫_{A''∩f⁻¹{y}} g' dHᵏ = ∫_{A∩f⁻¹{y}} g dHᵏ for Lᵐ-a.e. y.
7. (Conclusion.) By steps 3-6, ∫_A g·w dHⁿ = Σ_j ∫ F_j = ∫ Σ_j F_j = ∫_{ℝᵐ}∫_{A∩f⁻¹{y}} g dHᵏ dLᵐ(y) (lintegral_congr_ae). ∎

## Key steps

1. Replace g by a Borel g' and A by a Borel A' ⊆ A, each up to Hⁿ-null sets.
2. Disjointify the Borel pieces A' ∩ S_j; the remainder Z of A is Hⁿ-null by (Cov).
3. Left side: countable additivity of the set integral over the disjoint Borel pieces; apply (Loc) to each piece.
4. Right side: monotone convergence; for every y the slices of the pieces are disjoint Borel sets (f continuous on open U).
5. (NS) makes the null remainder Z and the set {g ≠ g'} invisible on Lᵐ-a.e. slice.

## Reference use

### local-project

Queries:
- `rg -n "^def CoareaFormula|^def SlicesAreRectifiable|^noncomputable def coareaJacobian|^noncomputable def approxTangentPlane|^def HasTangentialDifferentialAt" project/GMT/Ch03/Contract.lean`
- `rg -l -i "coarea" mathlib/Mathlib`
- `rg -l -i "\bsard\b" mathlib/Mathlib`
- `rg -n "theorem MeasurableSet.image_of_continuousOn_injOn|theorem ContinuousOn.measurableEmbedding|theorem Measurable.measurableEmbedding" mathlib/Mathlib`
- `rg -n "theorem lintegral_image_eq_lintegral_abs_det_fderiv_mul" mathlib/Mathlib`
- `rg -n "^theorem lintegral_iUnion |^theorem lintegral_tsum|^theorem lintegral_liminf_le" mathlib/Mathlib`
- `rg -n "theorem HasLineDerivAt.unique|theorem lintegral_withDensity_eq_lintegral_mul_non_measurable|theorem isOpen_iUnion_countable" mathlib/Mathlib`
- `grep -n "theorem hausdorffMeasure_le_liminf_sum|theorem hausdorffMeasure_le_liminf_tsum" mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `grep -n "def MeasureTheory.Measure.euclideanHausdorffMeasure|euclideanHausdorffMeasure_zero" mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `grep -n "^theorem|^noncomputable def" mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean (normDet, normDet_comp, normDet_of_subsingleton, normDet_eq_zero_iff_ker_ne_bot, normDet_sq)`
- `grep -n "toOpenPartialHomeomorph|implicitToOpenPartialHomeomorph|contDiffAt_symm" mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean mathlib/Mathlib/Analysis/Calculus/Implicit.lean mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `grep -rn "ContDiffOn.exists_lipschitzOnWith|LipschitzOnWith.extend_pi|measurableSet_of_differentiableAt|measurable_fderiv|LipschitzWith.ae_differentiableAt|WithLp.volume_preserving_toLp|measurableSet_eq_fun|AEMeasurable.ennreal_tsum|Measurable.lintegral_prod_right'" mathlib/Mathlib`
- `grep -n "^theorem|^def|^noncomputable def" (SimonGMT) Chapter03/Rectifiable.lean Chapter03/SubmanifoldCover.lean Chapter02/AreaDomain.lean Chapter02/CoareaLinear.lean Chapter02/CoareaLinearAlgebra.lean Chapter02/CoareaProjection.lean`
- `grep -rn "countablyRectifiable_image_contDiffOn_open|map_withDensity_areaJacobian_eq|weighted_area_formula_volume_of_injective_derivative|euclideanHausdorffMeasure_image_le_of_lipschitzOn|exists_lipschitz_extension_finiteDimensional|ae_fderivWithin_eq_of_lipschitz_extension|HasWeightedApproximateTangentSpaceAt.unique" Poincare/SimonGMT`
- `lake env lean on the ten frozen child types in the comparator's replayed Contract scope (gmt-compare.py contract_scope + lean_contract.validate_lean_statement), and on a parent-assembly test file with the ten child types and the four sibling frozen types as stubs`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/Implicit.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinearAlgebra.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaProjection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`

Snapshot project d09bc8a / Mathlib 25730c7c plus the pinned simongmt package. No match: Mathlib has no co-area formula (rg 'coarea': no file) and only a fixed-dimension Sard lemma (MeasureTheory/Function/Jacobian.lean), no C¹ Sard-type slice theorem and no countable rectifiability; SimonGMT has no nonlinear co-area formula. Hence the C¹ critical-slice estimate, the C¹ parametric co-area formula and the level-set rectifiability are supplied as children. Available and cited in the children: SimonGMT linear/projection co-area (CoareaLinear.lean, CoareaProjection.lean), Lipschitz and injective area formulas (AreaDomain.lean weighted_area_formula_lipschitzOn_fiberSum, injective_area_formula_lipschitzOn, ae_fderivWithin_eq_of_lipschitz_extension, exists_lipschitz_extension_finiteDimensional; WeightedArea.lean map_withDensity_areaJacobian_eq and weighted_area_formula_volume_of_injective_derivative for arbitrary integrands), Lipschitz image bound euclideanHausdorffMeasure_image_le_of_lipschitzOn, countablyRectifiable_image_contDiffOn_open / _iUnion / _of_measure_zero / CountablyRectifiable.mono, HasWeightedApproximateTangentSpaceAt.unique (needs only θ x ≠ 0); Mathlib normDet (normDet_comp, normDet_of_subsingleton, normDet_eq_zero_iff_ker_ne_bot, normDet_sq), μHE[d] = c_d·μH[d] with hausdorffMeasure_le_liminf_sum, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, inverse/implicit function theorem (ContDiffAt.toOpenPartialHomeomorph, OpenPartialHomeomorph.contDiffAt_symm, HasStrictFDerivAt.implicitToOpenPartialHomeomorph), change of variables lintegral_image_eq_lintegral_abs_det_fderiv_mul, Lusin-Souslin MeasurableSet.image_of_continuousOn_injOn / ContinuousOn.measurableEmbedding, lintegral_iUnion (arbitrary integrand), lintegral_tsum, lintegral_liminf_le, HasLineDerivAt.unique, Rademacher LipschitzWith.ae_differentiableAt, WithLp.volume_preserving_toLp. The README marks SimonGMT Chapter03 tangentialDifferential/tangentialJacobian (Differential.lean) as unfaithful; they are not used. All ten child types elaborate in the comparator's replayed Contract scope, the sibling antecedents are byte-identical to dag.json, and the parent assembly type-checks against stubs without sorry.
