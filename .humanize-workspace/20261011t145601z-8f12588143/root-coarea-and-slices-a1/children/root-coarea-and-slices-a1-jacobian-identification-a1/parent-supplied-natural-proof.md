# Parent-supplied natural-language proof

- Parent DAG node: `root.coarea_and_slices-a1`
- Child DAG node: `root.coarea_and_slices-a1.jacobian_identification-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Part 1.2 (identification of T_xM and d^Mf_x through a chart, using uniqueness of weighted tangent planes and of line derivatives; Simon Ch. 3, 2.1-2.2 and (2.7), chapter-03.txt lines 335-360 and 412-418), combined with the sibling coarea_normDet_chain_rule (the parent's LA).
1. ((i).) Let T := range A. By definition, approxTangentPlane n M θ x = h.choose where h : ∃ P, HasWeightedApproximateTangentSpaceAt n M θ x P, which holds with P = T; and h.choose satisfies HasWeightedApproximateTangentSpaceAt n M θ x h.choose (Exists.choose_spec). Since θ(x) ≠ 0, uniqueness of weighted approximate tangent spaces (SimonGMT HasWeightedApproximateTangentSpaceAt.unique) gives h.choose = T.
2. ((ii).) A is injective, so it induces a linear isomorphism A' : ℝⁿ → T (LinearEquiv.ofInjective). Define L := Γ ∘ A'⁻¹ : T → ℝᵐ, continuous because T is finite-dimensional. For τ ∈ T put w := A'⁻¹τ, so τ = Aw and Lτ = Γw; the hypothesis gives HasLineDerivAt ℝ f (Lτ) x τ. Hence HasTangentialDifferentialAt T f x L.
3. (d^Mf_x = L.) By definition tangentialDifferential T f x = h'.choose for h' : ∃ L, HasTangentialDifferentialAt T f x L (true by step 2); call it L'. For each τ ∈ T both L'τ and Lτ are line derivatives of f at x in direction τ, so L'τ = Lτ by uniqueness of line derivatives (Mathlib HasLineDerivAt.unique). Hence tangentialDifferential T f x = L and coareaJacobian T f x = normDet((L as a linear map)*).
4. ((iii).) Rewrite approxTangentPlane n M θ x = T by step 1, so the left side is normDet(L*)·normDet(A) by step 3. For v ∈ ℝⁿ, L(Av) = Γ(A'⁻¹(Av)) = Γv. Apply the sibling coarea_normDet_chain_rule to T, the linear map A (injective, range A = T), L and Γ: normDet(L*)·normDet(A) = normDet(A ∘ ι_{ker Γ})·normDet(Γ*). ∎

## Key steps

1. Uniqueness of weighted approximate tangent spaces (θ(x) ≠ 0) identifies approxTangentPlane with range A.
2. L := Γ ∘ A'⁻¹ on range A is a tangential differential (line derivatives along A).
3. Uniqueness of line derivatives identifies tangentialDifferential with L.
4. The chain rule sibling converts coareaJacobian·normDet(A) into normDet(A∘ι_{ker Γ})·normDet(Γ*).

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
