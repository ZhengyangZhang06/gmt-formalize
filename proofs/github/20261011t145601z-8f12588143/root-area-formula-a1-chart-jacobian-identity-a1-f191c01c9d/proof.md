# Parent-supplied natural-language proof

- Parent DAG node: `root.area_formula-a1`
- Child DAG node: `root.area_formula-a1.chart_jacobian_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 2, items (a′)-(c′), of the parent proof. These are Simon Ch. 3 (2.1)-(2.3) (chapter-03.txt lines 327-369): T_yM agrees a.e. with the tangent plane of the chart; d^Mf_x(τ) = D_τf(x) = d/dt f(x + tτ)|_{t=0} by Ch. 2 (4.10); and J^M_f = √det((d^Mf_x)*∘d^Mf_x). The Jacobian chain rule is Simon Ch. 2 (4.11) (chapter-02.txt lines 960-981): J(f∘ψ)(u) = Jψ(u)·J^M_f(ψ(u)).

Library:
- SimonGMT Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt.unique (Chapter03/Rectifiable.lean);
- Mathlib HasLineDerivAt.unique, LinearEquiv.ofInjective, LinearMap.finrank_range_add_finrank_ker, LinearMap.normDet_comp, LinearMap.normDet_comp_of_finrank_eq, LinearMap.normDet_codRestrict.

Notation.
- ℝ^d = Rn d.
- x := ψ(u).
- A := fderiv ℝ ψ u : ℝⁿ →L[ℝ] ℝ^N, and T := range A.
- B := fderiv ℝ (f∘ψ) u : ℝⁿ →L[ℝ] ℝ^p.

Hypotheses:
- (H1) θ(x) ≠ 0.
- (H2) HasWeightedApproximateTangentSpaceAt n M θ x T.
- (H3) For every w ∈ ℝⁿ, HasLineDerivAt ℝ f (Bw) x (Aw); that is, t ↦ f(x + t·Aw) has derivative Bw at t = 0.

Only (H1)-(H3) about the two given linear maps A and B are used. No differentiability of ψ or f∘ψ is needed: if ψ is not differentiable at u then A = 0, and (H2) forces n = 0, which the argument covers.

Proof.
1. T_xM = T. By (H2), the proposition ∃P, HasWeightedApproximateTangentSpaceAt n M θ x P holds. So by definition approxTangentPlane n M θ x is a chosen P′ satisfying HasWeightedApproximateTangentSpaceAt n M θ x P′. By (H1) and uniqueness of weighted approximate tangent spaces at points of nonzero multiplicity (HasWeightedApproximateTangentSpaceAt.unique), P′ = T. This is conclusion (i).
2. A is injective. The first component of (H2) is finrank T = n = dim ℝⁿ (finrank_euclideanSpace_fin). By rank–nullity (LinearMap.finrank_range_add_finrank_ker), dim ker A = 0. So A is injective, and its corestriction A′ : ℝⁿ → T, A′w := Aw, is a linear isomorphism (LinearEquiv.ofInjective).
3. The tangential differential. Let L := B ∘ (A′)⁻¹ : T → ℝ^p. It is linear, and continuous because T is finite dimensional (LinearMap.toContinuousLinearMap). For τ ∈ T put w := (A′)⁻¹τ. Then Aw = τ and Lτ = Bw, so by (H3) HasLineDerivAt ℝ f (Lτ) x τ. Hence HasTangentialDifferentialAt T f x L. This is conclusion (ii), with this L.
4. Identification of d^Mf_x. Suppose L′ : T →L[ℝ] ℝ^p also satisfies HasTangentialDifferentialAt T f x L′. For each τ ∈ T, both L′τ and Lτ are derivatives at t = 0 of t ↦ f(x + tτ), so L′τ = Lτ (HasLineDerivAt.unique); hence L′ = L. The existential in the definition of tangentialDifferential holds (Step 3), so tangentialDifferential T f x is a chosen L′ with this property. Therefore it equals L, and areaJacobian T f x = normDet(L).
5. Jacobian chain rule. By construction L ∘ A′ = B as linear maps ℝⁿ → ℝ^p. Since finrank ℝⁿ = n = finrank T, LinearMap.normDet_comp_of_finrank_eq gives normDet(B) = normDet(L ∘ A′) = normDet(L)·normDet(A′). Moreover normDet(A′) = normDet(A), because A′ is the codomain restriction of A to T (LinearMap.normDet_codRestrict).
 Equivalently, as in the parent: let G := L ∘ π_T, where π_T is the orthogonal projection onto T. Then G ∘ A = B and G|_{range A} = L, so LinearMap.normDet_comp gives normDet(B) = normDet(L)·normDet(A).
6. Conclusion (iii). By Steps 1, 4 and 5:
 areaJacobian (approxTangentPlane n M θ x) f x · normDet(A) = areaJacobian T f x · normDet(A) = normDet(L) · normDet(A) = normDet(B). ∎

Appendix: formalization aid, not part of the mathematical argument. Below is a kernel-checked scratch proof of exactly this statement. It was elaborated after `import GMT.Ch03.Submission` in the contract scope and uses only the axioms propext, Classical.choice and Quot.sound. When transplanting, rename C3check to Submission.areaFormula_chart_jacobian_identity. Use ContinuousLinearMap.ext rather than `ext`, which unfolds EuclideanSpace coordinates.

theorem C3check : ∀ (n N p : ℕ) (M : Set (Rn N)) (θ : Rn N → ℝ) (f : Rn N → Rn p) (ψ : Rn n → Rn N) (u : Rn n), θ (ψ u) ≠ 0 → HasWeightedApproximateTangentSpaceAt n M θ (ψ u) (LinearMap.range (fderiv ℝ ψ u).toLinearMap) → (∀ w : Rn n, HasLineDerivAt ℝ f (fderiv ℝ (f ∘ ψ) u w) (ψ u) (fderiv ℝ ψ u w)) → approxTangentPlane n M θ (ψ u) = LinearMap.range (fderiv ℝ ψ u).toLinearMap ∧ (∃ L : ↥(LinearMap.range (fderiv ℝ ψ u).toLinearMap) →L[ℝ] Rn p, HasTangentialDifferentialAt (LinearMap.range (fderiv ℝ ψ u).toLinearMap) f (ψ u) L) ∧ areaJacobian (approxTangentPlane n M θ (ψ u)) f (ψ u) * (fderiv ℝ ψ u).toLinearMap.normDet = (fderiv ℝ (f ∘ ψ) u).toLinearMap.normDet := by
  intro n N p M θ f ψ u hθ hW hline
  classical
  have h1 : approxTangentPlane n M θ (ψ u) = LinearMap.range (fderiv ℝ ψ u).toLinearMap := by
    have hex : ∃ P : Submodule ℝ (Rn N), HasWeightedApproximateTangentSpaceAt n M θ (ψ u) P :=
      ⟨_, hW⟩
    unfold approxTangentPlane
    rw [dif_pos hex]
    exact hex.choose_spec.unique hθ hW
  have hinj : Function.Injective (fderiv ℝ ψ u).toLinearMap := by
    have h := LinearMap.finrank_range_add_finrank_ker (fderiv ℝ ψ u).toLinearMap
    rw [hW.1, finrank_euclideanSpace_fin] at h
    have hk : Module.finrank ℝ (LinearMap.ker (fderiv ℝ ψ u).toLinearMap) = 0 := by omega
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.finrank_eq_zero.mp hk
  set T := LinearMap.range (fderiv ℝ ψ u).toLinearMap with hT
  let e : Rn n ≃ₗ[ℝ] T := LinearEquiv.ofInjective (fderiv ℝ ψ u).toLinearMap hinj
  let L : T →L[ℝ] Rn p :=
    LinearMap.toContinuousLinearMap ((fderiv ℝ (f ∘ ψ) u).toLinearMap ∘ₗ e.symm.toLinearMap)
  have hLapp : ∀ τ : T, L τ = fderiv ℝ (f ∘ ψ) u (e.symm τ) := fun τ ↦ rfl
  have heA : ∀ τ : T, fderiv ℝ ψ u (e.symm τ) = (τ : Rn N) := fun τ ↦
    congrArg Subtype.val (e.apply_symm_apply τ)
  have hL : HasTangentialDifferentialAt T f (ψ u) L := by
    intro τ
    have := hline (e.symm τ)
    rw [heA τ] at this
    rwa [hLapp τ]
  have hunique : tangentialDifferential T f (ψ u) = L := by
    have hex : ∃ L' : T →L[ℝ] Rn p, HasTangentialDifferentialAt T f (ψ u) L' := ⟨L, hL⟩
    unfold tangentialDifferential
    rw [dif_pos hex]
    refine ContinuousLinearMap.ext fun τ ↦ ?_
    exact (hex.choose_spec τ).unique (hL τ)
  refine ⟨h1, ⟨L, hL⟩, ?_⟩
  rw [h1]
  unfold areaJacobian
  rw [hunique]
  have hcomp : L.toLinearMap ∘ₗ e.toLinearMap = (fderiv ℝ (f ∘ ψ) u).toLinearMap := by
    refine LinearMap.ext fun w ↦ ?_
    show L (e w) = _
    rw [hLapp]
    simp
  have hcod : e.toLinearMap =
      (fderiv ℝ ψ u).toLinearMap.codRestrict T (fun c ↦ LinearMap.mem_range_self _ c) :=
    LinearMap.ext fun w ↦ Subtype.ext rfl
  have h2 := LinearMap.normDet_comp_of_finrank_eq e.toLinearMap L.toLinearMap
    (by rw [finrank_euclideanSpace_fin, hW.1])
  rw [hcomp, hcod, LinearMap.normDet_codRestrict] at h2
  exact h2.symm

## Key steps

1. θ(x) ≠ 0 and uniqueness of weighted approximate tangent spaces give approxTangentPlane n M θ x = range Dψ(u).
2. finrank (range Dψ(u)) = n forces Dψ(u) to be injective, so its corestriction is an isomorphism ℝⁿ ≅ T.
3. L := D(f∘ψ)(u) ∘ (Dψ(u)|^T)⁻¹ is a tangential differential, by the line-derivative hypothesis.
4. Uniqueness of line derivatives gives tangentialDifferential T f x = L, so areaJacobian = normDet L.
5. normDet_comp_of_finrank_eq and normDet_codRestrict give normDet(D(f∘ψ)(u)) = normDet(L)·normDet(Dψ(u)).

## Reference use

### local-project

Queries:
- `rg -n "^def AreaFormula|^def IsC1Submanifold|^noncomputable def approxTangentPlane|^noncomputable def tangentialDifferential|^noncomputable def areaJacobian|^def HasTangentialDifferentialAt|^def IsPositiveLocallyIntegrableWeight|^abbrev Rn" project/GMT/Ch03/Contract.lean`
- `rg -n "theorem normDet_comp|theorem normDet_codRestrict|theorem normDet_ne_zero_tfae|theorem normDet_nonneg|normDet_sq" mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `rg -n "theorem lintegral_iUnion₀|theorem lintegral_tsum|theorem lintegral_indicator₀" mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/`
- `rg -n "theorem isOpen_iUnion_countable|theorem isOpen_biUnion_countable" mathlib/Mathlib/Topology/Bases.lean`
- `rg -n "theorem HasLineDerivAt.unique" mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean`
- `rg -n "theorem LinearMap.exists_antilipschitzWith" mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `rg -n "theorem approximates_deriv_on_nhds|protected theorem lipschitzWith" mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/`
- `rg -n "theorem ContinuousOn.measurable_piecewise" mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `rg -n "theorem measurable_fderiv |theorem measurableSet_of_differentiableAt " mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `rg -n "exists_measurable_subset_ae_eq" mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `rg -n "lemma tsum_set_one|protected theorem tsum_biUnion" mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `rg -n "theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume" mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n "^def LocallyLipschitzOn" mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `rg -n -l "areaFormula_|AreaFormula" mathlib/Mathlib  (no match)`
- `rg -n -i -l "coarea|area_formula" mathlib/Mathlib  (no match)`
- `grep -n "weighted_area_formula_lipschitzOn_fiberSum|aemeasurable_weightedAreaFiberSum_lipschitzOn|ae_eq_of_hasFDerivWithinAt|def areaJacobianWithin|def weightedAreaFiberSum|def areaFiber|theorem continuous_normDet|euclideanHausdorffMeasure_image_le_of_lipschitzOn|HasWeightedApproximateTangentSpaceAt.unique" in the pinned simongmt package lake-packages-25730c7c/simongmt/Poincare/SimonGMT`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Ch03/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ApproximatesLinearOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaMultiplicity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`

Snapshot: project d09bc8a, Mathlib 25730c7c, plus the pinned simongmt package (2b36630). The contract definitions used by the children are in Contract.lean (Rn line 56, IsC1Submanifold 68, approxTangentPlane 84, HasTangentialDifferentialAt 92, tangentialDifferential 97, areaJacobian 102, AreaFormula 218).

Found and cited from Mathlib:
- NormDet.lean: LinearMap.normDet_comp (324), normDet_comp_of_finrank_eq (348), normDet_codRestrict (365), normDet_nonneg, normDet_ne_zero_tfae / normDet_eq_zero_iff_ker_ne_bot.
- lintegral_indicator₀ (Lebesgue/Basic.lean 518), lintegral_iUnion₀ (592), lintegral_tsum (Lebesgue/Add.lean 362).
- TopologicalSpace.isOpen_biUnion_countable (Bases.lean 942); HasLineDerivAt.unique (LineDeriv/Basic.lean 156).
- LinearMap.exists_antilipschitzWith (FiniteDimension.lean 231); HasStrictFDerivAt.approximates_deriv_on_nhds (InverseFunctionTheorem/FDeriv.lean 76).
- ContinuousOn.measurable_piecewise (BorelSpace/Basic.lean 523); measurableSet_of_differentiableAt and measurable_fderiv (FDeriv/Measurable.lean 372, 378); NullMeasurableSet.exists_measurable_subset_ae_eq (NullMeasurable.lean 214).
- ENNReal.tsum_set_one (636) and ENNReal.tsum_biUnion (94) in InfiniteSum/ENNReal.lean; EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Volume/Measure.lean 187); LocallyLipschitzOn (EMetricSpace/Lipschitz.lean 72).

Found and cited from SimonGMT:
- AreaDomain.lean: weighted_area_formula_lipschitzOn_fiberSum, aemeasurable_weightedAreaFiberSum_lipschitzOn, ae_eq_of_hasFDerivWithinAt, areaJacobianWithin (= normDet ∘ fderivWithin).
- AreaMultiplicity.lean: areaFiber, weightedAreaFiberSum.
- continuous_normDet (AreaApproximation.lean 28); euclideanHausdorffMeasure_image_le_of_lipschitzOn (Chapter02/Lipschitz.lean 216); HasWeightedApproximateTangentSpaceAt.unique (Chapter03/Rectifiable.lean 345).

No match: rg finds no AreaFormula or areaFormula_ declaration and no area or coarea formula in the snapshot's Mathlib. The per-piece formula therefore uses SimonGMT's area formulas for Lipschitz maps on Euclidean domains (AreaDomain.lean). That file is not in the import closure of GMT.Ch03.Submission, so Submission.lean must add `import Poincare.SimonGMT.Chapter02.AreaDomain`. Its oleans are present, and the comparator does not freeze Submission's imports.

Checks run against this toolchain:
- All five child statements elaborate after `import GMT.Ch03.Submission`.
- A scratch proof of AreaFormula from the five children plus the two siblings compiles.
- Scratch proofs of all five children compile with the standard axioms only.
