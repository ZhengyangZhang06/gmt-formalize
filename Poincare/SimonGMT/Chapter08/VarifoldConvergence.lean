module

public import Poincare.SimonGMT.Chapter08.FirstVariationRiesz
public import Mathlib.Topology.Order.LiminfLimsup

@[expose] public section

/-!
# First variation under Radon convergence

Simon (8.3.7) and Remark (8.3.8)(1): convergence against all continuous
compactly supported functions on the actual open Grassmann bundle implies
convergence of first variation on every source test field. Taking the
original unit-test supremum proves lower semicontinuity. In particular,
finite local liminf bounds construct locally bounded first variation for
the limiting varifold, so the Riesz construction applies without a new
existence hypothesis.

This module does not assert the separate lower-density conclusion of
(8.3.7), which needs the monotonicity and covering argument.
Source: `Simon-gmt new.pdf`, printed pp. 211--212, PDF objects 217 and 219.
-/

open Set Filter MeasureTheory Function
open scoped Topology ENNReal CompactlySupported

namespace Poincare.SimonGMT.Chapter08.Varifold
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N n : ℕ} {U : Set (Euclidean N)}

/-- Radon (vague) convergence on Simon's actual space `Gₙ(U)`, not
on its ambient closure. -/
def RadonConverges (Vi : ℕ → Varifold N n U) (V : Varifold N n U) : Prop :=
  ∀ f : C_c(U ×ˢ (univ : Set (Grassmannian N n)), ℝ),
    Tendsto (fun i ↦ ∫ z, f z ∂(Vi i).domainMeasure) atTop
      (𝓝 (∫ z, f z ∂V.domainMeasure))

/-- The tangential divergence is a genuine continuous compactly supported
test function on the open Grassmann bundle. -/
def divergenceDomainTest (X : TestVectorField (N := N) U) :
    C_c(U ×ˢ (univ : Set (Grassmannian N n)), ℝ) where
  toFun z := tangentialDivergence X z.1.1 z.1.2
  continuous_toFun := (continuous_tangentialDivergence X.contDiff).comp continuous_subtype_val
  hasCompactSupport' := by
    let F := fun z : Euclidean N × Grassmannian N n ↦ tangentialDivergence X z.1 z.2
    have hcompact : IsCompact (tsupport F) := hasCompactSupport_tangentialDivergence X X.compactSupport
    have hsupport : tsupport F ⊆ U ×ˢ (univ : Set (Grassmannian N n)) := by
      apply (closure_minimal (support_tangentialDivergence_subset X)
        ((isClosed_tsupport X).prod isClosed_univ)).trans
      exact Set.prod_mono X.support_subset (subset_refl _)
    have hK : IsCompact ((Subtype.val : U ×ˢ (univ : Set (Grassmannian N n)) →
        Euclidean N × Grassmannian N n) ⁻¹' tsupport F) :=
      Topology.IsInducing.subtypeVal.isCompact_preimage' hcompact (by
        intro z hz
        exact ⟨⟨z, hsupport hz⟩, rfl⟩)
    exact hK.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_comp_subset_preimage F continuous_subtype_val)

theorem integral_divergenceDomainTest (V : Varifold N n U)
    (X : TestVectorField (N := N) U) :
    (∫ z, divergenceDomainTest X z ∂V.domainMeasure) = V.firstVariation X := by
  rw [firstVariation, ← V.map_domainMeasure,
    (MeasurableEmbedding.subtype_coe
      (V.isOpen_domain.measurableSet.prod MeasurableSet.univ)).integral_map]
  rfl

theorem RadonConverges.firstVariation_tendsto
    {Vi : ℕ → Varifold N n U} {V : Varifold N n U} (h : RadonConverges Vi V)
    (X : TestVectorField (N := N) U) :
    Tendsto (fun i ↦ (Vi i).firstVariation X) atTop (𝓝 (V.firstVariation X)) := by
  simpa only [integral_divergenceDomainTest] using h (divergenceDomainTest X)

/-- The local variation supremum is lower semicontinuous. No local
boundedness assumption is needed for this extended-real inequality. -/
theorem RadonConverges.firstVariationNormOn_le_liminf
    {Vi : ℕ → Varifold N n U} {V : Varifold N n U} (h : RadonConverges Vi V)
    (W : Set (Euclidean N)) :
    V.firstVariationNormOn W ≤ liminf (fun i ↦ (Vi i).firstVariationNormOn W) atTop := by
  classical
  unfold firstVariationNormOn
  refine iSup_le fun X ↦ ?_
  split_ifs with hX
  · calc
      ENNReal.ofReal |V.firstVariation X| =
          liminf (fun i ↦ ENNReal.ofReal |(Vi i).firstVariation X|) atTop :=
        (ENNReal.tendsto_ofReal (h.firstVariation_tendsto X).abs).liminf_eq.symm
      _ ≤ _ := liminf_le_liminf (Eventually.of_forall fun i ↦ by
        apply le_iSup_of_le X
        rw [ite_eq_left hX])
  · exact zero_le

/-- The local liminf hypothesis in (8.3.7) supplies locally bounded
first variation of the limit rather than presupposing it. -/
theorem RadonConverges.hasLocallyBoundedFirstVariation
    {Vi : ℕ → Varifold N n U} {V : Varifold N n U} (h : RadonConverges Vi V)
    (hbound : ∀ W : Set (Euclidean N), IsOpen W →
      (IsCompact (closure W) ∧ closure W ⊆ U) →
      liminf (fun i ↦ (Vi i).firstVariationNormOn W) atTop ≠ ∞) :
    V.HasLocallyBoundedFirstVariation := by
  intro W hW hWU
  exact ne_top_of_le_ne_top (hbound W hW hWU) (h.firstVariationNormOn_le_liminf W)

/-- The measure-valued conclusion in (8.3.7), with the limiting measure
constructed from the source assumptions. -/
theorem RadonConverges.firstVariationRieszMeasure_le_liminf
    {Vi : ℕ → Varifold N n U} {V : Varifold N n U} (h : RadonConverges Vi V)
    (hi : ∀ i, (Vi i).HasLocallyBoundedFirstVariation)
    (hbound : ∀ W : Set (Euclidean N), IsOpen W →
      (IsCompact (closure W) ∧ closure W ⊆ U) →
      liminf (fun i ↦ (Vi i).firstVariationNormOn W) atTop ≠ ∞)
    (W : Set (Euclidean N)) (hW : IsOpen W)
    (hWU : IsCompact (closure W) ∧ closure W ⊆ U) :
    V.firstVariationRieszMeasure (h.hasLocallyBoundedFirstVariation hbound) W ≤
      liminf (fun i ↦ (Vi i).firstVariationRieszMeasure (hi i) W) atTop := by
  simp_rw [firstVariationRieszMeasure_eq_norm _ _ W hW hWU]
  exact h.firstVariationNormOn_le_liminf W

end
end Poincare.SimonGMT.Chapter08.Varifold
