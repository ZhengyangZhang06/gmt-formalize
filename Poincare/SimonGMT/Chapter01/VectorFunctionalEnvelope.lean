module

public import Poincare.SimonGMT.Chapter01.RadonOuterMeasure
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
public import Mathlib.Analysis.Normed.Module.Basic

@[expose] public section

/-!
# The positive envelope in the proof of Simon Theorem 4.14

The source's compact-set boundedness hypothesis suffices to construct the
positive envelope `λ(f) = sup {L(ω) | ‖ω‖ ≤ f}` and its Radon measure, on an
arbitrary locally compact Hausdorff space.  In particular no countability
hypothesis is introduced.  This is the measure-construction step of 4.14;
it does not assert the remaining existence of a measurable unit polar field.
-/

open CompactlySupportedContinuousMap Set Filter MeasureTheory TopologicalSpace
open scoped CompactlySupported Topology ENNReal NNReal

namespace Poincare.SimonGMT.Chapter01

universe u v

variable {X : Type u} [TopologicalSpace X]
  {H : Type v} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The precise local boundedness assumption in Simon 4.14, expressed as
boundedness above rather than an extended-real supremum. -/
def IsLocallyBoundedCcFunctional (L : C_c(X, H) →ₗ[ℝ] ℝ) : Prop :=
  ∀ K : Set X, IsCompact K →
    BddAbove (L '' {ω : C_c(X, H) | (∀ x, ‖ω x‖ ≤ 1) ∧ tsupport ω ⊆ K})

/-- The real-valued envelope on the cone of nonnegative test functions. -/
noncomputable def vectorFunctionalEnvelope (L : C_c(X, H) →ₗ[ℝ] ℝ)
    (f : C_c(X, ℝ≥0)) : ℝ :=
  sSup (L '' {ω : C_c(X, H) | ∀ x, ‖ω x‖ ≤ (f x : ℝ)})

theorem vectorFunctionalEnvelope_values_nonempty (L : C_c(X, H) →ₗ[ℝ] ℝ)
    (f : C_c(X, ℝ≥0)) :
    (L '' {ω : C_c(X, H) | ∀ x, ‖ω x‖ ≤ (f x : ℝ)}).Nonempty :=
  ⟨0, 0, by simp, map_zero L⟩

theorem vectorFunctionalEnvelope_values_bddAbove (L : C_c(X, H) →ₗ[ℝ] ℝ)
    (hL : IsLocallyBoundedCcFunctional L) (f : C_c(X, ℝ≥0)) :
    BddAbove (L '' {ω : C_c(X, H) | ∀ x, ‖ω x‖ ≤ (f x : ℝ)}) := by
  obtain ⟨C, hC⟩ := hL (tsupport f) f.hasCompactSupport
  let M : ℝ := ‖f.toReal.toBoundedContinuousFunction‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hfM (x : X) : (f x : ℝ) ≤ M := by
    have hx := f.toReal.toBoundedContinuousFunction.norm_coe_le_norm x
    have hx' : (f x : ℝ) ≤ ‖f.toReal.toBoundedContinuousFunction‖ := by
      simpa using hx
    exact hx'.trans (by dsimp [M]; linarith)
  refine ⟨M * C, ?_⟩
  rintro y ⟨ω, hω, rfl⟩
  have hωK : tsupport ω ⊆ tsupport f := by
    apply closure_mono
    intro x hx
    by_contra hxf
    have hf0 : f x = 0 := not_not.mp hxf
    have hω0 : ω x = 0 := norm_eq_zero.mp (le_antisymm (by simpa [hf0] using hω x)
      (norm_nonneg _))
    exact hx hω0
  have hg : L (M⁻¹ • ω) ≤ C := hC ⟨M⁻¹ • ω, ⟨?_, ?_⟩, rfl⟩
  · have heq : L ω = M * L (M⁻¹ • ω) := by
      rw [map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hM.ne', one_mul]
    rw [heq]
    exact mul_le_mul_of_nonneg_left hg hM.le
  · intro x
    rw [CompactlySupportedContinuousMap.smul_apply, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hM.le)]
    calc
      M⁻¹ * ‖ω x‖ ≤ M⁻¹ * M := mul_le_mul_of_nonneg_left
        ((hω x).trans (hfM x)) (inv_nonneg.mpr hM.le)
      _ = 1 := inv_mul_cancel₀ hM.ne'
  · exact (tsupport_smul_subset_right (fun _ : X => M⁻¹) ω).trans hωK

theorem le_vectorFunctionalEnvelope (L : C_c(X, H) →ₗ[ℝ] ℝ)
    (hL : IsLocallyBoundedCcFunctional L) (f : C_c(X, ℝ≥0))
    (ω : C_c(X, H)) (hω : ∀ x, ‖ω x‖ ≤ (f x : ℝ)) :
    L ω ≤ vectorFunctionalEnvelope L f :=
  le_csSup (vectorFunctionalEnvelope_values_bddAbove L hL f) ⟨ω, hω, rfl⟩

theorem vectorFunctionalEnvelope_le (L : C_c(X, H) →ₗ[ℝ] ℝ)
    (f : C_c(X, ℝ≥0)) {C : ℝ}
    (hC : ∀ ω : C_c(X, H), (∀ x, ‖ω x‖ ≤ (f x : ℝ)) → L ω ≤ C) :
    vectorFunctionalEnvelope L f ≤ C :=
  csSup_le (vectorFunctionalEnvelope_values_nonempty L f)
    (by rintro y ⟨ω, hω, rfl⟩; exact hC ω hω)

theorem vectorFunctionalEnvelope_nonneg (L : C_c(X, H) →ₗ[ℝ] ℝ)
    (hL : IsLocallyBoundedCcFunctional L) (f : C_c(X, ℝ≥0)) :
    0 ≤ vectorFunctionalEnvelope L f := by
  simpa using le_vectorFunctionalEnvelope L hL f 0 (by simp)

/-- The pointwise estimate behind the source's splitting argument. -/
theorem norm_vectorFunctionalSplit_le (f g : C_c(X, ℝ≥0)) (ω : C_c(X, H))
    (hω : ∀ x, ‖ω x‖ ≤ (f x : ℝ) + g x) (x : X) :
    ‖((f x : ℝ) / ((f x : ℝ) + g x)) • ω x‖ ≤ (f x : ℝ) := by
  by_cases hz : (f x : ℝ) + g x = 0
  · simp [hz]
  · have hpos : 0 < (f x : ℝ) + g x := lt_of_le_of_ne
      (add_nonneg (f x).coe_nonneg (g x).coe_nonneg) (Ne.symm hz)
    rw [norm_smul, Real.norm_of_nonneg
      (div_nonneg (f x).coe_nonneg hpos.le)]
    calc
      (f x : ℝ) / ((f x : ℝ) + g x) * ‖ω x‖ ≤
          (f x : ℝ) / ((f x : ℝ) + g x) * ((f x : ℝ) + g x) :=
        mul_le_mul_of_nonneg_left (hω x) (div_nonneg (f x).coe_nonneg hpos.le)
      _ = (f x : ℝ) := div_mul_cancel₀ _ hz

/-- The apparent singularity at `f + g = 0` is removable because the split
vector is dominated by `f`, which is zero there. -/
theorem continuous_vectorFunctionalSplit (f g : C_c(X, ℝ≥0)) (ω : C_c(X, H))
    (hω : ∀ x, ‖ω x‖ ≤ (f x : ℝ) + g x) :
    Continuous (fun x => ((f x : ℝ) / ((f x : ℝ) + g x)) • ω x) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hz : (f x : ℝ) + g x = 0
  · have hfzero : (f x : ℝ) = 0 := by
      have := (g x).coe_nonneg
      have := (f x).coe_nonneg
      linarith
    change Tendsto _ (𝓝 x) (𝓝 _)
    simp only [hz, div_zero, zero_smul]
    have ht : Tendsto (fun y => (f y : ℝ)) (𝓝 x) (𝓝 (f x : ℝ)) :=
      (NNReal.continuous_coe.comp f.continuous).tendsto x
    rw [hfzero] at ht
    exact squeeze_zero_norm (norm_vectorFunctionalSplit_le f g ω hω) ht
  · exact ((NNReal.continuous_coe.comp f.continuous).continuousAt.div
      ((NNReal.continuous_coe.comp f.continuous).continuousAt.add
        (NNReal.continuous_coe.comp g.continuous).continuousAt) hz).smul
        ω.continuous.continuousAt

/-- The first compactly supported vector in the source's decomposition. -/
noncomputable def vectorFunctionalSplit (f g : C_c(X, ℝ≥0)) (ω : C_c(X, H))
    (hω : ∀ x, ‖ω x‖ ≤ (f x : ℝ) + g x) : C_c(X, H) :=
  { toFun := fun x => ((f x : ℝ) / ((f x : ℝ) + g x)) • ω x
    continuous_toFun := continuous_vectorFunctionalSplit f g ω hω
    hasCompactSupport' := ω.hasCompactSupport.smul_left }

theorem vectorFunctionalSplit_add (f g : C_c(X, ℝ≥0)) (ω : C_c(X, H))
    (hω : ∀ x, ‖ω x‖ ≤ (f x : ℝ) + g x) :
    vectorFunctionalSplit f g ω hω +
      vectorFunctionalSplit g f ω (by simpa only [add_comm] using hω) = ω := by
  ext x
  change ((f x : ℝ) / ((f x : ℝ) + g x)) • ω x +
    ((g x : ℝ) / ((g x : ℝ) + f x)) • ω x = ω x
  by_cases hz : (f x : ℝ) + g x = 0
  · have hωzero : ω x = 0 := norm_eq_zero.mp
      (le_antisymm (by simpa only [hz] using hω x) (norm_nonneg _))
    simp [hωzero]
  · rw [add_comm (g x : ℝ) (f x : ℝ), ← add_smul, ← add_div,
      div_self hz, one_smul]

@[simp] theorem vectorFunctionalEnvelope_zero (L : C_c(X, H) →ₗ[ℝ] ℝ)
    (hL : IsLocallyBoundedCcFunctional L) : vectorFunctionalEnvelope L 0 = 0 := by
  apply le_antisymm _ (vectorFunctionalEnvelope_nonneg L hL 0)
  apply vectorFunctionalEnvelope_le
  intro ω hω
  have hωzero : ω = 0 := by
    ext x
    exact norm_eq_zero.mp (le_antisymm (by simpa using hω x) (norm_nonneg _))
  simp [hωzero]

/-- Additivity of the supremum in the first paragraph of the proof of
4.14, including continuity of the splitting at its zero denominator. -/
theorem vectorFunctionalEnvelope_add (L : C_c(X, H) →ₗ[ℝ] ℝ)
    (hL : IsLocallyBoundedCcFunctional L) (f g : C_c(X, ℝ≥0)) :
    vectorFunctionalEnvelope L (f + g) =
      vectorFunctionalEnvelope L f + vectorFunctionalEnvelope L g := by
  apply le_antisymm
  · apply vectorFunctionalEnvelope_le
    intro ω hω
    have hω' : ∀ x, ‖ω x‖ ≤ (f x : ℝ) + g x := by simpa using hω
    calc
      L ω = L (vectorFunctionalSplit f g ω hω') +
          L (vectorFunctionalSplit g f ω (by simpa only [add_comm] using hω')) := by
        rw [← map_add, vectorFunctionalSplit_add]
      _ ≤ vectorFunctionalEnvelope L f + vectorFunctionalEnvelope L g :=
        add_le_add
          (le_vectorFunctionalEnvelope L hL f _ (norm_vectorFunctionalSplit_le f g ω hω'))
          (le_vectorFunctionalEnvelope L hL g _
            (norm_vectorFunctionalSplit_le g f ω (by simpa only [add_comm] using hω')))
  · have hpair (ω₁ ω₂ : C_c(X, H))
        (h₁ : ∀ x, ‖ω₁ x‖ ≤ (f x : ℝ)) (h₂ : ∀ x, ‖ω₂ x‖ ≤ (g x : ℝ)) :
        L ω₁ + L ω₂ ≤ vectorFunctionalEnvelope L (f + g) := by
      rw [← map_add]
      apply le_vectorFunctionalEnvelope L hL
      intro x
      exact (norm_add_le _ _).trans (add_le_add (h₁ x) (h₂ x))
    have hfirst : vectorFunctionalEnvelope L f ≤
        vectorFunctionalEnvelope L (f + g) - vectorFunctionalEnvelope L g := by
      apply vectorFunctionalEnvelope_le
      intro ω₁ h₁
      have hsecond : vectorFunctionalEnvelope L g ≤
          vectorFunctionalEnvelope L (f + g) - L ω₁ := by
        apply vectorFunctionalEnvelope_le
        intro ω₂ h₂
        linarith [hpair ω₁ ω₂ h₁ h₂]
      linarith
    linarith

/-- Nonnegative homogeneity of the source's positive envelope. -/
theorem vectorFunctionalEnvelope_smul (L : C_c(X, H) →ₗ[ℝ] ℝ)
    (hL : IsLocallyBoundedCcFunctional L) (c : ℝ≥0) (f : C_c(X, ℝ≥0)) :
    vectorFunctionalEnvelope L (c • f) = (c : ℝ) * vectorFunctionalEnvelope L f := by
  by_cases hc0 : c = 0
  · simp [hc0, vectorFunctionalEnvelope_zero L hL]
  have hc : 0 < (c : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc0)
  apply le_antisymm
  · apply vectorFunctionalEnvelope_le
    intro ω hω
    have hscaled : ∀ x, ‖((c : ℝ)⁻¹ • ω) x‖ ≤ (f x : ℝ) := by
      intro x
      rw [CompactlySupportedContinuousMap.smul_apply, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hc.le)]
      calc
        (c : ℝ)⁻¹ * ‖ω x‖ ≤ (c : ℝ)⁻¹ * ((c : ℝ) * (f x : ℝ)) :=
          mul_le_mul_of_nonneg_left (by simpa using hω x) (inv_nonneg.mpr hc.le)
        _ = (f x : ℝ) := by rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
    calc
      L ω = (c : ℝ) * L ((c : ℝ)⁻¹ • ω) := by
        rw [map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
      _ ≤ (c : ℝ) * vectorFunctionalEnvelope L f :=
        mul_le_mul_of_nonneg_left (le_vectorFunctionalEnvelope L hL f _ hscaled) hc.le
  · have hdiv : vectorFunctionalEnvelope L f ≤
        vectorFunctionalEnvelope L (c • f) / (c : ℝ) := by
      apply vectorFunctionalEnvelope_le
      intro ω hω
      have hscaled : L ((c : ℝ) • ω) ≤ vectorFunctionalEnvelope L (c • f) := by
        apply le_vectorFunctionalEnvelope L hL
        intro x
        rw [CompactlySupportedContinuousMap.smul_apply, norm_smul, Real.norm_of_nonneg hc.le]
        exact mul_le_mul_of_nonneg_left (hω x) hc.le
      rw [map_smul, smul_eq_mul] at hscaled
      apply (le_div_iff₀ hc).mpr
      simpa only [mul_comm] using hscaled
    calc
      (c : ℝ) * vectorFunctionalEnvelope L f ≤
          (c : ℝ) * (vectorFunctionalEnvelope L (c • f) / (c : ℝ)) :=
        mul_le_mul_of_nonneg_left hdiv hc.le
      _ = vectorFunctionalEnvelope L (c • f) := mul_div_cancel₀ _ hc.ne'

/-- The source's positive envelope as an `NNReal`-linear functional. -/
noncomputable def vectorFunctionalEnvelopeNNReal (L : C_c(X, H) →ₗ[ℝ] ℝ)
    (hL : IsLocallyBoundedCcFunctional L) : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0 where
  toFun f := ⟨vectorFunctionalEnvelope L f, vectorFunctionalEnvelope_nonneg L hL f⟩
  map_add' f g := Subtype.ext (vectorFunctionalEnvelope_add L hL f g)
  map_smul' c f := Subtype.ext (vectorFunctionalEnvelope_smul L hL c f)

/-- The positive real linear functional used in Simon 4.14. -/
noncomputable def vectorFunctionalPositiveEnvelope (L : C_c(X, H) →ₗ[ℝ] ℝ)
    (hL : IsLocallyBoundedCcFunctional L) : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  toRealPositiveLinear (vectorFunctionalEnvelopeNNReal L hL)

theorem vectorFunctionalPositiveEnvelope_apply_nonneg
    (L : C_c(X, H) →ₗ[ℝ] ℝ) (hL : IsLocallyBoundedCcFunctional L)
    (f : C_c(X, ℝ≥0)) :
    vectorFunctionalPositiveEnvelope L hL f.toReal = vectorFunctionalEnvelope L f :=
  eq_toRealPositiveLinear_toReal _ _

section RadonMeasure

variable [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The dominating Radon measure constructed in the proof of 4.14. -/
noncomputable def vectorFunctionalEnvelopeMeasure (L : C_c(X, H) →ₗ[ℝ] ℝ)
    (hL : IsLocallyBoundedCcFunctional L) : Measure X :=
  RealRMK.rieszMeasure (vectorFunctionalPositiveEnvelope L hL)

instance vectorFunctionalEnvelopeMeasure_regular (L : C_c(X, H) →ₗ[ℝ] ℝ)
    (hL : IsLocallyBoundedCcFunctional L) : (vectorFunctionalEnvelopeMeasure L hL).Regular :=
  RealRMK.regular_rieszMeasure _

/-- The equality marked `(†)` on page 36: the literal dominated supremum of
the vector functional is the integral against a Radon measure. -/
theorem simon_theorem_4_14_positive_envelope (L : C_c(X, H) →ₗ[ℝ] ℝ)
    (hL : IsLocallyBoundedCcFunctional L) (f : C_c(X, ℝ≥0)) :
    sSup (L '' {ω : C_c(X, H) | ∀ x, ‖ω x‖ ≤ (f x : ℝ)}) =
      ∫ x, (f x : ℝ) ∂vectorFunctionalEnvelopeMeasure L hL := by
  change vectorFunctionalEnvelope L f = _
  rw [vectorFunctionalEnvelopeMeasure,
    ← vectorFunctionalPositiveEnvelope_apply_nonneg L hL f]
  simpa only [toReal_apply] using
    (RealRMK.integral_rieszMeasure (vectorFunctionalPositiveEnvelope L hL) f.toReal).symm

theorem vectorFunctionalEnvelopeMeasure_isRadon (L : C_c(X, H) →ₗ[ℝ] ℝ)
    (hL : IsLocallyBoundedCcFunctional L) :
    IsRadonOuterMeasure (vectorFunctionalEnvelopeMeasure L hL).toOuterMeasure :=
  isRadonOuterMeasure_toOuterMeasure _

/-- Domination of the original vector functional by the envelope integral. -/
theorem abs_apply_le_integral_vectorFunctionalEnvelopeMeasure
    (L : C_c(X, H) →ₗ[ℝ] ℝ) (hL : IsLocallyBoundedCcFunctional L)
    (f : C_c(X, ℝ≥0)) (ω : C_c(X, H)) (hω : ∀ x, ‖ω x‖ ≤ (f x : ℝ)) :
    |L ω| ≤ ∫ x, (f x : ℝ) ∂vectorFunctionalEnvelopeMeasure L hL := by
  rw [← simon_theorem_4_14_positive_envelope L hL f, abs_le]
  constructor
  · have hneg : -L ω ≤ vectorFunctionalEnvelope L f := by
      simpa only [map_neg] using
        le_vectorFunctionalEnvelope L hL f (-ω) (by simpa using hω)
    change -vectorFunctionalEnvelope L f ≤ L ω
    linarith
  · exact le_vectorFunctionalEnvelope L hL f ω hω

/-- The exact norm domination used to pass the vector functional to `L¹`.
No finite-dimensionality is needed for this part of the argument. -/
theorem norm_apply_le_integral_norm_vectorFunctionalEnvelopeMeasure
    (L : C_c(X, H) →ₗ[ℝ] ℝ) (hL : IsLocallyBoundedCcFunctional L)
    (ω : C_c(X, H)) :
    ‖L ω‖ ≤ ∫ x, ‖ω x‖ ∂vectorFunctionalEnvelopeMeasure L hL := by
  let f : C_c(X, ℝ≥0) :=
    { toFun := fun x => ‖ω x‖₊
      continuous_toFun := ω.continuous.nnnorm
      hasCompactSupport' := ω.hasCompactSupport.comp_left (by simp) }
  exact abs_apply_le_integral_vectorFunctionalEnvelopeMeasure L hL f ω (fun _ => le_rfl)

end RadonMeasure

end Poincare.SimonGMT.Chapter01
