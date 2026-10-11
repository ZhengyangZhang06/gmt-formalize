module

public import Poincare.SimonGMT.Chapter01.RadonCaratheodoryIntegral
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.RCLike.Real

@[expose] public section

/-!
# Polar representation on a general locally compact Hausdorff space

The envelope forces unit norm compact-locally. Replacing nonunit values by
a fixed unit vector then gives a global unit field without assuming that a
compact-locally null set is globally null. The full Carathéodory measure is
essential for measurability of the field on an unrestricted domain.
-/

open CompactlySupportedContinuousMap MeasureTheory Set Filter
open scoped CompactlySupported ENNReal NNReal Topology

namespace Poincare.SimonGMT.Chapter01

universe u v

section LocalNorm

variable {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A measure realizing the exact positive envelope forces its bounded
representing field to have norm one on each compact set, almost everywhere.
This formulation applies to the full Carathéodory sigma-algebra. -/
theorem norm_eq_one_on_compact_of_measure_envelope
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (L : C_c(X, H) →ₗ[ℝ] ℝ)
    (henv : ∀ f : C_c(X, ℝ≥0), vectorFunctionalEnvelope L f =
      ∫ x, (f x : ℝ) ∂μ)
    (ν : X → H) (hν : AEStronglyMeasurable ν μ)
    (hνle : ∀ᵐ x ∂μ, ‖ν x‖ ≤ 1)
    (hrep : ∀ ω : C_c(X, H), L ω = ∫ x, inner ℝ (ω x) (ν x) ∂μ)
    {K : Set X} (hK : IsCompact K) :
    ∀ᵐ x ∂μ, x ∈ K → ‖ν x‖ = 1 := by
  obtain ⟨g, hgK, hgc, _, _⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ (subset_univ K)
  let gCc : C_c(X, ℝ) := ⟨g, hgc⟩
  let f : C_c(X, ℝ≥0) := gCc.nnrealPart
  have hfK (x : X) (hx : x ∈ K) : (f x : ℝ) = 1 := by
    simp only [f, nnrealPart_apply, Real.coe_toNNReal']
    change max (g x) 0 = 1
    rw [hgK hx]
    norm_num
  have hfi : Integrable (fun x => (f x : ℝ)) μ :=
    (NNReal.continuous_coe.comp f.continuous).integrable_of_hasCompactSupport
      (f.hasCompactSupport.comp_left (by simp))
  have hfν : Integrable (fun x => (f x : ℝ) * ‖ν x‖) μ := by
    apply hfi.mono' (hfi.aestronglyMeasurable.mul hν.norm)
    filter_upwards [hνle] with x hx
    change ‖(f x : ℝ) * ‖ν x‖‖ ≤ (f x : ℝ)
    rw [Real.norm_of_nonneg (mul_nonneg (f x).coe_nonneg (norm_nonneg _))]
    exact mul_le_of_le_one_right (f x).coe_nonneg hx
  have hupper : (fun x => (f x : ℝ) * ‖ν x‖) ≤ᵐ[μ] (fun x => (f x : ℝ)) := by
    filter_upwards [hνle] with x hx
    exact mul_le_of_le_one_right (f x).coe_nonneg hx
  have hlower : (∫ x, (f x : ℝ) ∂μ) ≤ ∫ x, (f x : ℝ) * ‖ν x‖ ∂μ := by
    rw [← henv]
    apply vectorFunctionalEnvelope_le
    intro ω hω
    have hωi := ω.continuous.integrable_of_hasCompactSupport (μ := μ) ω.hasCompactSupport
    have hinner : Integrable (fun x => inner ℝ (ω x) (ν x)) μ := by
      apply hωi.norm.mono' (hωi.aestronglyMeasurable.inner hν)
      filter_upwards [hνle] with x hx
      exact (norm_inner_le_norm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hx)
    rw [hrep]
    apply integral_mono_ae hinner hfν
    exact Eventually.of_forall fun x => (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hω x) (norm_nonneg _))
  have heq : (fun x => (f x : ℝ) * ‖ν x‖) =ᵐ[μ] (fun x => (f x : ℝ)) :=
    (integral_eq_iff_of_ae_le hfν hfi hupper).mp
      (le_antisymm (integral_mono_ae hfν hfi hupper) hlower)
  filter_upwards [heq] with x hx hxK
  simpa only [hfK x hxK, one_mul] using hx

omit [T2Space X] [LocallyCompactSpace X] [OpensMeasurableSpace X] in
/-- Compact-local agreement of fields preserves all compact-test integrals.
The fields need not agree almost everywhere on the entire space. -/
theorem integral_inner_eq_of_ae_eq_on_compacts
    (μ : Measure X) {ν η : X → H}
    (heq : ∀ K : Set X, IsCompact K → ν =ᵐ[μ.restrict K] η)
    (f : C_c(X, H)) :
    (∫ x, inner ℝ (f x) (ν x) ∂μ) = ∫ x, inner ℝ (f x) (η x) ∂μ := by
  have hs (a : X → H) : (∫ x in tsupport f, inner ℝ (f x) (a x) ∂μ) =
      ∫ x, inner ℝ (f x) (a x) ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport hx, inner_zero_left]
  rw [← hs ν, ← hs η]
  apply integral_congr_ae
  filter_upwards [heq (tsupport f) f.hasCompactSupport] with x hx
  rw [hx]

omit [LocallyCompactSpace X] in
/-- A compact-locally unit field can be made unit everywhere, retaining
compact-local agreement. No global-null assertion is needed. -/
theorem exists_unit_modification_on_compacts [Nontrivial H]
    (μ : Measure X) (ν : X → H) (hν : StronglyMeasurable ν)
    (hunit : ∀ K : Set X, IsCompact K → ∀ᵐ x ∂μ, x ∈ K → ‖ν x‖ = 1) :
    ∃ η : X → H, StronglyMeasurable η ∧ (∀ x, ‖η x‖ = 1) ∧
      ∀ K : Set X, IsCompact K → ν =ᵐ[μ.restrict K] η := by
  classical
  obtain ⟨e, he⟩ := exists_norm_eq H (show (0 : ℝ) ≤ 1 by norm_num)
  let A : Set X := {x | ‖ν x‖ = 1}
  have hA : MeasurableSet A := measurableSet_eq_fun hν.norm.measurable measurable_const
  let η : X → H := A.piecewise ν (fun _ => e)
  refine ⟨η, hν.piecewise hA stronglyMeasurable_const, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ A
    · have hxunit : ‖ν x‖ = 1 := hx
      simpa only [η, piecewise_eq_of_mem A _ _ hx] using hxunit
    · simpa only [η, piecewise_eq_of_notMem A _ _ hx] using he
  · intro K hK
    apply (ae_restrict_iff' hK.measurableSet).mpr
    filter_upwards [hunit K hK] with x hx hxK
    exact (piecewise_eq_of_mem A _ _ (hx hxK)).symm

end LocalNorm

section Representation

variable {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [mX : MeasurableSpace X] [BorelSpace X]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The bounded-field representation in Simon 4.14 on the full measure,
with no countability condition on the domain or the Hilbert space. -/
theorem simon_theorem_4_14_bounded_caratheodory [MeasurableSpace H] [BorelSpace H]
    (L : C_c(X, H) →ₗ[ℝ] ℝ) (hL : IsLocallyBoundedCcFunctional L) :
    ∃ ν : X → H,
      @Measurable X H (vectorFunctionalEnvelopeMeasure L hL).toOuterMeasure.caratheodory _ ν ∧
      (∀ x, ‖ν x‖ ≤ 1) ∧
      ∀ f : C_c(X, H), L f = ∫ x, inner ℝ (f x) (ν x)
        ∂radonCaratheodoryMeasure (vectorFunctionalEnvelopeMeasure L hL) := by
  obtain ⟨T, hT, hText⟩ := simon_theorem_4_14_l1_extension L hL
  obtain ⟨ν, hν, hνle, _, hrep⟩ :=
    exists_radon_caratheodory_L1_dual_field (vectorFunctionalEnvelopeMeasure L hL) T hT
  exact ⟨ν, hν, hνle, fun f => (hText f).symm.trans (hrep f)⟩

/-- The full polar representation for a separable real Hilbert target,
including all finite-dimensional targets. The domain is any locally compact
Hausdorff space, and the measure is the full Carathéodory measure. -/
theorem simon_theorem_4_14_caratheodory [SecondCountableTopology H]
    (L : C_c(X, H) →ₗ[ℝ] ℝ) (hL : IsLocallyBoundedCcFunctional L) :
    ∃ ν : X → H,
      StronglyMeasurable[(vectorFunctionalEnvelopeMeasure L hL).toOuterMeasure.caratheodory] ν ∧
      (∀ᵐ x ∂radonCaratheodoryMeasure (vectorFunctionalEnvelopeMeasure L hL), ‖ν x‖ = 1) ∧
      ∀ f : C_c(X, H), L f = ∫ x, inner ℝ (f x) (ν x)
        ∂radonCaratheodoryMeasure (vectorFunctionalEnvelopeMeasure L hL) := by
  borelize H
  let μ₀ := vectorFunctionalEnvelopeMeasure L hL
  obtain ⟨ν, hνmeas, hνle, hrep⟩ := simon_theorem_4_14_bounded_caratheodory L hL
  have hν : StronglyMeasurable[μ₀.toOuterMeasure.caratheodory] ν :=
    hνmeas.stronglyMeasurable
  have henv : ∀ f : C_c(X, ℝ≥0), vectorFunctionalEnvelope L f =
      ∫ x, (f x : ℝ) ∂radonCaratheodoryMeasure μ₀ := by
    intro f
    have hf : StronglyMeasurable (fun x => (f x : ℝ)) :=
      (NNReal.continuous_coe.comp f.continuous).stronglyMeasurable_of_hasCompactSupport
        (f.hasCompactSupport.comp_left (by simp))
    rw [integral_radonCaratheodoryMeasure μ₀ hf]
    exact simon_theorem_4_14_positive_envelope L hL f
  let μ : @Measure X μ₀.toOuterMeasure.caratheodory := radonCaratheodoryMeasure μ₀
  have hμregular : @Measure.Regular X μ₀.toOuterMeasure.caratheodory _ μ := inferInstance
  have hopen : @OpensMeasurableSpace X _ μ₀.toOuterMeasure.caratheodory :=
    opensMeasurableSpace_radonCaratheodoryMeasure μ₀
  let : MeasurableSpace X := μ₀.toOuterMeasure.caratheodory
  let : OpensMeasurableSpace X := hopen
  let : μ.Regular := hμregular
  have hlocal : ∀ K : Set X, IsCompact K → ∀ᵐ x ∂μ, x ∈ K → ‖ν x‖ = 1 :=
    fun _ hK => norm_eq_one_on_compact_of_measure_envelope μ L henv ν
      hν.aestronglyMeasurable (Eventually.of_forall hνle) hrep hK
  rcases subsingleton_or_nontrivial H with hH | hH
  · have hcompact : ∀ K : Set X, IsCompact K → μ K = 0 := by
      intro K hK
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hlocal K hK] with x hx hxK
      have hzero : ν x = 0 := Subsingleton.elim _ _
      simpa [hzero] using hx hxK
    have huniv : μ univ = 0 := by
      rw [isOpen_univ.measure_eq_iSup_isCompact μ]
      apply le_antisymm _ bot_le
      exact iSup_le fun K => iSup_le fun _ => iSup_le fun hK => (hcompact K hK).le
    have hμ : μ = 0 := Measure.measure_univ_eq_zero.mp huniv
    refine ⟨ν, hν, ?_, hrep⟩
    change ∀ᵐ x ∂μ, ‖ν x‖ = 1
    simp [hμ]
  · obtain ⟨η, hη, hηunit, heq⟩ := exists_unit_modification_on_compacts μ ν hν hlocal
    refine ⟨η, hη, Eventually.of_forall hηunit, ?_⟩
    intro f
    exact (hrep f).trans (integral_inner_eq_of_ae_eq_on_compacts μ heq f)

end Representation

/-- Simon Theorem 4.14 with the printed hypotheses: a locally compact
Hausdorff domain and a finite-dimensional real Hilbert target. The witness is
a Radon outer measure, and both measurability and integration use its full
Carathéodory sigma-algebra. -/
theorem simon_theorem_4_14
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (L : C_c(X, H) →ₗ[ℝ] ℝ) (hL : IsLocallyBoundedCcFunctional L) :
    ∃ (μ : OuterMeasure X) (hμ : IsRadonOuterMeasure μ) (ν : X → H),
      @Measurable X H μ.caratheodory (borel H) ν ∧
      (∀ᵐ x ∂hμ.toCaratheodoryMeasure, ‖ν x‖ = 1) ∧
      ∀ f : C_c(X, H), L f = ∫ x, inner ℝ (f x) (ν x) ∂hμ.toCaratheodoryMeasure := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  borelize H
  obtain ⟨ν, hν, hunit, hrep⟩ := simon_theorem_4_14_caratheodory L hL
  exact ⟨(vectorFunctionalEnvelopeMeasure L hL).toOuterMeasure,
    vectorFunctionalEnvelopeMeasure_isRadon L hL, ν, hν.measurable, hunit, hrep⟩

end Poincare.SimonGMT.Chapter01
