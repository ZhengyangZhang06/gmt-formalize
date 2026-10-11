module

public import Poincare.SimonGMT.Chapter01.RadonLocalDualField
public import Poincare.SimonGMT.Chapter01.VectorFunctionalL1

@[expose] public section

/-!
# Integrals on the full Carathéodory sigma-algebra

The full measure associated to a regular Borel measure has exactly the same
outer measure. Borel strongly measurable integrands therefore have the same
integrals for both measures. This transports the compact local dual fields
to Simon's full measure, without a countability assumption on the domain.
-/

open CompactlySupportedContinuousMap MeasureTheory Set Filter
open scoped CompactlySupported ENNReal Topology

namespace Poincare.SimonGMT.Chapter01

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  [mX : MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.Regular]

/-- The full Carathéodory measure of a regular Borel measure. -/
noncomputable abbrev radonCaratheodoryMeasure : @Measure X μ.toOuterMeasure.caratheodory :=
  (isRadonOuterMeasure_toOuterMeasure μ).toCaratheodoryMeasure

theorem radonCaratheodoryMeasure_apply (A : Set X) :
    radonCaratheodoryMeasure μ A = μ A :=
  (isRadonOuterMeasure_toOuterMeasure μ).toCaratheodoryMeasure_apply_all A

omit [T2Space X] [μ.Regular] in
theorem opensMeasurableSpace_radonCaratheodoryMeasure :
    @OpensMeasurableSpace X _ μ.toOuterMeasure.caratheodory := by
  refine @OpensMeasurableSpace.mk X _ μ.toOuterMeasure.caratheodory ?_
  exact (@OpensMeasurableSpace.borel_le X _ mX _).trans
    (le_toOuterMeasure_caratheodory μ)

instance radonCaratheodoryMeasure_regular :
    @Measure.Regular X μ.toOuterMeasure.caratheodory _ (radonCaratheodoryMeasure μ) :=
  (isRadonOuterMeasure_toOuterMeasure μ).toCaratheodoryMeasure_regular

theorem radonCaratheodoryMeasure_trim :
    (radonCaratheodoryMeasure μ).trim (le_toOuterMeasure_caratheodory μ) = μ := by
  ext A hA
  rw [trim_measurableSet_eq _ hA, radonCaratheodoryMeasure_apply]

theorem ae_radonCaratheodoryMeasure_iff {P : X → Prop} :
    (∀ᵐ x ∂radonCaratheodoryMeasure μ, P x) ↔ ∀ᵐ x ∂μ, P x := by
  simp only [ae_iff, radonCaratheodoryMeasure_apply]

theorem ae_restrict_radonCaratheodoryMeasure_iff {A : Set X} (hA : MeasurableSet A)
    {P : X → Prop} :
    (∀ᵐ x ∂(radonCaratheodoryMeasure μ).restrict A, P x) ↔
      ∀ᵐ x ∂μ.restrict A, P x := by
  rw [ae_restrict_iff' (le_toOuterMeasure_caratheodory μ A hA),
    ae_restrict_iff' hA, ae_radonCaratheodoryMeasure_iff]

theorem integral_radonCaratheodoryMeasure {E : Type v} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : X → E} (hf : StronglyMeasurable f) :
    (∫ x, f x ∂radonCaratheodoryMeasure μ) = ∫ x, f x ∂μ := by
  rw [integral_trim (le_toOuterMeasure_caratheodory μ) hf,
    radonCaratheodoryMeasure_trim]

theorem setIntegral_radonCaratheodoryMeasure {E : Type v} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : X → E} (hf : StronglyMeasurable f)
    {A : Set X} (hA : MeasurableSet A) :
    (∫ x in A, f x ∂radonCaratheodoryMeasure μ) = ∫ x in A, f x ∂μ := by
  rw [setIntegral_trim (le_toOuterMeasure_caratheodory μ) hf hA,
    radonCaratheodoryMeasure_trim]

section LocalDual

variable [LocallyCompactSpace X]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [LocallyCompactSpace X] in
/-- The finite dual on the support of a test function represents the original
global functional. Zero extension recovers precisely the original `L¹` class. -/
theorem compactL1DualField_represents_test
    (T : Lp H 1 μ →L[ℝ] ℝ) (hT : ‖T‖ ≤ 1) (f : C_c(X, H)) :
    T (compactlySupportedToL1 μ f) =
      ∫ x in tsupport f, inner ℝ (f x)
        (compactL1DualField μ (tsupport f) f.hasCompactSupport T hT x) ∂μ := by
  let K : Set X := tsupport f
  have hK : IsCompact K := f.hasCompactSupport
  let : Fact (μ K < ∞) := ⟨hK.measure_lt_top⟩
  have hf : MemLp (f : X → H) 2 (μ.restrict K) :=
    f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport
  have hzero : zeroExtendL1Continuous μ hK.measurableSet
      ((hf.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)).toLp f) =
        compactlySupportedToL1 μ f := by
    apply Lp.ext
    refine (zeroExtendL1Continuous_coeFn_toLp μ hK.measurableSet _).trans ?_
    refine EventuallyEq.trans ?_ (compactlySupportedToL1_coeFn μ f).symm
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ K
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]
  rw [← hzero]
  exact (boundedFiniteRestrictedL1Field_spec μ hK.measurableSet T hT).2.2 f hf

omit [LocallyCompactSpace X] in
/-- Compact-local agreement suffices for the full Carathéodory integral
representation of every compactly supported continuous test function. -/
theorem radon_local_L1_dual_represents_test
    (T : Lp H 1 μ →L[ℝ] ℝ) (hT : ‖T‖ ≤ 1) (ν : X → H)
    (hν : ∀ (C : Set X) (hC : IsCompact C),
      ν =ᵐ[μ.restrict C] compactL1DualField μ C hC T hT)
    (f : C_c(X, H)) :
    T (compactlySupportedToL1 μ f) =
      ∫ x, inner ℝ (f x) (ν x) ∂radonCaratheodoryMeasure μ := by
  rw [compactL1DualField_represents_test μ T hT f]
  have hstrong : StronglyMeasurable (fun x => inner ℝ (f x)
      (compactL1DualField μ (tsupport f) f.hasCompactSupport T hT x)) :=
    (f.continuous.stronglyMeasurable_of_hasCompactSupport f.hasCompactSupport).inner
      (compactL1DualField_stronglyMeasurable μ _ f.hasCompactSupport T hT)
  rw [← setIntegral_radonCaratheodoryMeasure μ hstrong f.hasCompactSupport.measurableSet]
  calc
    _ = ∫ x in tsupport f, inner ℝ (f x) (ν x) ∂radonCaratheodoryMeasure μ := by
      apply integral_congr_ae
      have hae := (ae_restrict_radonCaratheodoryMeasure_iff μ
        f.hasCompactSupport.measurableSet).mpr (hν (tsupport f) f.hasCompactSupport)
      filter_upwards [hae] with x hx
      rw [hx]
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport hx, inner_zero_left]

/-- A bounded representing field for the full measure, with compact-local
compatibility retained for further localization arguments. -/
theorem exists_radon_caratheodory_L1_dual_field [MeasurableSpace H] [BorelSpace H]
    (T : Lp H 1 μ →L[ℝ] ℝ) (hT : ‖T‖ ≤ 1) :
    ∃ ν : X → H, @Measurable X H μ.toOuterMeasure.caratheodory _ ν ∧
      (∀ x, ‖ν x‖ ≤ 1) ∧
      (∀ (C : Set X) (hC : IsCompact C),
        ν =ᵐ[μ.restrict C] compactL1DualField μ C hC T hT) ∧
      ∀ f : C_c(X, H), T (compactlySupportedToL1 μ f) =
        ∫ x, inner ℝ (f x) (ν x) ∂radonCaratheodoryMeasure μ := by
  obtain ⟨ν, hν, hνle, hνlocal⟩ := exists_radon_local_L1_dual_field μ T hT
  exact ⟨ν, hν, hνle, hνlocal, radon_local_L1_dual_represents_test μ T hT ν hνlocal⟩

end LocalDual

end Poincare.SimonGMT.Chapter01
