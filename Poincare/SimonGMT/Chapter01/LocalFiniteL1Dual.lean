module

public import Poincare.SimonGMT.Chapter01.FiniteL1Dual
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

@[expose] public section

/-!
# Finite restrictions of a Hilbert-valued `L¹` functional

A functional on an arbitrary measure space restricts to any finite measurable
piece by zero extension.  Finite Hilbert duality then constructs a strongly
measurable field bounded by one everywhere.  The finite-measure assumption is on the
piece only; the original measure need not be sigma-finite.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter01

universe u v

variable {X : Type u} [MeasurableSpace X]
  {H : Type v} [NormedAddCommGroup H]
  (μ : Measure X) {s : Set X} (hs : MeasurableSet s)

/-- Extend an `L¹` class on a restriction by zero off the restricting set. -/
noncomputable def zeroExtendL1 (F : Lp H 1 (μ.restrict s)) : Lp H 1 μ :=
  ((memLp_indicator_iff_restrict hs.nullMeasurableSet).mpr (Lp.memLp F)).toLp
    (s.indicator (F : X → H))

theorem zeroExtendL1_coeFn (F : Lp H 1 (μ.restrict s)) :
    zeroExtendL1 μ hs F =ᵐ[μ] s.indicator (F : X → H) :=
  MemLp.coeFn_toLp _

theorem zeroExtendL1_norm (F : Lp H 1 (μ.restrict s)) :
    ‖zeroExtendL1 μ hs F‖ = ‖F‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (zeroExtendL1_coeFn μ hs F),
    eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet, Lp.norm_def]

section Linear

variable [NormedSpace ℝ H]

/-- Zero extension is linear and isometric. -/
noncomputable def zeroExtendL1Linear : Lp H 1 (μ.restrict s) →ₗ[ℝ] Lp H 1 μ where
  toFun := zeroExtendL1 μ hs
  map_add' F G := by
    apply Lp.ext
    refine (zeroExtendL1_coeFn μ hs (F + G)).trans ?_
    refine ((ae_eq_restrict_iff_indicator_ae_eq hs).mp (Lp.coeFn_add F G)).trans ?_
    change s.indicator (fun x => F x + G x) =ᵐ[μ] _
    rw [indicator_add]
    exact ((zeroExtendL1_coeFn μ hs F).add (zeroExtendL1_coeFn μ hs G)).symm.trans
      (Lp.coeFn_add _ _).symm
  map_smul' c F := by
    apply Lp.ext
    refine (zeroExtendL1_coeFn μ hs (c • F)).trans ?_
    refine ((ae_eq_restrict_iff_indicator_ae_eq hs).mp (Lp.coeFn_smul c F)).trans ?_
    change s.indicator (fun x => c • F x) =ᵐ[μ] _
    rw [indicator_smul]
    exact ((zeroExtendL1_coeFn μ hs F).const_smul c).symm.trans (Lp.coeFn_smul _ _).symm

/-- The continuous zero-extension map used to restrict a functional. -/
noncomputable def zeroExtendL1Continuous : Lp H 1 (μ.restrict s) →L[ℝ] Lp H 1 μ :=
  (zeroExtendL1Linear μ hs).mkContinuous 1 fun F => by
    change ‖zeroExtendL1 μ hs F‖ ≤ 1 * ‖F‖
    rw [zeroExtendL1_norm, one_mul]

theorem zeroExtendL1Continuous_norm_le :
    ‖zeroExtendL1Continuous μ hs (H := H)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro F
  change ‖zeroExtendL1 μ hs F‖ ≤ 1 * ‖F‖
  rw [zeroExtendL1_norm, one_mul]

theorem zeroExtendL1Continuous_toLp {f : X → H} (hf : MemLp f 1 (μ.restrict s)) :
    zeroExtendL1Continuous μ hs (hf.toLp f) =
      ((memLp_indicator_iff_restrict hs.nullMeasurableSet).mpr hf).toLp (s.indicator f) := by
  change zeroExtendL1 μ hs (hf.toLp f) = _
  apply Lp.ext
  exact (zeroExtendL1_coeFn μ hs (hf.toLp f)).trans
    (((ae_eq_restrict_iff_indicator_ae_eq hs).mp hf.coeFn_toLp).trans
      (MemLp.coeFn_toLp _).symm)

theorem zeroExtendL1Continuous_coeFn_toLp {f : X → H} (hf : MemLp f 1 (μ.restrict s)) :
    zeroExtendL1Continuous μ hs (hf.toLp f) =ᵐ[μ] s.indicator f := by
  rw [zeroExtendL1Continuous_toLp]
  exact MemLp.coeFn_toLp _

end Linear

section Hilbert

variable [InnerProductSpace ℝ H] [CompleteSpace H] [IsFiniteMeasure (μ.restrict s)]

/-- Finite restrictions of a norm-at-most-one `L¹` functional have strongly
measurable representing fields with a pointwise unit-ball bound.  Values on
the exceptional set are replaced by zero before any uncountable gluing. -/
theorem exists_bounded_finite_restricted_L1_field
    (T : Lp H 1 μ →L[ℝ] ℝ) (hT : ‖T‖ ≤ 1) :
    ∃ ν : X → H, StronglyMeasurable ν ∧ (∀ x, ‖ν x‖ ≤ 1) ∧
      ∀ (f : X → H) (hf : MemLp f 2 (μ.restrict s)),
        T (zeroExtendL1Continuous μ hs
          ((hf.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)).toLp f)) =
          ∫ x in s, inner ℝ (f x) (ν x) ∂μ := by
  classical
  let Ts := T.comp (zeroExtendL1Continuous μ hs)
  have hTs : ‖Ts‖ ≤ 1 := by
    calc
      ‖Ts‖ ≤ ‖T‖ * ‖zeroExtendL1Continuous μ hs (H := H)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hT (zeroExtendL1Continuous_norm_le μ hs)
        (norm_nonneg (zeroExtendL1Continuous μ hs (H := H))) zero_le_one
      _ = 1 := one_mul 1
  let v := finiteL1DualField (μ.restrict s) Ts
  have hv : StronglyMeasurable (v : X → H) := Lp.stronglyMeasurable v
  have hvle : ∀ᵐ x ∂μ.restrict s, ‖v x‖ ≤ 1 :=
    finiteL1DualField_norm_le_one (μ.restrict s) Ts hTs
  let A : Set X := {x | ‖v x‖ ≤ 1}
  let ν : X → H := A.piecewise v (fun _ => 0)
  have hA : MeasurableSet A := measurableSet_le hv.norm.measurable measurable_const
  have hν : StronglyMeasurable ν := hv.piecewise hA stronglyMeasurable_const
  have hνle (x : X) : ‖ν x‖ ≤ 1 := by
    by_cases hx : x ∈ A
    · change ‖v x‖ ≤ 1 at hx
      simpa only [ν, piecewise_eq_of_mem A _ _ hx] using hx
    · simp [ν, hx]
  have heq : ν =ᵐ[μ.restrict s] v := by
    filter_upwards [hvle] with x hx
    exact piecewise_eq_of_mem A _ _ hx
  refine ⟨ν, hν, hνle, ?_⟩
  intro f hf
  change Ts _ = _
  rw [finiteL1DualField_represents (μ.restrict s) Ts hf]
  apply integral_congr_ae
  filter_upwards [heq] with x hx
  rw [hx]

/-- A chosen, everywhere bounded finite-piece representative. -/
noncomputable def boundedFiniteRestrictedL1Field
    (T : Lp H 1 μ →L[ℝ] ℝ) (hT : ‖T‖ ≤ 1) : X → H :=
  (exists_bounded_finite_restricted_L1_field μ hs T hT).choose

theorem boundedFiniteRestrictedL1Field_spec
    (T : Lp H 1 μ →L[ℝ] ℝ) (hT : ‖T‖ ≤ 1) :
    StronglyMeasurable (boundedFiniteRestrictedL1Field μ hs T hT) ∧
      (∀ x, ‖boundedFiniteRestrictedL1Field μ hs T hT x‖ ≤ 1) ∧
      ∀ (f : X → H) (hf : MemLp f 2 (μ.restrict s)),
        T (zeroExtendL1Continuous μ hs
          ((hf.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)).toLp f)) =
          ∫ x in s, inner ℝ (f x) (boundedFiniteRestrictedL1Field μ hs T hT x) ∂μ :=
  (exists_bounded_finite_restricted_L1_field μ hs T hT).choose_spec

/-- Finite-piece fields obtained from one global functional agree almost
everywhere on overlaps.  The proof tests their difference on the intersection
and uses the integral of its squared norm, so no countability is involved. -/
theorem boundedFiniteRestrictedL1Field_ae_eq_inter
    {t : Set X} (ht : MeasurableSet t) [IsFiniteMeasure (μ.restrict t)]
    (T : Lp H 1 μ →L[ℝ] ℝ) (hT : ‖T‖ ≤ 1) :
    boundedFiniteRestrictedL1Field μ hs T hT =ᵐ[μ.restrict (s ∩ t)]
      boundedFiniteRestrictedL1Field μ ht T hT := by
  classical
  let v := boundedFiniteRestrictedL1Field μ hs T hT
  let w := boundedFiniteRestrictedL1Field μ ht T hT
  obtain ⟨hv, hvle, hvrep⟩ := boundedFiniteRestrictedL1Field_spec μ hs T hT
  obtain ⟨hw, hwle, hwrep⟩ := boundedFiniteRestrictedL1Field_spec μ ht T hT
  let d : X → H := fun x => v x - w x
  let f : X → H := (s ∩ t).indicator d
  have hd : StronglyMeasurable d := hv.sub hw
  have hdle (x : X) : ‖d x‖ ≤ 2 := by
    exact (norm_sub_le _ _).trans (by linarith [hvle x, hwle x])
  have hf : StronglyMeasurable f := hd.indicator (hs.inter ht)
  have hfle (x : X) : ‖f x‖ ≤ 2 := by
    by_cases hx : x ∈ s ∩ t
    · simpa [f, hx] using hdle x
    · simp [f, hx]
  have hfs : MemLp f 2 (μ.restrict s) :=
    MemLp.of_bound hf.aestronglyMeasurable 2 (Eventually.of_forall hfle)
  have hft : MemLp f 2 (μ.restrict t) :=
    MemLp.of_bound hf.aestronglyMeasurable 2 (Eventually.of_forall hfle)
  have hF : zeroExtendL1Continuous μ hs
      ((hfs.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)).toLp f) =
      zeroExtendL1Continuous μ ht
      ((hft.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)).toLp f) := by
    apply Lp.ext
    refine (zeroExtendL1Continuous_coeFn_toLp μ hs _).trans ?_
    refine EventuallyEq.trans ?_ (zeroExtendL1Continuous_coeFn_toLp μ ht _).symm
    exact Eventually.of_forall fun x => by
      by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;> simp [f, hxs, hxt]
  have heq : (∫ x in s ∩ t, inner ℝ (d x) (v x) ∂μ) =
      ∫ x in s ∩ t, inner ℝ (d x) (w x) ∂μ := by
    have hvtest := hvrep f hfs
    have hwtest := hwrep f hft
    have hiv : (fun x => inner ℝ (f x) (v x)) =
        (s ∩ t).indicator (fun x => inner ℝ (d x) (v x)) := by
      funext x
      by_cases hx : x ∈ s ∩ t <;> simp [f, hx]
    have hiw : (fun x => inner ℝ (f x) (w x)) =
        (s ∩ t).indicator (fun x => inner ℝ (d x) (w x)) := by
      funext x
      by_cases hx : x ∈ s ∩ t <;> simp [f, hx]
    change _ = ∫ x in s, inner ℝ (f x) (v x) ∂μ at hvtest
    change _ = ∫ x in t, inner ℝ (f x) (w x) ∂μ at hwtest
    rw [hiv, setIntegral_indicator (hs.inter ht)] at hvtest
    rw [hiw, setIntegral_indicator (hs.inter ht)] at hwtest
    rw [← inter_assoc, inter_self] at hvtest
    rw [inter_left_comm, inter_self] at hwtest
    exact hvtest.symm.trans ((congrArg T hF).trans hwtest)
  have hμs : μ s < ∞ := lt_top_iff_ne_top.mpr (isFiniteMeasure_restrict.mp inferInstance)
  let : IsFiniteMeasure (μ.restrict (s ∩ t)) :=
    isFiniteMeasure_restrict.mpr ((measure_mono inter_subset_left).trans_lt hμs).ne
  have hdmem : MemLp d 2 (μ.restrict (s ∩ t)) :=
    MemLp.of_bound hd.aestronglyMeasurable 2 (Eventually.of_forall hdle)
  have hivint : Integrable (fun x => inner ℝ (d x) (v x)) (μ.restrict (s ∩ t)) := by
    apply memLp_one_iff_integrable.mp
    apply MemLp.of_bound (hd.inner hv).aestronglyMeasurable 2
    exact Eventually.of_forall fun x => (norm_inner_le_norm _ _).trans
      ((mul_le_of_le_one_right (norm_nonneg _) (hvle x)).trans (hdle x))
  have hiwint : Integrable (fun x => inner ℝ (d x) (w x)) (μ.restrict (s ∩ t)) := by
    apply memLp_one_iff_integrable.mp
    apply MemLp.of_bound (hd.inner hw).aestronglyMeasurable 2
    exact Eventually.of_forall fun x => (norm_inner_le_norm _ _).trans
      ((mul_le_of_le_one_right (norm_nonneg _) (hwle x)).trans (hdle x))
  have hzero : (∫ x in s ∩ t, ‖d x‖ ^ 2 ∂μ) = 0 := by
    calc
      (∫ x in s ∩ t, ‖d x‖ ^ 2 ∂μ) =
          ∫ x in s ∩ t, inner ℝ (d x) (v x) - inner ℝ (d x) (w x) ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          change ‖d x‖ ^ 2 = inner ℝ (d x) (v x) - inner ℝ (d x) (w x)
          rw [← inner_sub_right]
          exact (real_inner_self_eq_norm_sq (d x)).symm
      _ = (∫ x in s ∩ t, inner ℝ (d x) (v x) ∂μ) -
          ∫ x in s ∩ t, inner ℝ (d x) (w x) ∂μ := integral_sub hivint hiwint
      _ = 0 := sub_eq_zero.mpr heq
  have hsq : (fun x => ‖d x‖ ^ 2) =ᵐ[μ.restrict (s ∩ t)] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖d x‖)
      ((memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).mp hdmem)).mp hzero
  filter_upwards [hsq] with x hx
  change ‖d x‖ ^ 2 = 0 at hx
  have hx0 : d x = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (d x)])
  exact sub_eq_zero.mp hx0

end Hilbert

end Poincare.SimonGMT.Chapter01
