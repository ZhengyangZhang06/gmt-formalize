module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

@[expose] public section

/-!
# Finite-measure Hilbert-valued `L¹` duality

This supplies the duality step used in Simon 4.14 in the finite-measure case.
It is derived from Hilbert-space Riesz representation on `L²`, rather than
assuming a representation of the original compact-support functional.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter01

universe u v

variable {X : Type u} [MeasurableSpace X]
  {H : Type v} [NormedAddCommGroup H]
  (μ : Measure X) [IsFiniteMeasure μ]

section Inclusion

variable [NormedSpace ℝ H]

/-- The natural inclusion from `L²` into `L¹` for a finite measure. -/
noncomputable def finiteL2ToL1Linear : Lp H 2 μ →ₗ[ℝ] Lp H 1 μ where
  toFun F := ⟨F.1, Lp.antitone (by norm_num : (1 : ℝ≥0∞) ≤ 2) F.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finiteL2ToL1Linear_coeFn (F : Lp H 2 μ) :
    (finiteL2ToL1Linear μ F : X → H) = F := rfl

theorem finiteL2ToL1Linear_norm_le (F : Lp H 2 μ) :
    ‖finiteL2ToL1Linear μ F‖ ≤ (μ univ ^ (1 / 2 : ℝ)).toReal * ‖F‖ := by
  have hb := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.aestronglyMeasurable F)
  have hfin : eLpNorm (F : X → H) 2 μ * μ univ ^ (1 / 2 : ℝ) ≠ ∞ := by
    finiteness
  have hb' : eLpNorm (F : X → H) 1 μ ≤
      eLpNorm (F : X → H) 2 μ * μ univ ^ (1 / 2 : ℝ) := by
    convert hb using 1
    norm_num
  have ht := ENNReal.toReal_mono hfin hb'
  simpa only [Lp.norm_def, finiteL2ToL1Linear_coeFn, ENNReal.toReal_mul, mul_comm] using ht

/-- The finite-measure inclusion is continuous. -/
noncomputable def finiteL2ToL1 : Lp H 2 μ →L[ℝ] Lp H 1 μ :=
  (finiteL2ToL1Linear μ).mkContinuous (μ univ ^ (1 / 2 : ℝ)).toReal
    (finiteL2ToL1Linear_norm_le μ)

theorem finiteL2ToL1_toLp {f : X → H} (hf : MemLp f 2 μ) :
    finiteL2ToL1 μ (hf.toLp f) =
      (hf.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)).toLp f := rfl

end Inclusion

variable [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The `L²` representative of an `L¹` functional restricted to `L²`. -/
noncomputable def finiteL1DualField (T : Lp H 1 μ →L[ℝ] ℝ) : Lp H 2 μ :=
  (InnerProductSpace.toDual ℝ (Lp H 2 μ)).symm (T.comp (finiteL2ToL1 μ))

/-- Representation on every square-integrable test function. -/
theorem finiteL1DualField_represents (T : Lp H 1 μ →L[ℝ] ℝ)
    {f : X → H} (hf : MemLp f 2 μ) :
    T ((hf.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)).toLp f) =
      ∫ x, inner ℝ (f x) (finiteL1DualField μ T x) ∂μ := by
  have h := InnerProductSpace.toDual_symm_apply
    (𝕜 := ℝ) (x := hf.toLp f) (y := T.comp (finiteL2ToL1 μ))
  change inner ℝ (finiteL1DualField μ T) (hf.toLp f) = _ at h
  rw [L2.inner_def] at h
  rw [← finiteL2ToL1_toLp μ hf]
  change (T.comp (finiteL2ToL1 μ)) (hf.toLp f) = _
  rw [← h]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, real_inner_comm]

/-- A functional of norm at most one has an essentially unit-ball-valued
representative.  Indicator tests give `∫ ‖ν‖² ≤ ∫ ‖ν‖` on every measurable
set, which forces `‖ν‖ ≤ 1` almost everywhere. -/
theorem finiteL1DualField_norm_le_one (T : Lp H 1 μ →L[ℝ] ℝ) (hT : ‖T‖ ≤ 1) :
    ∀ᵐ x ∂μ, ‖finiteL1DualField μ T x‖ ≤ 1 := by
  let ν := finiteL1DualField μ T
  have hν : MemLp (ν : X → H) 2 μ := Lp.memLp ν
  have hν1 : Integrable (ν : X → H) μ :=
    memLp_one_iff_integrable.mp (hν.mono_exponent (by norm_num))
  have hνsq : Integrable (fun x => ‖ν x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hν.aestronglyMeasurable).mp hν
  have hle : (fun x => ‖ν x‖ ^ 2) ≤ᵐ[μ] (fun x => ‖ν x‖) := by
    apply ae_le_of_forall_setIntegral_le hνsq hν1.norm
    intro S hS _
    let hSν : MemLp (S.indicator (ν : X → H)) 2 μ := hν.indicator hS.nullMeasurableSet
    let F : Lp H 1 μ := (hSν.mono_exponent (by norm_num)).toLp _
    have hbound : T F ≤ ‖F‖ := (le_abs_self _).trans
      ((T.le_opNorm F).trans (by simpa using mul_le_mul_of_nonneg_right hT (norm_nonneg F)))
    have heq : T F = ∫ x in S, ‖ν x‖ ^ 2 ∂μ := by
      rw [finiteL1DualField_represents μ T hSν]
      have heq' : (fun x => inner ℝ (S.indicator (ν : X → H) x) (ν x)) =
          S.indicator (fun x => ‖ν x‖ ^ 2) := by
        funext x
        by_cases hx : x ∈ S <;> simp [hx]
      rw [heq', integral_indicator hS]
    have hnorm : ‖F‖ = ∫ x in S, ‖ν x‖ ∂μ := by
      rw [L1.norm_eq_integral_norm]
      have hF : (F : X → H) =ᵐ[μ] S.indicator (ν : X → H) :=
        MemLp.coeFn_toLp (hSν.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2))
      calc
        (∫ x, ‖F x‖ ∂μ) = ∫ x, ‖S.indicator (ν : X → H) x‖ ∂μ :=
          integral_congr_ae (by filter_upwards [hF] with x hx; rw [hx])
        _ = ∫ x in S, ‖ν x‖ ∂μ := by
          simp_rw [norm_indicator_eq_indicator_norm]
          exact integral_indicator hS
    rwa [heq, hnorm] at hbound
  filter_upwards [hle] with x hx
  nlinarith [norm_nonneg (ν x)]

end Poincare.SimonGMT.Chapter01
