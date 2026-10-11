module

public import Poincare.SimonGMT.Chapter01.RadonDensity
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

public section

/-!
# Simon GMT, Chapter 1, Remarks 4.13 and 4.15

This module records the order estimates used in the proof of Riesz
representation and the precise `L¹` extension furnished by a polar
representation.  The vector-valued existence theorem in 4.14 is kept
separate: the extension theorem below starts from exactly such a
representation and adds no unproved existence assumption.
-/

open CompactlySupportedContinuousMap Set TopologicalSpace MeasureTheory
open scoped CompactlySupported ENNReal MeasureTheory Topology

namespace Poincare.SimonGMT.Chapter01

universe u v

section PositiveFunctional

variable {X : Type u} [TopologicalSpace X]

/-- Simon Remark 4.13(1): a positive linear functional is monotone. -/
theorem simon_remark_4_13_mono (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ)
    {f g : C_c(X, ℝ)} (hfg : ∀ x, f x ≤ g x) : Λ f ≤ Λ g :=
  OrderHomClass.mono Λ hfg

/-- Simon Remark 4.13, estimate `(*)`: a cutoff equal to one on the support
of `f` controls the positive functional by the uniform norm of `f`. -/
theorem simon_remark_4_13_compact_bound (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ)
    {f g : C_c(X, ℝ)} {K : Set X}
    (hg : ∀ x, 0 ≤ g x) (hfK : tsupport f ⊆ K) (hgK : EqOn g 1 K) :
    Λ f ≤ ‖f.toBoundedContinuousFunction‖ * Λ g := by
  have hpoint : f ≤ ‖f.toBoundedContinuousFunction‖ • g := by
    intro x
    change f x ≤ ‖f.toBoundedContinuousFunction‖ * g x
    by_cases hx : x ∈ tsupport f
    · rw [hgK (hfK hx)]
      simpa using (le_trans (le_abs_self (f x))
        (BoundedContinuousFunction.norm_coe_le_norm f.toBoundedContinuousFunction x))
    · rw [image_eq_zero_of_notMem_tsupport hx]
      exact mul_nonneg (norm_nonneg _) (hg x)
  calc
    Λ f ≤ Λ (‖f.toBoundedContinuousFunction‖ • g) := OrderHomClass.mono Λ hpoint
    _ = ‖f.toBoundedContinuousFunction‖ * Λ g := by rw [map_smul]; rfl

/-- Simon Remark 4.13, local estimate `(**)`.  A single compactly supported
cutoff `g`, chosen from `K ⊆ V`, bounds every `[0,1]`-valued test function
supported in the intermediate neighborhood `W`. -/
theorem simon_remark_4_13_local_sandwich (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ)
    [T2Space X] [LocallyCompactSpace X]
    {K V : Set X} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ (W : Set X) (g : C_c(X, ℝ)),
      IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧ closure W ⊆ V ∧
      (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧ EqOn g 1 (closure W) ∧ tsupport g ⊆ V ∧
      ∀ f : C_c(X, ℝ), (∀ x, 0 ≤ f x ∧ f x ≤ 1) → tsupport f ⊆ W → Λ f ≤ Λ g := by
  obtain ⟨W, hWopen, hKW, hWclV, hWcompact⟩ :=
    exists_open_between_and_isCompact_closure hK hV hKV
  obtain ⟨U, Z, g₀, _, hWclU, _, hUclV,
      _, hWclZ, hgZ, hgUc, hgI, hgcompact⟩ :=
    simon_lemma_4_4 hWcompact hV hWclV
  let g : C_c(X, ℝ) := ⟨g₀, hgcompact⟩
  have hg_nonneg : ∀ x, 0 ≤ g x := fun x => (hgI x).1
  have hg_support : tsupport g ⊆ V := by
    rw [tsupport]
    apply (closure_mono ?_).trans hUclV
    intro x hx
    by_contra hxU
    exact hx (hgUc hxU)
  refine ⟨W, g, hWopen, hKW, hWcompact, hWclV,
    fun x => hgI x, hgZ.mono hWclZ, hg_support, ?_⟩
  intro f hf hfW
  apply OrderHomClass.mono Λ
  intro x
  by_cases hx : x ∈ tsupport f
  · calc
      f x ≤ 1 := (hf x).2
      _ = g x := (hgZ (hWclZ (subset_closure (hfW hx)))).symm
  · rw [image_eq_zero_of_notMem_tsupport hx]
    exact hg_nonneg x

end PositiveFunctional

section PolarExtension

variable {X : Type u} {H : Type v} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The conclusion of Simon Theorem 4.14, isolated as a reusable interface.
It records a unit polar field and the integral representation on compactly
supported continuous maps. -/
def IsVectorRieszRepresentation [TopologicalSpace X] (L : C_c(X, H) →ₗ[ℝ] ℝ)
    (μ : Measure X) (ν : X → H) : Prop :=
  AEStronglyMeasurable ν μ ∧ (∀ᵐ x ∂μ, ‖ν x‖ = 1) ∧
    ∀ f : C_c(X, H), L f = ∫ x, inner ℝ (f x) (ν x) ∂μ

/-- The polar integral of any `L¹` class is integrable. -/
theorem integrable_inner_l1 (μ : Measure X) (ν : X → H)
    (hν : AEStronglyMeasurable ν μ) (hνnorm : ∀ᵐ x ∂μ, ‖ν x‖ = 1)
    (F : Lp H 1 μ) : Integrable (fun x => inner ℝ (F x) (ν x)) μ := by
  refine Integrable.mono' (L1.integrable_coeFn F).norm
    ((Lp.aestronglyMeasurable F).inner hν) ?_
  filter_upwards [hνnorm] with x hx
  exact (norm_inner_le_norm (F x) (ν x)).trans_eq (by rw [hx, mul_one])

/-- The continuous functional on `L¹` induced by a measurable unit polar
field. -/
@[expose] noncomputable def polarL1Functional (μ : Measure X) (ν : X → H)
    (hν : AEStronglyMeasurable ν μ) (hνnorm : ∀ᵐ x ∂μ, ‖ν x‖ = 1) :
    Lp H 1 μ →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun F => ∫ x, inner ℝ (F x) (ν x) ∂μ
      map_add' := by
        intro F G
        rw [← integral_add (integrable_inner_l1 μ ν hν hνnorm F)
          (integrable_inner_l1 μ ν hν hνnorm G)]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add F G] with x hx
        simp only [Pi.add_apply, hx, inner_add_left]
      map_smul' := by
        intro c F
        rw [← integral_smul]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c F] with x hx
        simp only [Pi.smul_apply, hx, RingHom.id_apply, real_inner_smul_left,
          smul_eq_mul] }
    1 (fun F => by
      rw [one_mul, L1.norm_eq_integral_norm]
      exact norm_integral_le_of_norm_le (L1.integrable_coeFn F).norm (by
        filter_upwards [hνnorm] with x hx
        exact (norm_inner_le_norm (F x) (ν x)).trans_eq (by rw [hx, mul_one])))

@[simp] theorem polarL1Functional_apply (μ : Measure X) (ν : X → H)
    (hν : AEStronglyMeasurable ν μ) (hνnorm : ∀ᵐ x ∂μ, ‖ν x‖ = 1)
    (F : Lp H 1 μ) :
    polarL1Functional μ ν hν hνnorm F = ∫ x, inner ℝ (F x) (ν x) ∂μ :=
  rfl

/-- The extension has operator norm at most one. -/
theorem polarL1Functional_norm_le (μ : Measure X) (ν : X → H)
    (hν : AEStronglyMeasurable ν μ) (hνnorm : ∀ᵐ x ∂μ, ‖ν x‖ = 1) :
    ‖polarL1Functional μ ν hν hνnorm‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro F
  rw [one_mul, polarL1Functional_apply, L1.norm_eq_integral_norm]
  exact norm_integral_le_of_norm_le (L1.integrable_coeFn F).norm (by
    filter_upwards [hνnorm] with x hx
    exact (norm_inner_le_norm (F x) (ν x)).trans_eq (by rw [hx, mul_one]))

variable [TopologicalSpace X] [OpensMeasurableSpace X]

/-- Simon Remark 4.15: every polar representation from Theorem 4.14 extends
to a continuous linear functional on `L¹(μ; H)`, agreeing with `L` on compactly
supported continuous maps. -/
theorem simon_remark_4_15 (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (L : C_c(X, H) →ₗ[ℝ] ℝ) (ν : X → H)
    (hrep : IsVectorRieszRepresentation L μ ν) :
    ∃ Lbar : Lp H 1 μ →L[ℝ] ℝ, ‖Lbar‖ ≤ 1 ∧
      ∀ f : C_c(X, H),
        Lbar ((memLp_one_iff_integrable.mpr
          (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)).toLp
            (fun x => f x)) = L f := by
  refine ⟨polarL1Functional μ ν hrep.1 hrep.2.1,
    polarL1Functional_norm_le μ ν hrep.1 hrep.2.1, ?_⟩
  intro f
  let hf : MemLp (fun x => f x) 1 μ := memLp_one_iff_integrable.mpr
    (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)
  change polarL1Functional μ ν hrep.1 hrep.2.1
    (hf.toLp (fun x => f x)) = L f
  rw [polarL1Functional_apply, hrep.2.2 f]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

end PolarExtension

end Poincare.SimonGMT.Chapter01
