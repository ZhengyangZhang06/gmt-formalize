module

public import Poincare.SimonGMT.Chapter08.Varifold
public import Mathlib.Geometry.Manifold.SmoothApprox

@[expose] public section

/-!
# Local bounds and smooth test-field approximation for Simon (8.2.5)

The definition of locally bounded first variation is equivalent to the
source's local uniform-norm bound. A domain-local signed polar representation
implies that bound, and continuous compactly supported unit fields are
uniformly approximable by `C¹` unit fields preserving support.

The forward Riesz/Radon existence theorem and the extension of first
variation from `C¹` tests to `C_c(U; ℝᴺ)` are not asserted here.
-/

open Set Filter MeasureTheory Function
open scoped Topology ENNReal

namespace Poincare.SimonGMT.Chapter08.Varifold
noncomputable section
variable {N n : ℕ} {U : Set (Euclidean N)}

def TestVectorField.scale (X : TestVectorField (N := N) U) (c : ℝ) :
    TestVectorField (N := N) U where
  toFun := c • X.toFun
  contDiff := X.contDiff.const_smul c
  compactSupport := X.compactSupport.mono (support_const_smul_subset c X.toFun)
  support_subset := (closure_mono (support_const_smul_subset c X.toFun)).trans X.support_subset

theorem TestVectorField.tsupport_scale_subset (X : TestVectorField (N := N) U) (c : ℝ) :
    tsupport (X.scale c).toFun ⊆ tsupport X.toFun :=
  closure_mono (support_const_smul_subset c X.toFun)

theorem TestVectorField.norm_le_iff_on_domain (X : TestVectorField (N := N) U)
    {B : ℝ} (hB : 0 ≤ B) : (∀ x, ‖X x‖ ≤ B) ↔ ∀ x ∈ U, ‖X x‖ ≤ B := by
  refine ⟨fun h x _ ↦ h x, fun h x ↦ ?_⟩
  by_cases hx : x ∈ U
  · exact h x hx
  · have hz : X x = 0 := image_eq_zero_of_notMem_tsupport
      (fun hs ↦ hx (X.support_subset hs))
    simpa only [hz, norm_zero] using hB

theorem le_firstVariationNormOn
    (V : Varifold N n U) (W : Set (Euclidean N)) (X : TestVectorField (N := N) U)
    (hX : X.UnitSupportedIn W) : ENNReal.ofReal |V.firstVariation X| ≤ V.firstVariationNormOn W := by
  classical
  unfold firstVariationNormOn
  exact le_iSup_of_le X (by rw [ite_eq_left hX])

theorem firstVariationNormOn_ne_top_iff_exists_bound
    (V : Varifold N n U) (W : Set (Euclidean N)) :
    V.firstVariationNormOn W ≠ ∞ ↔ ∃ C : ℝ, 0 ≤ C ∧
      ∀ X : TestVectorField (N := N) U, X.UnitSupportedIn W → |V.firstVariation X| ≤ C := by
  classical
  constructor
  · intro hfin
    refine ⟨(V.firstVariationNormOn W).toReal, ENNReal.toReal_nonneg, fun X hX ↦ ?_⟩
    exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp (V.le_firstVariationNormOn W X hX)
  · rintro ⟨C, hC, hbound⟩
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    unfold firstVariationNormOn
    refine iSup_le fun X ↦ ?_
    split_ifs with hX
    · exact ENNReal.ofReal_le_ofReal (hbound X hX)
    · exact zero_le

theorem firstVariation_bound_of_unit_bound
    (V : Varifold N n U) (W : Set (Euclidean N)) (C : ℝ)
    (_hC : 0 ≤ C)
    (hbound : ∀ X : TestVectorField (N := N) U, X.UnitSupportedIn W → |V.firstVariation X| ≤ C)
    (X : TestVectorField (N := N) U) (hX : tsupport X.toFun ⊆ W)
    {B : ℝ} (hB : 0 ≤ B) (hXB : ∀ x, ‖X x‖ ≤ B) :
    |V.firstVariation X| ≤ C * B := by
  rcases hB.eq_or_lt with rfl | hBpos
  · have hzero : X.toFun = fun _ ↦ 0 := by
      funext x
      exact norm_eq_zero.mp (le_antisymm (hXB x) (norm_nonneg _))
    change |V.firstVariation X.toFun| ≤ _
    rw [hzero, V.firstVariation_zero, abs_zero, mul_zero]
  let Y := X.scale B⁻¹
  have hY : Y.UnitSupportedIn W := by
    refine ⟨(X.tsupport_scale_subset _).trans hX, fun x ↦ ?_⟩
    change ‖B⁻¹ • X x‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hBpos)]
    simpa only [inv_mul_cancel₀ hBpos.ne'] using
      mul_le_mul_of_nonneg_left (hXB x) (inv_nonneg.mpr hB)
  have hh := hbound Y hY
  change |V.firstVariation (B⁻¹ • X.toFun)| ≤ C at hh
  rw [V.firstVariation_const_smul B⁻¹ X.contDiff X.compactSupport, abs_mul,
    abs_of_pos (inv_pos.mpr hBpos)] at hh
  have hmul := mul_le_mul_of_nonneg_right hh hB
  calc
    |V.firstVariation X| = (B⁻¹ * |V.firstVariation X|) * B := by
      rw [mul_right_comm, inv_mul_cancel₀ hBpos.ne', one_mul]
    _ ≤ C * B := hmul

/-- The supremum formulation agrees with Simon's pre-(2.5) local uniform
norm estimate. Bounds over all ambient points or only over `U` are
equivalent by `TestVectorField.norm_le_iff_on_domain`. -/
theorem hasLocallyBoundedFirstVariation_iff_local_bound
    (V : Varifold N n U) :
    V.HasLocallyBoundedFirstVariation ↔
      ∀ W : Set (Euclidean N), IsOpen W →
        (IsCompact (closure W) ∧ closure W ⊆ U) →
          ∃ C : ℝ, 0 ≤ C ∧ ∀ X : TestVectorField (N := N) U,
            tsupport X.toFun ⊆ W → ∀ B : ℝ, 0 ≤ B →
              (∀ x, ‖X x‖ ≤ B) → |V.firstVariation X| ≤ C * B := by
  constructor
  · intro hV W hW hWU
    obtain ⟨C, hC, hc⟩ := (V.firstVariationNormOn_ne_top_iff_exists_bound W).mp (hV W hW hWU)
    exact ⟨C, hC, fun X hX _ hB hXB ↦ V.firstVariation_bound_of_unit_bound W C hC hc X hX hB hXB⟩
  · intro hV W hW hWU
    obtain ⟨C, hC, hc⟩ := hV W hW hWU
    apply (V.firstVariationNormOn_ne_top_iff_exists_bound W).mpr
    exact ⟨C, hC, fun X hX ↦ by simpa only [mul_one] using hc X hX.1 1 zero_le_one hX.2⟩

/-- The upper estimate in (2.5) follows from any signed unit polar
representation (2.6). This proves an implication, not existence. -/
theorem firstVariationNormOn_le_of_polarRepresentation
    (V : Varifold N n U) {μ : Measure (Euclidean N)} {ν : Euclidean N → Euclidean N}
    (hrep : V.IsFirstVariationPolarRepresentation μ ν) (W : Set (Euclidean N)) :
    V.firstVariationNormOn W ≤ μ W := by
  classical
  unfold firstVariationNormOn
  refine iSup_le fun X ↦ ?_
  split_ifs with hX
  · rw [(hrep.2.2 X).2, abs_neg, ← Real.enorm_eq_ofReal_abs]
    apply (enorm_integral_le_lintegral_enorm (fun x ↦ inner ℝ (ν x) (X x))).trans
    apply le_trans ?_ (lintegral_indicator_one_le W)
    apply lintegral_mono_ae
    filter_upwards [hrep.2.1] with x hx
    by_cases hxW : x ∈ W
    · rw [indicator_of_mem hxW]
      change ‖inner ℝ (ν x) (X x)‖ₑ ≤ 1
      rw [Real.enorm_eq_ofReal_abs]
      apply ENNReal.ofReal_le_one.mpr
      have hb : ‖inner ℝ (ν x) (X x)‖ ≤ ‖ν x‖ * ‖X x‖ := norm_inner_le_norm _ _
      rw [Real.norm_eq_abs, hx, one_mul] at hb
      exact hb.trans (hX.2 x)
    · have hz : X x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hxW (hX.1 h))
      simp only [hz, inner_zero_right, enorm_zero, indicator_of_notMem hxW]
      exact le_rfl
  · exact zero_le

/-- The representation-to-boundedness implication in the preamble to
(2.5), with Radon finiteness only on the actual open domain. -/
theorem hasLocallyBoundedFirstVariation_of_domain_polarRepresentation
    (V : Varifold N n U) (μ : Measure U) [IsLocallyFiniteMeasure μ]
    {ν : Euclidean N → Euclidean N}
    (hrep : V.IsFirstVariationPolarRepresentation (μ.map Subtype.val) ν) :
    V.HasLocallyBoundedFirstVariation := by
  intro W hW hWU
  have hfinite : (μ.map (Subtype.val : U → Euclidean N)) (closure W) ≠ ∞ := by
    rw [Measure.map_apply measurable_subtype_coe hWU.1.measurableSet]
    apply IsCompact.measure_ne_top
    apply Topology.IsInducing.subtypeVal.isCompact_preimage' hWU.1
    simpa using hWU.2
  apply ne_top_of_le_ne_top hfinite
  exact (V.firstVariationNormOn_le_of_polarRepresentation hrep W).trans (measure_mono subset_closure)

theorem exists_testVectorField_uniform_approx
    (f : Euclidean N → Euclidean N) (hf : Continuous f) (hc : HasCompactSupport f)
    (hU : tsupport f ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ X : TestVectorField (N := N) U,
      tsupport X.toFun ⊆ tsupport f ∧ ∀ x, ‖X x - f x‖ < ε := by
  obtain ⟨g, hg, he, hs⟩ := hf.exists_contDiff_approx 1 continuous_const (fun _ ↦ hε)
  refine ⟨⟨g, hg, hc.mono hs, (closure_mono hs).trans hU⟩, closure_mono hs, ?_⟩
  intro x
  exact (dist_eq_norm (g x) (f x)) ▸ he x

/-- Continuous compactly supported unit fields can be approximated uniformly
by `C¹` unit fields with no enlargement of their support. This is a density
ingredient for the exact supremum in (2.5), not a representation theorem. -/
theorem exists_unit_testVectorField_uniform_approx
    (f : Euclidean N → Euclidean N) (hf : Continuous f) (hc : HasCompactSupport f)
    (hU : tsupport f ⊆ U) (hunit : ∀ x, ‖f x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ X : TestVectorField (N := N) U,
      tsupport X.toFun ⊆ tsupport f ∧ (∀ x, ‖X x‖ ≤ 1) ∧ ∀ x, ‖X x - f x‖ < ε := by
  let δ := ε / 2
  have hδ : 0 < δ := half_pos hε
  obtain ⟨G, hGs, hGe⟩ := exists_testVectorField_uniform_approx f hf hc hU hδ
  let a : ℝ := (1 + δ)⁻¹
  have ha : 0 < a := inv_pos.mpr (by linarith)
  have hale : a ≤ 1 := (inv_le_one₀ (by linarith : 0 < 1 + δ)).mpr (by linarith)
  have hamul : a * (1 + δ) = 1 := inv_mul_cancel₀ (by linarith : (1 + δ : ℝ) ≠ 0)
  refine ⟨G.scale a, (G.tsupport_scale_subset a).trans hGs, ?_, ?_⟩
  · intro x
    change ‖a • G x‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, ← hamul]
    apply mul_le_mul_of_nonneg_left ?_ ha.le
    have htri := norm_add_le (G x - f x) (f x)
    have he := hGe x
    have hu := hunit x
    rw [sub_add_cancel] at htri
    linarith
  · intro x
    change ‖a • G x - f x‖ < ε
    have hid : a • G x - f x = a • (G x - f x) + (a - 1) • f x := by module
    rw [hid]
    calc
      ‖a • (G x - f x) + (a - 1) • f x‖ ≤
          ‖a • (G x - f x)‖ + ‖(a - 1) • f x‖ := norm_add_le _ _
      _ = a * ‖G x - f x‖ + (1 - a) * ‖f x‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos ha, abs_of_nonpos (sub_nonpos.mpr hale)]
        ring
      _ < a * δ + (1 - a) := add_lt_add_of_lt_of_le
        (mul_lt_mul_of_pos_left (hGe x) ha)
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hunit x) (sub_nonneg.mpr hale))
      _ ≤ ε := by dsimp [δ] at *; nlinarith

end
end Poincare.SimonGMT.Chapter08.Varifold
