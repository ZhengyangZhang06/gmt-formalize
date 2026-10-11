module

public import Poincare.SimonGMT.Chapter08.ConstancyManifoldGluing

@[expose] public section

/-!
# Corrected constancy in arbitrary codimension

The printed connectedness of a larger carrier M does not imply
connectedness of M ∩ U. Under the explicit corrected hypothesis that
M ∩ U is connected, the actual stationary varifold has one finite
constant multiplicity there. The statement remains localized to U.

Source: Simon, Chapter 8, Theorem 4.1, printed pp. 213--214.
-/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

namespace Poincare.SimonGMT.Chapter08
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {N n : ℕ}

/-- Every manifold point in the open domain belongs to the support of
the restricted Hausdorff measure. -/
theorem mem_support_simonHausdorff_restrict_manifold
    {M U : Set (Euclidean N)}
    (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M)
    (hU : IsOpen U) {x : Euclidean N} (hxM : x ∈ M) (hxU : x ∈ U) :
    x ∈ ((Chapter01.simonHausdorffMeasureReal (n : ℝ)).restrict (M ∩ U)).support := by
  let : (simonManifoldMeasure n M).IsOpenPosMeasure := isOpenPosMeasure_simonManifoldMeasure hSM
  rw [(nhds_basis_opens x).mem_measureSupport]
  rintro O ⟨hxO, hOo⟩
  have hp := ((hOo.inter hU).preimage (continuous_subtype_val (p := (· ∈ M)))).measure_pos
    (simonManifoldMeasure n M) ⟨⟨x, hxM⟩, hxO, hxU⟩
  rw [simonManifoldMeasure,
    (MeasurableEmbedding.subtype_coe (simonSubmanifold_measurableSet hSM)).comap_preimage,
    Subtype.range_coe] at hp
  rw [Measure.restrict_apply hOo.measurableSet]
  convert hp using 1
  congr 1
  ext y
  simp only [mem_inter_iff]
  tauto

namespace Varifold
variable {U M : Set (Euclidean N)}

/-- The corrected weight-level constancy theorem, with no codimension
restriction, no extra analytic premise, and no mass outside U asserted. -/
theorem Stationary.exists_const_simonHausdorff_connectedCarrier
    {V : Varifold N n U} (hV : V.Stationary)
    (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M)
    (hM : U ∩ V.weight.support ⊆ M) (hconn : IsPreconnected (M ∩ U)) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ V.weight =
      c • (Chapter01.simonHausdorffMeasureReal (n : ℝ)).restrict (M ∩ U) := by
  obtain ⟨c, hc⟩ := hV.density_ae_eq_const_of_connected_domain_carrier hSM hM hconn
  have hUa : ∀ᵐ x ∂V.weight, x ∈ U := by
    rw [ae_iff]
    change V.weight Uᶜ = 0
    rw [V.weight_apply V.isOpen_domain.measurableSet.compl]
    exact V.supported
  have hrestrict := Measure.restrict_eq_self_of_ae_mem hUa
  have hρ := (hV.constancyDensity_representation hSM hM).2.2.2
  have hrep : V.weight =
      ((Chapter01.simonHausdorffMeasureReal (n : ℝ)).restrict (M ∩ U)).withDensity
        (fun x ↦ ENNReal.ofReal (V.constancyDensity M x)) := by
    conv_lhs => rw [← hrestrict, ← hρ, restrict_withDensity V.isOpen_domain.measurableSet,
      Measure.restrict_restrict V.isOpen_domain.measurableSet, inter_comm U M]
  refine ⟨ENNReal.ofReal c, ENNReal.ofReal_ne_top, ?_⟩
  rw [hrep]
  calc
    _ = ((Chapter01.simonHausdorffMeasureReal (n : ℝ)).restrict (M ∩ U)).withDensity
        (fun _ ↦ ENNReal.ofReal c) := by
      apply withDensity_congr_ae
      filter_upwards [hc] with x hx
      exact congrArg ENNReal.ofReal hx
    _ = _ := withDensity_const _

/-- A nonzero constant multiplicity puts every actual carrier point
in the weight support. This is not the false closure assertion about a
larger carrier outside the actual domain. -/
theorem mem_weight_support_of_const_simonHausdorff
    {V : Varifold N n U}
    (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M)
    {c : ℝ≥0∞} (hc : c ≠ 0)
    (hweight : V.weight = c •
      (Chapter01.simonHausdorffMeasureReal (n : ℝ)).restrict (M ∩ U))
    {x : Euclidean N} (hxM : x ∈ M) (hxU : x ∈ U) : x ∈ V.weight.support := by
  have hx := mem_support_simonHausdorff_restrict_manifold hSM V.isOpen_domain hxM hxU
  rw [hweight, Measure.mem_support_iff_forall]
  intro A hA
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_pos hc ((Measure.mem_support_iff_forall _).mp hx A hA).ne'

/-- Corrected constancy for the entire Grassmann-bundle measure.
The measurable tangent field is constructed, and wherever the constant
is nonzero it agrees with every actual chart tangent throughout M ∩ U. -/
theorem Stationary.exists_const_tangentGraph_connectedCarrier
    {V : Varifold N n U} (hV : V.Stationary)
    (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M)
    (hM : U ∩ V.weight.support ⊆ M) (hne : M.Nonempty)
    (hconn : IsPreconnected (M ∩ U)) :
    ∃ (c : ℝ≥0∞) (T : Euclidean N → Grassmannian N n), c ≠ ⊤ ∧
      Measurable T ∧ ContinuousOn T (U ∩ V.weight.support) ∧
      V.weight = c • (Chapter01.simonHausdorffMeasureReal (n : ℝ)).restrict (M ∩ U) ∧
      V.measure = (c • (Chapter01.simonHausdorffMeasureReal (n : ℝ)).restrict (M ∩ U)).map
        (fun x ↦ (x, T x)) ∧
      ∀ {W : Set (Euclidean N)} {D : Set (Euclidean n)}
        {φ : Euclidean n → Euclidean N},
        Chapter02.IsSimonLocalRepresentation 2 M D W φ →
        ∀ a ∈ D, φ a ∈ U → c ≠ 0 → (T (φ a)).plane = (fderiv ℝ φ a).range := by
  obtain ⟨c, hc, hweight⟩ := hV.exists_const_simonHausdorff_connectedCarrier hSM hM hconn
  obtain ⟨T, hTm, hTc, hTeq, hgraph⟩ := hV.exists_measurable_tangentGraph hM hSM hne
  refine ⟨c, T, hc, hTm, hTc, hweight, hweight ▸ hgraph, ?_⟩
  intro W D φ hφ a ha haU hc0
  have haM : φ a ∈ M := by
    have h : φ a ∈ φ '' D := mem_image_of_mem φ ha
    rw [hφ.image_eq] at h
    exact h.2
  have hsupp := mem_weight_support_of_const_simonHausdorff hSM hc0 hweight haM haU
  rw [V.weight_support_eq_fst_image_support] at hsupp
  obtain ⟨⟨y, S⟩, hz, hy⟩ := hsupp
  change y = φ a at hy
  have hz' : (φ a, S) ∈ V.measure.support := by simpa only [hy] using hz
  rw [← hTeq (φ a) haU S hz']
  exact hV.plane_eq_parametrizedTangent hM hφ ha hz' haU

/-- The customary formulation with M contained in U is valid in every
codimension; in that case connectedness of M is sufficient. -/
theorem Stationary.exists_const_simonHausdorff_carrier_of_subset
    {V : Varifold N n U} (hV : V.Stationary)
    (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M)
    (hM : U ∩ V.weight.support ⊆ M) (hMU : M ⊆ U) (hconn : IsPreconnected M) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ V.weight =
      c • (Chapter01.simonHausdorffMeasureReal (n : ℝ)).restrict M := by
  have h := hV.exists_const_simonHausdorff_connectedCarrier hSM hM
    (by simpa only [inter_eq_left.mpr hMU] using hconn)
  simpa only [inter_eq_left.mpr hMU] using h

end Varifold
end
end Poincare.SimonGMT.Chapter08
