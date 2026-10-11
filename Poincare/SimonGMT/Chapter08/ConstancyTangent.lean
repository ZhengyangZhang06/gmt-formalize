module

public import Poincare.SimonGMT.Chapter08.ConstancySupport

@[expose] public section

/-!
# Tangent-plane concentration in Simon's constancy argument

The nonnegative test gives the exact plane and measure conclusions in
proof (3)--(4) of (8.4.1), once normal defining functions are available.
For an affine plane, those functions are constructed explicitly; no
normal-family assumption is needed in that specialization.

The general `C²`-submanifold-to-defining-functions bridge and the later
Hausdorff-density and distributional-constancy steps are not asserted.

Source: `Simon-gmt new.pdf`, printed p. 214, PDF object 221.
-/

open Set Filter MeasureTheory Function InnerProductSpace
open scoped Topology ENNReal

namespace Poincare.SimonGMT.Chapter08
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
variable {N n : ℕ}

namespace Grassmannian

theorem eq_of_plane_eq {S T : Grassmannian N n} (h : S.plane = T.plane) : S = T := by
  apply Subtype.ext
  rw [← S.toMatrix_projectionLinearMap, ← T.toMatrix_projectionLinearMap,
    S.projectionLinearMap_eq_starProjection, T.projectionLinearMap_eq_starProjection, h]

/-- Equal dimensions turn annihilation of the candidate normal space
into equality of the represented tangent planes. -/
theorem eq_of_project_orthogonal_eq_zero {S T : Grassmannian N n}
    (h : ∀ v ∈ T.planeᗮ, S.project v = 0) : S = T := by
  have horth : T.planeᗮ ≤ S.planeᗮ := by
    intro v hv
    rw [← Submodule.ker_starProjection]
    change S.plane.starProjection v = 0
    rw [← S.project_eq_starProjection]
    exact h v hv
  apply eq_of_plane_eq
  exact Submodule.eq_of_le_of_finrank_eq
    (Submodule.orthogonal_le_orthogonal_iff.mp horth)
    (S.finrank_plane.trans T.finrank_plane.symm)

end Grassmannian

namespace Varifold
variable {U : Set (Euclidean N)}

/-- A finite family of genuine `C²` defining functions identifies the
plane at a support point. Compact localization is constructed by the
preceding module rather than imposed on the defining functions. -/
theorem Stationary.plane_eq_of_normal_defining_family {V : Varifold N n U}
    (hV : V.Stationary) {M : Set (Euclidean N)} (hM : U ∩ V.weight.support ⊆ M)
    {z : Euclidean N × Grassmannian N n} (hz : z ∈ V.measure.support) (hzU : z.1 ∈ U)
    (T : Grassmannian N n) {k : ℕ} (f : Fin k → Euclidean N → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hfM : ∀ i, EqOn (f i) (fun _ ↦ 0) M)
    (hspan : Submodule.span ℝ (range fun i ↦ gradient (f i) z.1) = T.planeᗮ) :
    z.2 = T := by
  have hker : Submodule.span ℝ (range fun i ↦ gradient (f i) z.1) ≤
      LinearMap.ker z.2.projectionLinearMap := by
    apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    exact hV.project_gradient_eq_zero_of_vanishing hM (hf i) (hfM i) hz hzU
  rw [hspan] at hker
  exact Grassmannian.eq_of_project_orthogonal_eq_zero (fun v hv ↦ hker hv)

/-- The actual measure is recovered from its weight when its plane
coordinate is almost everywhere determined. This is an equality of
measures, not merely a postulated disintegration identity. -/
theorem measure_eq_map_tangentGraph (V : Varifold N n U)
    (T : Euclidean N → Grassmannian N n) (hT : Measurable T)
    (hplane : ∀ᵐ z ∂V.measure, z.2 = T z.1) :
    V.measure = V.weight.map (fun x ↦ (x, T x)) := by
  have hgraph : Measurable (fun x ↦ (x, T x)) := measurable_id.prodMk hT
  rw [weight, Measure.map_map hgraph measurable_fst]
  calc
    V.measure = V.measure.map id := Measure.map_id.symm
    _ = V.measure.map ((fun x ↦ (x, T x)) ∘ Prod.fst) := by
      apply Measure.map_congr
      filter_upwards [hplane] with z hz
      exact Prod.ext rfl hz

/-- The integral form printed as proof (4), before any assertion of
absolute continuity with respect to Hausdorff measure. -/
theorem integral_eq_tangentGraph (V : Varifold N n U)
    (T : Euclidean N → Grassmannian N n) (hT : Measurable T)
    (hplane : ∀ᵐ z ∂V.measure, z.2 = T z.1)
    {F : Euclidean N × Grassmannian N n → ℝ} (hF : Continuous F) :
    (∫ z, F z ∂V.measure) = ∫ x, F (x, T x) ∂V.weight := by
  rw [V.measure_eq_map_tangentGraph T hT hplane]
  exact integral_map (measurable_id.prodMk hT).aemeasurable hF.aestronglyMeasurable

/-- The local normal-family input from the source yields the global
bundle-measure conclusion by actual support concentration. The input
records geometric defining functions, not the desired plane identity. -/
theorem Stationary.measure_eq_map_tangentGraph_of_defining_functions {V : Varifold N n U}
    (hV : V.Stationary) {M : Set (Euclidean N)} (hM : U ∩ V.weight.support ⊆ M)
    (T : Euclidean N → Grassmannian N n) (hT : Measurable T)
    (hdef : ∀ x ∈ M, ∃ k : ℕ, ∃ f : Fin k → Euclidean N → ℝ,
      (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, EqOn (f i) (fun _ ↦ 0) M) ∧
        Submodule.span ℝ (range fun i ↦ gradient (f i) x) = (T x).planeᗮ) :
    V.measure = V.weight.map (fun x ↦ (x, T x)) := by
  apply V.measure_eq_map_tangentGraph T hT
  filter_upwards [V.measure.support_mem_ae, V.ae_mem_domain,
    V.ae_mem_carrier_of_support_subset hM] with z hz hzU hzM
  obtain ⟨k, f, hf, hfM, hspan⟩ := hdef z.1 hzM
  exact hV.plane_eq_of_normal_defining_family hM hz hzU.1 (T z.1) f hf hfM hspan

/-- In the affine-plane case, the defining functions are explicitly
the normal linear coordinates `y ↦ ⟨v,y-a⟩`. -/
theorem Stationary.plane_eq_of_affine_carrier {V : Varifold N n U}
    (hV : V.Stationary) (a : Euclidean N) (T : Grassmannian N n)
    (hM : U ∩ V.weight.support ⊆ {x | x - a ∈ T.plane})
    {z : Euclidean N × Grassmannian N n} (hz : z ∈ V.measure.support) (hzU : z.1 ∈ U) :
    z.2 = T := by
  apply Grassmannian.eq_of_project_orthogonal_eq_zero
  intro v hv
  let f : Euclidean N → ℝ := fun y ↦ inner ℝ v (y - a)
  have hf : ContDiff ℝ 2 f := by
    simpa only [f, Function.comp_def, innerSL_apply_apply, id_eq] using
      (innerSL ℝ v).contDiff.comp (contDiff_id.sub contDiff_const)
  have hfM : EqOn f (fun _ ↦ 0) {x | x - a ∈ T.plane} := by
    intro x hx
    exact T.plane.inner_left_of_mem_orthogonal hx hv
  have hgrad : gradient f z.1 = v := by
    have hd : HasFDerivAt f (innerSL ℝ v) z.1 := by
      simpa only [f, Function.comp_def, innerSL_apply_apply, ContinuousLinearMap.comp_id] using
        (innerSL ℝ v).hasFDerivAt.comp z.1 (hasFDerivAt_sub_const a)
    apply (toDual ℝ (Euclidean N)).injective
    rw [toDual_gradient, hd.fderiv]
    rfl
  have hp := hV.project_gradient_eq_zero_of_vanishing hM hf hfM hz hzU
  rwa [hgrad] at hp

/-- Stationarity and support on an affine plane determine the entire
Grassmann-bundle measure from the weight. Constancy of that weight is
not assumed or claimed in this intermediate theorem. -/
theorem Stationary.measure_eq_map_of_affine_carrier {V : Varifold N n U}
    (hV : V.Stationary) (a : Euclidean N) (T : Grassmannian N n)
    (hM : U ∩ V.weight.support ⊆ {x | x - a ∈ T.plane}) :
    V.measure = V.weight.map (fun x ↦ (x, T)) := by
  apply V.measure_eq_map_tangentGraph (fun _ ↦ T) measurable_const
  filter_upwards [V.measure.support_mem_ae, V.ae_mem_domain] with z hz hzU
  exact hV.plane_eq_of_affine_carrier a T hM hz hzU.1

end Varifold
end
end Poincare.SimonGMT.Chapter08
