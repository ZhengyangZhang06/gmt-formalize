module

public import Poincare.SimonGMT.Chapter08.ConstancyTangent

@[expose] public section

/-!
# The nearest-projection clause for linear embedded subspaces

For the actual orthogonal nearest projection onto a linear subspace,
`p_# V = V` is equivalent to support on points and planes tangent to that
subspace. The proof uses the genuine Jacobian-weighted varifold
pushforward, including its zero-Jacobian locus.

This formalizes the flat specialization of the parenthetical equivalence
in Simon (8.4.2)(3); the curved embedded-manifold extension remains open.

Source: `Simon-gmt new.pdf`, printed p. 213, PDF object 219.
-/

open Set Filter MeasureTheory Function
open scoped Topology ENNReal

namespace Poincare.SimonGMT.Chapter08.Varifold
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
variable {N n : ℕ} {U : Set (Euclidean N)}

/-- The `n`-plane bundle tangent to a linear ambient subspace. -/
def linearTangentBundle (L : Submodule ℝ (Euclidean N)) :
    Set (Euclidean N × Grassmannian N n) := {z | z.1 ∈ L ∧ z.2.plane ≤ L}

theorem plane_le_iff_project_mem (L : Submodule ℝ (Euclidean N)) (S : Grassmannian N n) :
    S.plane ≤ L ↔ ∀ v, S.project v ∈ L := by
  constructor
  · intro h v
    exact h ⟨v, rfl⟩
  · intro h v hv
    obtain ⟨w, rfl⟩ := hv
    exact h w

theorem isClosed_planes_le (L : Submodule ℝ (Euclidean N)) :
    IsClosed {S : Grassmannian N n | S.plane ≤ L} := by
  have heq : {S : Grassmannian N n | S.plane ≤ L} =
      ⋂ v : Euclidean N, {S | S.project v ∈ L} := by
    ext S
    simp only [mem_ofPred_eq, mem_iInter]
    exact plane_le_iff_project_mem L S
  rw [heq]
  apply isClosed_iInter
  intro v
  have hp : Continuous (fun S : Grassmannian N n ↦ (S, v)) :=
    continuous_id.prodMk continuous_const
  exact L.closed_of_finiteDimensional.preimage
    ((Grassmannian.continuous_project (N := N) (n := n)).comp hp)

theorem isClosed_linearTangentBundle (L : Submodule ℝ (Euclidean N)) :
    IsClosed (linearTangentBundle (n := n) L) :=
  (L.closed_of_finiteDimensional.preimage continuous_fst).inter
    ((isClosed_planes_le (n := n) L).preimage continuous_snd)

theorem tangentialDerivative_starProjection (L : Submodule ℝ (Euclidean N))
    (x : Euclidean N) (S : Grassmannian N n) (hS : S.plane ≤ L) :
    tangentialDerivative L.starProjection x S = S.plane.subtype := by
  apply LinearMap.ext
  intro v
  change (fderiv ℝ (L.starProjection : Euclidean N → Euclidean N) x) v = (v : Euclidean N)
  rw [L.starProjection.hasFDerivAt.fderiv]
  exact Submodule.starProjection_eq_self_iff.mpr (hS v.property)

theorem tangentialJacobianReal_starProjection (L : Submodule ℝ (Euclidean N))
    (x : Euclidean N) (S : Grassmannian N n) (hS : S.plane ≤ L) :
    tangentialJacobianReal L.starProjection x S = 1 := by
  simp only [tangentialJacobianReal, tangentialDerivative_starProjection L x S hS]
  simp

theorem transportedPlane_starProjection (L : Submodule ℝ (Euclidean N))
    (x : Euclidean N) (S : Grassmannian N n) (hS : S.plane ≤ L) :
    transportedPlane L.starProjection x S = S := by
  apply Grassmannian.eq_of_plane_eq
  rw [transportedPlane_eq_image _ _ _
    (by rw [tangentialJacobianReal_starProjection L x S hS]; exact one_ne_zero),
    tangentialDerivative_starProjection L x S hS]
  exact Submodule.range_subtype _

/-- Every projected varifold is supported on the tangent bundle of the
target subspace. Degenerate image planes carry zero Jacobian weight. -/
theorem pushforwardMeasure_support_subset_linearTangentBundle (V : Varifold N n U)
    (L : Submodule ℝ (Euclidean N)) :
    (V.pushforwardMeasure L.starProjection).support ⊆ linearTangentBundle L := by
  apply Measure.support_subset_of_isClosed (isClosed_linearTangentBundle L)
  change ∀ᵐ z ∂V.pushforwardMeasure L.starProjection, z ∈ linearTangentBundle L
  have hF : Measurable (imageMap (n := n) L.starProjection) :=
    measurable_imageMap L.starProjection.contDiff
  have hB : MeasurableSet (linearTangentBundle (n := n) L) :=
    (isClosed_linearTangentBundle L).measurableSet
  have hJ : Measurable (fun z : Euclidean N × Grassmannian N n ↦
      tangentialJacobian L.starProjection z.1 z.2) :=
    ENNReal.measurable_ofReal.comp
      (continuous_tangentialJacobianReal L.starProjection.contDiff).measurable
  rw [pushforwardMeasure]
  apply (ae_map_iff hF.aemeasurable hB).mpr
  apply (ae_withDensity_iff hJ).mpr
  filter_upwards with z hz
  refine ⟨Submodule.coe_mem (L.orthogonalProjectionOnto z.1), ?_⟩
  change (transportedPlane L.starProjection z.1 z.2).plane ≤ L
  rw [transportedPlane_eq_image _ _ _ ((tangentialJacobian_ne_zero_iff _ _ _).mp hz)]
  rintro v ⟨w, rfl⟩
  change (fderiv ℝ (L.starProjection : Euclidean N → Euclidean N) z.1) w ∈ L
  rw [L.starProjection.hasFDerivAt.fderiv]
  exact Submodule.coe_mem (L.orthogonalProjectionOnto w)

/-- Conversely, on tangent points and planes the projection has unit
tangential Jacobian and fixes the entire bundle point. -/
theorem pushforwardMeasure_starProjection_eq_of_ae (V : Varifold N n U)
    (L : Submodule ℝ (Euclidean N))
    (hV : ∀ᵐ z ∂V.measure, z ∈ linearTangentBundle L) :
    V.pushforwardMeasure L.starProjection = V.measure := by
  have hJ : (fun z : Euclidean N × Grassmannian N n ↦
      tangentialJacobian L.starProjection z.1 z.2) =ᵐ[V.measure] 1 := by
    filter_upwards [hV] with z hz
    simp only [tangentialJacobian, tangentialJacobianReal_starProjection L z.1 z.2 hz.2,
      ENNReal.ofReal_one, Pi.one_apply]
  have hF : imageMap (n := n) L.starProjection =ᵐ[V.measure] id := by
    filter_upwards [hV] with z hz
    apply Prod.ext
    · exact Submodule.starProjection_eq_self_iff.mpr hz.1
    · exact transportedPlane_starProjection L z.1 z.2 hz.2
  rw [pushforwardMeasure, withDensity_congr_ae hJ, withDensity_one,
    Measure.map_congr hF, Measure.map_id]

/-- The exact support/projection equivalence in Remark (8.4.2)(3),
specialized to a linear embedded subspace and its actual nearest projection. -/
theorem pushforwardMeasure_starProjection_eq_iff (V : Varifold N n U)
    (L : Submodule ℝ (Euclidean N)) :
    V.pushforwardMeasure L.starProjection = V.measure ↔
      V.measure.support ⊆ linearTangentBundle L := by
  constructor
  · intro h
    rw [← h]
    exact V.pushforwardMeasure_support_subset_linearTangentBundle L
  · intro h
    apply V.pushforwardMeasure_starProjection_eq_of_ae L
    filter_upwards [V.measure.support_mem_ae] with z hz
    exact h hz

/-- Tangential divergence on a plane in `L` is unchanged by projecting
the test vector field onto the fixed ambient subspace `L`. -/
theorem tangentialDivergence_starProjection_comp (L : Submodule ℝ (Euclidean N))
    {X : Euclidean N → Euclidean N} {x : Euclidean N} (hX : DifferentiableAt ℝ X x)
    (S : Grassmannian N n) (hS : S.plane ≤ L) :
    tangentialDivergence (fun y ↦ L.starProjection (X y)) x S = tangentialDivergence X x S := by
  have hd : fderiv ℝ (fun y ↦ L.starProjection (X y)) x =
      L.starProjection.comp (fderiv ℝ X x) := by
    exact (L.starProjection.hasFDerivAt.comp x hX.hasFDerivAt).fderiv
  have hp : S.plane.starProjection.toLinearMap.comp L.starProjection.toLinearMap =
      S.plane.starProjection.toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap (Submodule.starProjection_comp_starProjection_of_le hS)
  rw [tangentialDivergence_eq_trace, hd, tangentialDivergence_eq_trace]
  change LinearMap.trace ℝ (Euclidean N)
      ((L.starProjection.toLinearMap.comp (fderiv ℝ X x).toLinearMap).comp
        S.plane.starProjection.toLinearMap) = _
  rw [LinearMap.comp_assoc,
    LinearMap.trace_comp_comm' ((fderiv ℝ X x).toLinearMap.comp S.plane.starProjection.toLinearMap)
      L.starProjection.toLinearMap, LinearMap.comp_assoc, hp]

def TestVectorField.projectTo (X : TestVectorField (N := N) U)
    (L : Submodule ℝ (Euclidean N)) : TestVectorField (N := N) U where
  toFun x := L.starProjection (X x)
  contDiff := L.starProjection.contDiff.comp X.contDiff
  compactSupport := X.compactSupport.comp_left (map_zero L.starProjection)
  support_subset := (tsupport_comp_subset (g := L.starProjection)
    (map_zero L.starProjection) X.toFun).trans X.support_subset

theorem firstVariation_projectTo (V : Varifold N n U) (L : Submodule ℝ (Euclidean N))
    (hplanes : ∀ᵐ z ∂V.measure, z.2.plane ≤ L) (X : TestVectorField (N := N) U) :
    V.firstVariation (X.projectTo L) = V.firstVariation X := by
  apply integral_congr_ae
  filter_upwards [hplanes] with z hz
  exact tangentialDivergence_starProjection_comp L X.contDiff.differentiable_one.differentiableAt z.2 hz

/-- The restricted testing convention in Remark (8.4.2)(3), for a fixed
linear embedded ambient subspace. -/
def StationaryAlong (V : Varifold N n U) (L : Submodule ℝ (Euclidean N)) : Prop :=
  ∀ X : TestVectorField (N := N) U, (∀ x ∈ L, X x ∈ L) → V.firstVariation X = 0

/-- For a flat ambient subspace and tangent bundle support, testing
only tangent vector fields is equivalent to ambient stationarity. This
uses the projected admissible test, not an assumed first-variation identity. -/
theorem stationaryAlong_iff_stationary (V : Varifold N n U)
    (L : Submodule ℝ (Euclidean N))
    (hplanes : ∀ᵐ z ∂V.measure, z.2.plane ≤ L) :
    V.StationaryAlong L ↔ V.Stationary := by
  constructor
  · intro hV X
    rw [← V.firstVariation_projectTo L hplanes X]
    apply hV
    intro x _
    exact Submodule.coe_mem (L.orthogonalProjectionOnto (X x))
  · intro hV X _
    exact hV X

end
end Poincare.SimonGMT.Chapter08.Varifold
