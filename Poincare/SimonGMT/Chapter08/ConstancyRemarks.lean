module

public import Poincare.SimonGMT.Chapter08.ConstancyCorrected
public import Poincare.SimonGMT.Chapter08.ConstancyFullDimension

@[expose] public section

/-!
# Valid corrected clauses of Simon's Remark 8.4.2

The relative-closedness conclusion in (1) requires the same correction
as the constancy theorem: connectedness of M ∩ U. In (3) the literal PDF
specifies an N-dimensional ambient submanifold of R^N. Such a submanifold
is open, and its tangent space is the entire ambient vector space. We
formalize that literal clause; no positive-codimension curved extension
or Lipschitz regularity extension is claimed here.
-/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

namespace Poincare.SimonGMT.Chapter08
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {N n k : ℕ}

/-- Tangency defined by an actual regular Simon parametrization. -/
def IsManifoldTangentVector (k : ℕ) (P : Set (Euclidean N))
    (x v : Euclidean N) : Prop :=
  ∃ (D : Set (Euclidean k)) (W : Set (Euclidean N))
    (φ : Euclidean k → Euclidean N),
    Chapter02.IsSimonLocalRepresentation 2 P D W φ ∧
    ∃ a ∈ D, φ a = x ∧ v ∈ (fderiv ℝ φ a).range

/-- A full-dimensional regular chart has the whole ambient tangent. -/
theorem range_fderiv_fullDimensional_chart
    {P W D : Set (Euclidean N)} {φ : Euclidean N → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 P D W φ)
    {a : Euclidean N} (ha : a ∈ D) : (fderiv ℝ φ a).range = ⊤ :=
  LinearMap.range_eq_top.mpr (LinearMap.surjective_of_injective (hφ.injective_fderiv ha))

/-- For the exact dimensions in the printed Remark (3), every vector
is tangent at every point of the ambient submanifold. -/
theorem isManifoldTangentVector_fullDimension
    {P : Set (Euclidean N)}
    (hP : Chapter02.IsSimonSubmanifold (E := Euclidean N) 2 P)
    {x : Euclidean N} (hx : x ∈ P) (v : Euclidean N) :
    IsManifoldTangentVector N P x v := by
  obtain ⟨D, W, φ, hxW, hφ⟩ := hP.exists_localRepresentation hx
  obtain ⟨a, ha, hax⟩ : x ∈ φ '' D := by rw [hφ.image_eq]; exact ⟨hxW, hx⟩
  refine ⟨D, W, φ, hφ, a, ha, hax, ?_⟩
  rw [range_fderiv_fullDimensional_chart hφ ha]
  trivial

namespace Varifold
variable {U M P : Set (Euclidean N)}

/-- Relative stationarity uses only fields tangent to the actual
embedded ambient submanifold, with tangency defined through its charts. -/
def StationaryAlongManifold (V : Varifold N n U) (k : ℕ)
    (P : Set (Euclidean N)) : Prop :=
  ∀ X : TestVectorField (N := N) U,
    (∀ x ∈ P, IsManifoldTangentVector k P x (X x)) → V.firstVariation X = 0

/-- The literal full-dimensional relative-stationarity clause is
equivalent to ambient stationarity, not a new assumed first variation. -/
theorem stationaryAlongManifold_fullDimension_iff (V : Varifold N n U)
    (hP : Chapter02.IsSimonSubmanifold (E := Euclidean N) 2 P) :
    V.StationaryAlongManifold N P ↔ V.Stationary := by
  constructor
  · intro hV X
    exact hV X (fun x hx ↦ isManifoldTangentVector_fullDimension hP hx (X x))
  · intro hV X _
    exact hV X

/-- Corrected Remark (1): a nonzero varifold has the whole actual
connected carrier as its support inside U. -/
theorem Stationary.support_inter_domain_eq_carrier
    {V : Varifold N n U} (hV : V.Stationary)
    (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M)
    (hM : U ∩ V.weight.support ⊆ M) (hconn : IsPreconnected (M ∩ U))
    (hne : V.measure ≠ 0) : V.weight.support ∩ U = M ∩ U := by
  obtain ⟨c, _, hc⟩ := hV.exists_const_simonHausdorff_connectedCarrier hSM hM hconn
  have hc0 : c ≠ 0 := by
    intro hz
    have hw : V.weight = 0 := by simpa only [hz, zero_smul] using hc
    apply hne
    apply Measure.measure_univ_eq_zero.mp
    have h : V.weight univ = 0 := by rw [hw]; rfl
    rw [weight, Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ] at h
    exact h
  apply subset_antisymm
  · intro x hx
    exact ⟨hM ⟨hx.2, hx.1⟩, hx.2⟩
  · intro x hx
    exact ⟨mem_weight_support_of_const_simonHausdorff hSM hc0 hc hx.1 hx.2, hx.2⟩

/-- The relative closedness printed in Remark (1), under the explicit
corrected domain-connectedness hypothesis. -/
theorem Stationary.closure_sdiff_carrier_inter_domain_eq_empty
    {V : Varifold N n U} (hV : V.Stationary)
    (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M)
    (hM : U ∩ V.weight.support ⊆ M) (hconn : IsPreconnected (M ∩ U))
    (hne : V.measure ≠ 0) : (closure M \ M) ∩ U = ∅ := by
  have hs := hV.support_inter_domain_eq_carrier hSM hM hconn hne
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxs : x ∈ V.weight.support := by
    by_contra hh
    have hO : IsOpen (U ∩ V.weight.supportᶜ) :=
      V.isOpen_domain.inter V.weight.isClosed_support.isOpen_compl
    obtain ⟨y, hyO, hyM⟩ := (mem_closure_iff_nhds.mp hx.1.1) _ (hO.mem_nhds ⟨hx.2, hh⟩)
    exact hyO.2 ((hs.symm ▸ (show y ∈ M ∩ U from ⟨hyM, hyO.1⟩)).1)
  exact hx.1.2 (hM ⟨hx.2, hxs⟩)

/-- Corrected constancy for the exact relative-stationarity clause in
the PDF: its ambient submanifold has full dimension. -/
theorem StationaryAlongManifold.exists_const_tangentGraph_fullDimension
    {V : Varifold N n U} (hV : V.StationaryAlongManifold N P)
    (hP : Chapter02.IsSimonSubmanifold (E := Euclidean N) 2 P)
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
  exact Stationary.exists_const_tangentGraph_connectedCarrier
    ((V.stationaryAlongManifold_fullDimension_iff hP).mp hV) hSM hM hne hconn

/-- Any map fixing an open ambient submanifold is locally the identity
at its points; its actual varifold pushforward fixes measures supported
there. This includes the nearest-projection clause in the literal
full-dimensional Remark (3). -/
theorem pushforwardMeasure_eq_of_fullDimensional_retraction
    (V : Varifold N n U)
    (hP : Chapter02.IsSimonSubmanifold (E := Euclidean N) 2 P)
    {p : Euclidean N → Euclidean N} (hp : EqOn p id P)
    (hsupp : V.weight.support ⊆ P) : V.pushforwardMeasure p = V.measure := by
  have hPo := isOpen_simonSubmanifold_fullDimension hP
  have hpoint : ∀ᵐ z ∂V.measure, p =ᶠ[𝓝 z.1] id := by
    filter_upwards [V.measure.support_mem_ae] with z hz
    exact Filter.mem_of_superset
      (hPo.mem_nhds (hsupp (V.fst_mem_weight_support_of_mem_support hz))) (fun y hy ↦ hp hy)
  have hJ : (fun z : Euclidean N × Grassmannian N n ↦
      tangentialJacobian p z.1 z.2) =ᵐ[V.measure] 1 := by
    filter_upwards [hpoint] with z hz
    have hd := hz.fderiv_eq (𝕜 := ℝ)
    have hder : tangentialDerivative p z.1 z.2 = z.2.plane.subtype := by
      apply LinearMap.ext
      intro v
      simp only [tangentialDerivative, hd, fderiv_id]
      rfl
    simp [tangentialJacobian, tangentialJacobianReal, hder]
  have hF : imageMap (n := n) p =ᵐ[V.measure] id := by
    filter_upwards [hpoint] with z hz
    apply Prod.ext
    · exact hz.self_of_nhds
    · change transportedPlane p z.1 z.2 = z.2
      have hd := hz.fderiv_eq (𝕜 := ℝ)
      have hder : tangentialDerivative p z.1 z.2 = z.2.plane.subtype := by
        apply LinearMap.ext
        intro v
        simp only [tangentialDerivative, hd, fderiv_id]
        rfl
      apply Grassmannian.eq_of_plane_eq
      rw [transportedPlane_eq_image _ _ _ (by simp [tangentialJacobianReal, hder]), hder]
      exact Submodule.range_subtype _
  rw [pushforwardMeasure, withDensity_congr_ae hJ, withDensity_one,
    Measure.map_congr hF, Measure.map_id]

/-- The actual tangent-plane bundle of an embedded ambient manifold. -/
def manifoldTangentBundle (k : ℕ) (P : Set (Euclidean N)) :
    Set (Euclidean N × Grassmannian N n) :=
  {z | z.1 ∈ P ∧ ∀ v ∈ z.2.plane, IsManifoldTangentVector k P z.1 v}

/-- The parenthetical support/projection equivalence in the literal
full-dimensional version of Remark (3). A nearest projection fixes every
point of its target; no artificial projection-invariance hypothesis is
needed in the forward direction. -/
theorem support_subset_manifoldTangentBundle_iff_fullDimension
    (V : Varifold N n U)
    (hP : Chapter02.IsSimonSubmanifold (E := Euclidean N) 2 P)
    {p : Euclidean N → Euclidean N} (hp : EqOn p id P) :
    V.measure.support ⊆ manifoldTangentBundle (n := n) N P ↔
      V.weight.support ⊆ P ∧ V.pushforwardMeasure p = V.measure := by
  have hsp : V.measure.support ⊆ manifoldTangentBundle (n := n) N P ↔
      V.weight.support ⊆ P := by
    constructor
    · intro h x hx
      rw [V.weight_support_eq_fst_image_support] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      exact (h hz).1
    · intro h z hz
      have hx := h (V.fst_mem_weight_support_of_mem_support hz)
      exact ⟨hx, fun v _ ↦ isManifoldTangentVector_fullDimension hP hx v⟩
  rw [hsp]
  exact ⟨fun h ↦ ⟨h, V.pushforwardMeasure_eq_of_fullDimensional_retraction hP hp h⟩,
    And.left⟩

end Varifold
end
end Poincare.SimonGMT.Chapter08
