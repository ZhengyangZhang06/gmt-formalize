module

public import Poincare.SimonGMT.Chapter08.ConstancyLocalDefining
public import Poincare.SimonGMT.Chapter02.SubmanifoldTopology
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

@[expose] public section

/-!
# Normal defining functions from Simon's actual parametrizations

For Simon (8.4.1), proof (3), project a parametrization onto a linear
left inverse of its derivative and apply the inverse function theorem.
This constructs a local ambient coordinate retraction. Subtracting the
parametrization composed with that retraction gives a genuine local
`C²` defining map whose derivative kernel is the parametrized tangent.
Relative properness, through the checked chart topology, ensures that
the map vanishes on the whole local carrier, not only one parametrized
piece selected without neighborhood control.

Source: Simon, printed p. 214, PDF object 221.
-/

open Set Filter Function MeasureTheory
open scoped Topology

namespace Poincare.SimonGMT.Chapter08
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {N n : ℕ}

/-- A `C²` immersion has a local `C²` ambient coordinate left inverse.
The inverse is constructed by the actual inverse function theorem. -/
theorem exists_local_coordinate_leftInverse
    {φ : Euclidean n → Euclidean N} {a : Euclidean n}
    (hφ : ContDiffAt ℝ 2 φ a) (hinj : Injective (fderiv ℝ φ a)) :
    ∃ ψ : Euclidean N → Euclidean n,
      ContDiffAt ℝ 2 ψ (φ a) ∧ ψ (φ a) = a ∧
      (∀ᶠ u in 𝓝 a, ψ (φ u) = u) ∧
      (fderiv ℝ ψ (φ a)).comp (fderiv ℝ φ a) = ContinuousLinearMap.id ℝ (Euclidean n) := by
  obtain ⟨P₀, hP₀⟩ := (fderiv ℝ φ a).toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  let P : Euclidean N →L[ℝ] Euclidean n := P₀.toContinuousLinearMap
  have hP : P.comp (fderiv ℝ φ a) = ContinuousLinearMap.id ℝ (Euclidean n) := by
    apply ContinuousLinearMap.ext
    intro v
    exact LinearMap.congr_fun hP₀ v
  let g : Euclidean n → Euclidean n := fun u ↦ P (φ u)
  have hg : ContDiffAt ℝ 2 g a := P.contDiff.contDiffAt.comp a hφ
  have hgd : HasFDerivAt g (ContinuousLinearEquiv.refl ℝ (Euclidean n)).toContinuousLinearMap a := by
    have h := P.hasFDerivAt.comp a (hφ.differentiableAt (by norm_num)).hasFDerivAt
    simpa using! hP ▸ h
  have hn : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  let η := hg.localInverse hgd hn
  have hη : ContDiffAt ℝ 2 η (g a) := hg.to_localInverse hgd hn
  have hηa : η (g a) = a := hg.localInverse_apply_image hgd hn
  have hηg : ∀ᶠ u in 𝓝 a, η (g u) = u :=
    (hg.hasStrictFDerivAt' hgd hn).eventually_left_inverse
  let ψ : Euclidean N → Euclidean n := fun y ↦ η (P y)
  have hψ : ContDiffAt ℝ 2 ψ (φ a) := hη.comp (φ a) P.contDiff.contDiffAt
  have hleft : ∀ᶠ u in 𝓝 a, ψ (φ u) = u := hηg
  refine ⟨ψ, hψ, hηa, hleft, ?_⟩
  have hd := (hψ.differentiableAt (by norm_num)).hasFDerivAt.comp a
    (hφ.differentiableAt (by norm_num)).hasFDerivAt
  have heq : (ψ ∘ φ) =ᶠ[𝓝 a] id := hleft
  have hid := hd.congr_of_eventuallyEq heq.symm
  exact hid.unique (hasFDerivAt_id a)

/-- The elementary algebra behind the constructed normal map. -/
theorem ker_id_sub_comp_eq_range
    (A : Euclidean n →L[ℝ] Euclidean N) (B : Euclidean N →L[ℝ] Euclidean n)
    (hBA : B.comp A = ContinuousLinearMap.id ℝ (Euclidean n)) :
    (ContinuousLinearMap.id ℝ (Euclidean N) - A.comp B).ker = A.range := by
  apply Submodule.ext
  intro v
  constructor
  · intro hv
    have h : v - A (B v) = 0 := hv
    exact ⟨B v, (sub_eq_zero.mp h).symm⟩
  · rintro ⟨u, rfl⟩
    change A u - A (B (A u)) = 0
    have h := congrArg (fun L : Euclidean n →L[ℝ] Euclidean n ↦ L u) hBA
    change B (A u) = u at h
    rw [h, sub_self]

/-- From Simon's genuine local parametrization one obtains a local
`C²` defining map whose kernel is exactly its tangent space. -/
theorem exists_local_normal_defining_map
    {M W : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ)
    {a : Euclidean n} (ha : a ∈ D) :
    ∃ (A : Set (Euclidean N)) (F : Euclidean N → Euclidean N),
      IsOpen A ∧ φ a ∈ A ∧ ContDiffOn ℝ 2 F A ∧
      EqOn F (fun _ ↦ 0) (M ∩ A) ∧
      (fderiv ℝ F (φ a)).ker = (fderiv ℝ φ a).range := by
  have hφa : ContDiffAt ℝ 2 φ a :=
    (hφ.contDiffOn a ha).contDiffAt (hφ.isOpen_source.mem_nhds ha)
  obtain ⟨ψ, hψ, hψa, hleft, hdleft⟩ :=
    exists_local_coordinate_leftInverse hφa (hφ.injective_fderiv ha)
  have hφψ : ContDiffAt ℝ 2 φ (ψ (φ a)) := by simpa only [hψa] using hφa
  let F : Euclidean N → Euclidean N := fun y ↦ y - φ (ψ y)
  have hF : ContDiffAt ℝ 2 F (φ a) := contDiffAt_id.sub (hφψ.comp (φ a) hψ)
  have hleftD : D ∩ {u | ψ (φ u) = u} ∈ 𝓝 a :=
    inter_mem (hφ.isOpen_source.mem_nhds ha) hleft
  obtain ⟨D₀, hD₀, hD₀o, haD₀⟩ := mem_nhds_iff.mp hleftD
  have hD₀D : D₀ ⊆ D := hD₀.trans inter_subset_left
  obtain ⟨A₀, hA₀o, _, hA₀⟩ := hφ.exists_open_image_eq_inter hD₀o hD₀D
  have haA₀ : φ a ∈ A₀ := by
    have h : φ a ∈ φ '' D₀ := mem_image_of_mem φ haD₀
    rw [hA₀] at h
    exact h.1
  obtain ⟨B, hB, hFB⟩ := hF.contDiffOn le_rfl (by norm_num)
  obtain ⟨B₀, hB₀, hB₀o, haB₀⟩ := mem_nhds_iff.mp hB
  refine ⟨A₀ ∩ B₀, F, hA₀o.inter hB₀o, ⟨haA₀, haB₀⟩,
    hFB.mono (inter_subset_right.trans hB₀), ?_, ?_⟩
  · intro y hy
    obtain ⟨u, hu, rfl⟩ : y ∈ φ '' D₀ := by rw [hA₀]; exact ⟨hy.2.1, hy.1⟩
    have hinv : ψ (φ u) = u := (hD₀ hu).2
    simp only [F, hinv, sub_self]
  · have hd : fderiv ℝ F (φ a) = ContinuousLinearMap.id ℝ (Euclidean N) -
        (fderiv ℝ φ a).comp (fderiv ℝ ψ (φ a)) := by
      have h := (hasFDerivAt_id (φ a)).sub
        ((hφψ.differentiableAt (by norm_num)).hasFDerivAt.comp (φ a)
          (hψ.differentiableAt (by norm_num)).hasFDerivAt)
      simpa only [F, Function.comp_def, hψa, Pi.sub_def, id_eq] using! h.fderiv
    rw [hd]
    exact ker_id_sub_comp_eq_range _ _ hdleft

/-- The defining map has the source dimension as its kernel dimension.
This rank condition is derived from injectivity of the parametrization. -/
theorem simonSubmanifold_exists_local_normal_defining_map
    {M : Set (Euclidean N)}
    (hM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M)
    {x : Euclidean N} (hx : x ∈ M) :
    ∃ (A : Set (Euclidean N)) (F : Euclidean N → Euclidean N),
      IsOpen A ∧ x ∈ A ∧ ContDiffOn ℝ 2 F A ∧
      EqOn F (fun _ ↦ 0) (M ∩ A) ∧ Module.finrank ℝ (fderiv ℝ F x).ker = n := by
  obtain ⟨D, W, φ, hxW, hφ⟩ := hM.exists_localRepresentation hx
  obtain ⟨a, ha, rfl⟩ : x ∈ φ '' D := by rw [hφ.image_eq]; exact ⟨hxW, hx⟩
  obtain ⟨A, F, hAo, hxA, hF, hFM, hker⟩ := exists_local_normal_defining_map hφ ha
  refine ⟨A, F, hAo, hxA, hF, hFM, ?_⟩
  rw [hker]
  simpa using
    LinearMap.finrank_range_of_inj (hφ.injective_fderiv ha)

/-- The parametrized tangent is independent of the actual Simon chart.
This follows from the constructed defining map and the chain rule. -/
theorem parametrizedTangent_eq_of_overlap
    {M W W' : Set (Euclidean N)} {D D' : Set (Euclidean n)}
    {φ ψ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ)
    (hψ : Chapter02.IsSimonLocalRepresentation 2 M D' W' ψ)
    {a b : Euclidean n} (ha : a ∈ D) (hb : b ∈ D') (hab : φ a = ψ b) :
    (fderiv ℝ φ a).range = (fderiv ℝ ψ b).range := by
  obtain ⟨A, F, hAo, haA, hF, hFM, hker⟩ := exists_local_normal_defining_map hφ ha
  have hbA : ψ b ∈ A := hab ▸ haA
  have hψb : ContDiffAt ℝ 2 ψ b :=
    (hψ.contDiffOn b hb).contDiffAt (hψ.isOpen_source.mem_nhds hb)
  have hzero : (F ∘ ψ) =ᶠ[𝓝 b] (fun _ ↦ 0) := by
    filter_upwards [hψ.isOpen_source.mem_nhds hb,
      hψb.continuousAt (hAo.mem_nhds hbA)] with u hu huA
    have huM : ψ u ∈ M := by
      have h : ψ u ∈ ψ '' D' := mem_image_of_mem ψ hu
      rw [hψ.image_eq] at h
      exact h.2
    exact hFM ⟨huM, huA⟩
  have hd := (((hF (ψ b) hbA).contDiffAt (hAo.mem_nhds hbA)).differentiableAt
    (by norm_num)).hasFDerivAt.comp b (hψb.differentiableAt (by norm_num)).hasFDerivAt
  have hd0 : (fderiv ℝ F (ψ b)).comp (fderiv ℝ ψ b) = 0 :=
    (hd.congr_of_eventuallyEq hzero.symm).unique (hasFDerivAt_const (0 : Euclidean N) b)
  have hle : (fderiv ℝ ψ b).range ≤ (fderiv ℝ φ a).range := by
    rw [← hker, hab]
    rintro v ⟨u, rfl⟩
    exact congrArg (fun L : Euclidean n →L[ℝ] Euclidean N ↦ L u) hd0
  symm
  apply Submodule.eq_of_le_of_finrank_eq hle
  exact (LinearMap.finrank_range_of_inj (hψ.injective_fderiv hb)).trans
    (LinearMap.finrank_range_of_inj (hφ.injective_fderiv ha)).symm

namespace Varifold
variable {U M W : Set (Euclidean N)}

/-- Actual Simon manifold parametrizations determine every support
plane, without a normal-family or tangent-identity premise. -/
theorem Stationary.plane_eq_parametrizedTangent {V : Varifold N n U}
    (hV : V.Stationary) (hM : U ∩ V.weight.support ⊆ M)
    {D : Set (Euclidean n)} {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ)
    {a : Euclidean n} (ha : a ∈ D)
    {S : Grassmannian N n} (hz : (φ a, S) ∈ V.measure.support) (haU : φ a ∈ U) :
    S.plane = (fderiv ℝ φ a).range := by
  obtain ⟨A, F, hAo, haA, hF, hFM, hker⟩ := exists_local_normal_defining_map hφ ha
  have hle := hV.plane_le_ker_fderiv_of_local_level_set hM hAo hF hFM hz haU haA
  rw [hker] at hle
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [S.finrank_plane]
  symm
  simpa using
    LinearMap.finrank_range_of_inj (hφ.injective_fderiv ha)

/-- In particular, no two different planes occur over the same carrier
point for a stationary varifold satisfying the actual manifold hypothesis. -/
theorem Stationary.support_fiber_subsingleton {V : Varifold N n U}
    (hV : V.Stationary) (hM : U ∩ V.weight.support ⊆ M)
    (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M)
    {x : Euclidean N} (hxU : x ∈ U) {S T : Grassmannian N n}
    (hS : (x, S) ∈ V.measure.support) (hT : (x, T) ∈ V.measure.support) : S = T := by
  have hxM : x ∈ M := hM ⟨hxU, V.fst_mem_weight_support_of_mem_support hS⟩
  obtain ⟨D, W, φ, hxW, hφ⟩ := hSM.exists_localRepresentation hxM
  obtain ⟨a, ha, rfl⟩ : x ∈ φ '' D := by rw [hφ.image_eq]; exact ⟨hxW, hxM⟩
  apply Grassmannian.eq_of_plane_eq
  exact (hV.plane_eq_parametrizedTangent hM hφ ha hS hxU).trans
    (hV.plane_eq_parametrizedTangent hM hφ ha hT hxU).symm

end Varifold
end
end Poincare.SimonGMT.Chapter08
