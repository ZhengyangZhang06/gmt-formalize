module

public import Poincare.SimonGMT.Chapter08.ConstancyCoordinateTests

@[expose] public section

/-!
# Actual supported tangent coordinate tests

Local coordinate inverses and ambient bump functions extend every
compactly supported scalar coordinate test to an admissible ambient
vector field. All neighborhoods remain inside the actual open domain.
-/

open Set Function Filter MeasureTheory Metric
open scoped Topology

namespace Poincare.SimonGMT.Chapter08
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {N n : ℕ}

/-- A genuine Simon chart has a smooth ambient coordinate inverse on
a neighborhood, valid on every part of the carrier in that neighborhood. -/
theorem exists_chart_coordinate_inverse_on_neighborhood
    {M W U : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ)
    (hU : IsOpen U) {a : Euclidean n} (ha : a ∈ D) (haU : φ a ∈ U) :
    ∃ (A : Set (Euclidean N)) (ψ : Euclidean N → Euclidean n),
      IsOpen A ∧ φ a ∈ A ∧ A ⊆ W ∩ U ∧ ContDiffOn ℝ 2 ψ A ∧
      MapsTo ψ A D ∧ ∀ u ∈ D, φ u ∈ A → ψ (φ u) = u := by
  have hφa : ContDiffAt ℝ 2 φ a :=
    (hφ.contDiffOn a ha).contDiffAt (hφ.isOpen_source.mem_nhds ha)
  obtain ⟨ψ, hψ, hψa, hleft, _⟩ :=
    exists_local_coordinate_leftInverse hφa (hφ.injective_fderiv ha)
  obtain ⟨D₀, hD₀, hD₀o, haD₀⟩ := _root_.mem_nhds_iff.mp
    (inter_mem (hφ.isOpen_source.mem_nhds ha) hleft)
  have hD₀D : D₀ ⊆ D := hD₀.trans inter_subset_left
  obtain ⟨A₀, hA₀o, hA₀W, hA₀⟩ := hφ.exists_open_image_eq_inter hD₀o hD₀D
  have haA₀ : φ a ∈ A₀ := by
    have h : φ a ∈ φ '' D₀ := mem_image_of_mem φ haD₀
    rw [hA₀] at h
    exact h.1
  obtain ⟨B, hB, hψB⟩ := hψ.contDiffOn le_rfl (by norm_num)
  have hψD : ψ ⁻¹' D ∈ 𝓝 (φ a) := hψ.continuousAt
    (by simpa only [hψa] using hφ.isOpen_source.mem_nhds ha)
  obtain ⟨C, hC, hCo, haC⟩ := _root_.mem_nhds_iff.mp
    (inter_mem hB hψD)
  refine ⟨A₀ ∩ U ∩ C, ψ, (hA₀o.inter hU).inter hCo,
    ⟨⟨haA₀, haU⟩, haC⟩, ?_, hψB.mono ?_, ?_, ?_⟩
  · intro y hy
    exact ⟨hA₀W hy.1.1, hy.1.2⟩
  · intro y hy
    exact (hC hy.2).1
  · intro y hy
    exact (hC hy.2).2
  · intro u hu huA
    have huM : φ u ∈ M := by
      have h : φ u ∈ φ '' D := mem_image_of_mem φ hu
      rw [hφ.image_eq] at h
      exact h.2
    obtain ⟨v, hv, heq⟩ : φ u ∈ φ '' D₀ := by
      rw [hA₀]
      exact ⟨huA.1.1, huM⟩
    have hvu : v = u := hφ.injOn (hD₀D hv) hu heq
    simpa only [mem_ofPred_eq, hvu] using (hD₀ hv).2

/-- On a neighborhood of each chart point in `U`, every scalar `C¹`
coordinate test is realized by a genuine ambient compactly supported
field with coordinate values `(η / Jφ) • Dφ(v)`. -/
theorem exists_supported_tangent_coordinate_tests
    {M W U : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ)
    (hU : IsOpen U) {a : Euclidean n} (ha : a ∈ D) (haU : φ a ∈ U) :
    ∃ B : Set (Euclidean n), IsOpen B ∧ a ∈ B ∧ B ⊆ D ∩ φ ⁻¹' U ∧
      ∀ (η : Euclidean n → ℝ), ContDiff ℝ 1 η → HasCompactSupport η →
        tsupport η ⊆ B → ∀ v : Euclidean n,
        ∃ X : Varifold.TestVectorField (N := N) U, tsupport X ⊆ W ∧
          ∀ u ∈ D, X (φ u) =
            (η u / Chapter02.areaJacobianAt φ u) • fderiv ℝ φ u v := by
  obtain ⟨A, ψ, hAo, haA, hAWU, hψ, hψD, hleft⟩ :=
    exists_chart_coordinate_inverse_on_neighborhood hφ hU ha haU
  obtain ⟨r, hr, hrA⟩ := nhds_basis_closedBall.mem_iff.mp (hAo.mem_nhds haA)
  let γ : ContDiffBump (φ a) :=
    { rIn := r / 2
      rOut := r
      rIn_pos := half_pos hr
      rIn_lt_rOut := half_lt_self hr }
  let B : Set (Euclidean n) := D ∩ φ ⁻¹' ball (φ a) (r / 2)
  have hBo : IsOpen B := by
    apply isOpen_iff_mem_nhds.mpr
    intro u hu
    exact inter_mem (hφ.isOpen_source.mem_nhds hu.1)
      (((hφ.contDiffOn u hu.1).contDiffAt
        (hφ.isOpen_source.mem_nhds hu.1)).continuousAt
        (isOpen_ball.mem_nhds hu.2))
  have hBA : ∀ u ∈ B, φ u ∈ A := by
    intro u hu
    apply hrA
    exact closedBall_subset_closedBall (by linarith : r / 2 ≤ r)
      (ball_subset_closedBall hu.2)
  have hγA : tsupport γ ⊆ A := by rw [γ.tsupport_eq]; exact hrA
  refine ⟨B, hBo, ⟨ha, mem_ball_self (half_pos hr)⟩,
    fun u hu ↦ ⟨hu.1, (hAWU (hBA u hu)).2⟩, ?_⟩
  intro η hη _ hηB v
  let F : Euclidean N → Euclidean N := fun y ↦
    (η (ψ y) / Chapter02.areaJacobianAt φ (ψ y)) • fderiv ℝ φ (ψ y) v
  have hF : ContDiffOn ℝ 1 F A := by
    have hψ₁ : ContDiffOn ℝ 1 ψ A := hψ.of_le (by norm_num)
    have hJ := (contDiffOn_areaJacobianAt_simonChart hφ).comp hψ₁ hψD
    have hAder := (hφ.contDiffOn.fderiv_of_isOpen hφ.isOpen_source
      (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).comp hψ₁ hψD
    exact ((hη.comp_contDiffOn hψ₁).div hJ
      (fun y hy ↦ (areaJacobianAt_pos_simonChart hφ (hψD hy)).ne')).smul
      (hAder.clm_apply contDiffOn_const)
  let X : Varifold.TestVectorField (N := N) U :=
    { toFun y := γ y • F y
      contDiff := contDiff_cutoff_smul_of_contDiffOn hAo hF γ.contDiff hγA
      compactSupport := γ.hasCompactSupport.smul_right
      support_subset := (tsupport_smul_subset_left γ F).trans
        (hγA.trans (hAWU.trans inter_subset_right)) }
  refine ⟨X, (tsupport_smul_subset_left γ F).trans
    (hγA.trans (hAWU.trans inter_subset_left)), ?_⟩
  intro u hu
  change γ (φ u) • F (φ u) = _
  by_cases huA : φ u ∈ A
  · have he : ψ (φ u) = u := hleft u hu huA
    dsimp only [F]
    rw [he]
    by_cases hηu : η u = 0
    · simp only [hηu, zero_div, zero_smul, smul_zero]
    · have huB := hηB (subset_tsupport η hηu)
      have hγone : γ (φ u) = 1 := γ.one_of_mem_closedBall (ball_subset_closedBall huB.2)
      rw [hγone, one_smul]
  · have hγzero : γ (φ u) = 0 := image_eq_zero_of_notMem_tsupport
      (fun ht ↦ huA (hγA ht))
    have hηzero : η u = 0 := by
      by_contra hh
      exact huA (hBA u (hηB (subset_tsupport η hh)))
    simp only [hγzero, hηzero, zero_div, zero_smul]

end
end Poincare.SimonGMT.Chapter08
