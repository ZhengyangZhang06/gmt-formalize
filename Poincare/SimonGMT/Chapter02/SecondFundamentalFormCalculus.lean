module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Poincare.SimonGMT.Chapter02.SecondFundamentalForm

@[expose] public section

/-!
# Simon GMT, Chapter 2, §4: curvature identities from moving normal frames

This module proves the differential identities in Simon (4.25), (4.26), and
(4.29).  The moving-frame hypotheses are stated at the exact first-order
level used in the source argument: normal fields are orthogonal to the
relevant tangent velocity near the base point, and their derivatives are the
directional derivatives entering the second fundamental form.
-/

open Filter InnerProductSpace Module
open scoped Topology

namespace Poincare.SimonGMT.Chapter02

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Differentiating the identity `ν(t) · v(t) = 0` gives the coefficient
identity used in Simon's proofs of (4.25) and (4.26). -/
theorem normal_derivative_inner_eq_neg_acceleration_inner
    {ν v : ℝ → E} {ν' a : E}
    (hν : HasDerivAt ν ν' 0) (hv : HasDerivAt v a 0)
    (horth : (fun t ↦ inner ℝ (ν t) (v t)) =ᶠ[𝓝 0] (fun _ ↦ 0)) :
    inner ℝ (ν 0) a = -inner ℝ (v 0) ν' := by
  have hproduct := hν.inner ℝ hv
  have hzero : HasDerivAt (fun t ↦ inner ℝ (ν t) (v t)) 0 0 :=
    (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ))).congr_of_eventuallyEq horth
  have h := hproduct.unique hzero
  have hs : inner ℝ ν' (v 0) = inner ℝ (v 0) ν' := real_inner_comm _ _
  linarith [h, hs]

/-- Orthogonal projection onto a normal space, expanded in any orthonormal
normal basis. -/
theorem orthogonalProjectionOnto_orthogonal_eq_sum
    {ι : Type*} [Fintype ι] (T : Submodule ℝ E)
    (b : OrthonormalBasis ι ℝ Tᗮ) (a : E) :
    Tᗮ.orthogonalProjectionOnto a =
      ∑ α, inner ℝ (b α : E) a • b α := by
  calc
    Tᗮ.orthogonalProjectionOnto a =
        ∑ α, inner ℝ (b α) (Tᗮ.orthogonalProjectionOnto a) • b α :=
      (b.sum_repr' (Tᗮ.orthogonalProjectionOnto a)).symm
    _ = ∑ α, inner ℝ (b α : E) a • b α := by
      apply Finset.sum_congr rfl
      intro α _
      rw [Tᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left]

/-- Simon (4.26): the second fundamental form is the normal projection of
the mixed derivative.  A two-parameter surface supplies `v` as its second
coordinate velocity along the first coordinate axis. -/
theorem secondFundamentalForm_eq_normalProjection_mixed
    {ι : Type*} [Fintype ι] {T : Submodule ℝ E}
    (b : OrthonormalBasis ι ℝ Tᗮ) (Dν : ι → T →ₗ[ℝ] E)
    (τ η : T) (a : E) (ν : ι → ℝ → E) (v : ℝ → E)
    (hν0 : ∀ α, ν α 0 = (b α : E)) (hv0 : v 0 = (η : E))
    (hν : ∀ α, HasDerivAt (ν α) (Dν α τ) 0)
    (hv : HasDerivAt v a 0)
    (horth : ∀ α,
      (fun t ↦ inner ℝ (ν α t) (v t)) =ᶠ[𝓝 0] (fun _ ↦ 0)) :
    secondFundamentalFormFromNormalFrame T b Dν τ η =
      Tᗮ.orthogonalProjectionOnto a := by
  rw [secondFundamentalFormFromNormalFrame_apply,
    orthogonalProjectionOnto_orthogonal_eq_sum T b]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro α _
  have h := normal_derivative_inner_eq_neg_acceleration_inner
    (hν α) hv (horth α)
  rw [hν0 α, hv0] at h
  calc
    -(inner ℝ (η : E) (Dν α τ) • b α) =
        (-inner ℝ (η : E) (Dν α τ)) • b α := by rw [neg_smul]
    _ = inner ℝ (b α : E) a • b α := by rw [h]

/-- The symmetry consequence in Simon (4.26): if the two orders of
differentiation are represented by the same mixed derivative, then the two
orders of the second fundamental form agree. -/
theorem secondFundamentalForm_swap_eq_of_common_mixed_derivative
    {ι : Type*} [Fintype ι] {T : Submodule ℝ E}
    (b : OrthonormalBasis ι ℝ Tᗮ) (Dν : ι → T →ₗ[ℝ] E)
    (τ η : T) (a : E)
    (ν₁ ν₂ : ι → ℝ → E) (v₁ v₂ : ℝ → E)
    (hν₁₀ : ∀ α, ν₁ α 0 = (b α : E)) (hv₁₀ : v₁ 0 = (η : E))
    (hν₁ : ∀ α, HasDerivAt (ν₁ α) (Dν α τ) 0)
    (hv₁ : HasDerivAt v₁ a 0)
    (horth₁ : ∀ α,
      (fun t ↦ inner ℝ (ν₁ α t) (v₁ t)) =ᶠ[𝓝 0] (fun _ ↦ 0))
    (hν₂₀ : ∀ α, ν₂ α 0 = (b α : E)) (hv₂₀ : v₂ 0 = (τ : E))
    (hν₂ : ∀ α, HasDerivAt (ν₂ α) (Dν α η) 0)
    (hv₂ : HasDerivAt v₂ a 0)
    (horth₂ : ∀ α,
      (fun t ↦ inner ℝ (ν₂ α t) (v₂ t)) =ᶠ[𝓝 0] (fun _ ↦ 0)) :
    secondFundamentalFormFromNormalFrame T b Dν τ η =
      secondFundamentalFormFromNormalFrame T b Dν η τ := by
  calc
    secondFundamentalFormFromNormalFrame T b Dν τ η =
        Tᗮ.orthogonalProjectionOnto a :=
      secondFundamentalForm_eq_normalProjection_mixed b Dν τ η a ν₁ v₁
        hν₁₀ hv₁₀ hν₁ hv₁ horth₁
    _ = secondFundamentalFormFromNormalFrame T b Dν η τ :=
      (secondFundamentalForm_eq_normalProjection_mixed b Dν η τ a ν₂ v₂
        hν₂₀ hv₂₀ hν₂ hv₂ horth₂).symm

/-- Simon (4.25): along a curve, the diagonal value of the second
fundamental form is the normal component of its acceleration. -/
theorem secondFundamentalForm_eq_normalProjection_curve
    {ι : Type*} [Fintype ι] {T : Submodule ℝ E}
    (b : OrthonormalBasis ι ℝ Tᗮ) (Dν : ι → T →ₗ[ℝ] E)
    (τ : T) (a : E) (ν : ι → ℝ → E) (velocity : ℝ → E)
    (hν0 : ∀ α, ν α 0 = (b α : E))
    (hvelocity0 : velocity 0 = (τ : E))
    (hν : ∀ α, HasDerivAt (ν α) (Dν α τ) 0)
    (hacceleration : HasDerivAt velocity a 0)
    (horth : ∀ α,
      (fun t ↦ inner ℝ (ν α t) (velocity t)) =ᶠ[𝓝 0] (fun _ ↦ 0)) :
    secondFundamentalFormFromNormalFrame T b Dν τ τ =
      Tᗮ.orthogonalProjectionOnto a :=
  secondFundamentalForm_eq_normalProjection_mixed b Dν τ τ a ν velocity
    hν0 hvelocity0 hν hacceleration horth

/-- The component of a vector field in a moving finite normal frame.  For
an orthonormal basis of the normal space this is exactly `X⊥`. -/
def normalFrameComponent {ι : Type*} [Fintype ι]
    (ν : ι → E → E) (X : E → E) : E → E :=
  fun y ↦ ∑ α, inner ℝ (ν α y) (X y) • ν α y

/-- At a point where the frame is an orthonormal basis of `T⊥`, the moving
frame component is the orthogonal projection onto `T⊥`. -/
theorem normalFrameComponent_eq_orthogonalProjectionOnto
    {ι : Type*} [Fintype ι] (T : Submodule ℝ E)
    (b : OrthonormalBasis ι ℝ Tᗮ) (ν : ι → E → E)
    (X : E → E) (x : E) (hνx : ∀ α, ν α x = (b α : E)) :
    normalFrameComponent ν X x =
      (Tᗮ.orthogonalProjectionOnto (X x) : E) := by
  rw [normalFrameComponent,
    orthogonalProjectionOnto_orthogonal_eq_sum T b]
  simp_rw [hνx]
  simp

/-- The product-rule calculation preceding Simon (4.29): derivatives of
the scalar coefficients make no contribution to tangential divergence
because every frame vector is normal at the base point. -/
theorem submanifoldDivergenceAt_normalFrameComponent
    {ι κ : Type*} [Fintype ι] [Fintype κ] {T : Submodule ℝ E}
    (b : OrthonormalBasis κ ℝ T) (ν : ι → E → E) (X : E → E) (x : E)
    (hν : ∀ α, DifferentiableAt ℝ (ν α) x)
    (hX : DifferentiableAt ℝ X x)
    (hnormal : ∀ α, ν α x ∈ Tᗮ) :
    submanifoldDivergenceAt T (normalFrameComponent ν X) x =
      ∑ α, inner ℝ (ν α x) (X x) *
        submanifoldDivergenceAt T (ν α) x := by
  let c : ι → E → ℝ := fun α y ↦ inner ℝ (ν α y) (X y)
  have hc (α : ι) : DifferentiableAt ℝ (c α) x :=
    (hν α).inner ℝ hX
  have hterm (α : ι) :
      DifferentiableAt ℝ (fun y ↦ c α y • ν α y) x :=
    (hc α).smul (hν α)
  have hsum :
      fderiv ℝ (normalFrameComponent ν X) x =
        ∑ α, fderiv ℝ (fun y ↦ c α y • ν α y) x := by
    change fderiv ℝ (fun y ↦ ∑ α, c α y • ν α y) x = _
    exact fderiv_fun_sum (u := Finset.univ) (fun α _ ↦ hterm α)
  rw [submanifoldDivergenceAt_eq_sum_inner b, hsum]
  simp_rw [submanifoldDivergenceAt_eq_sum_inner b]
  calc
    ∑ i, inner ℝ (b i : E)
        ((∑ α, fderiv ℝ (fun y ↦ c α y • ν α y) x) (b i : E)) =
        ∑ i, ∑ α, inner ℝ (b i : E)
          ((fderiv ℝ (fun y ↦ c α y • ν α y) x) (b i : E)) := by
      apply Finset.sum_congr rfl
      intro i _
      have happ :
          ((∑ α, fderiv ℝ (fun y ↦ c α y • ν α y) x) (b i : E)) =
            ∑ α, (fderiv ℝ (fun y ↦ c α y • ν α y) x) (b i : E) := by
        simp
      calc
        inner ℝ (b i : E)
            ((∑ α, fderiv ℝ (fun y ↦ c α y • ν α y) x) (b i : E)) =
            inner ℝ (b i : E)
              (∑ α, (fderiv ℝ (fun y ↦ c α y • ν α y) x) (b i : E)) :=
          congrArg (inner ℝ (b i : E)) happ
        _ = ∑ α, inner ℝ (b i : E)
            ((fderiv ℝ (fun y ↦ c α y • ν α y) x) (b i : E)) := by
          simpa using
            (inner_sum Finset.univ
              (fun α ↦ (fderiv ℝ (fun y ↦ c α y • ν α y) x) (b i : E))
              (b i : E))
    _ = ∑ α, ∑ i, inner ℝ (b i : E)
          ((fderiv ℝ (fun y ↦ c α y • ν α y) x) (b i : E)) := by
      rw [Finset.sum_comm]
    _ = ∑ α, c α x *
          ∑ i, inner ℝ (b i : E) ((fderiv ℝ (ν α) x) (b i : E)) := by
      apply Finset.sum_congr rfl
      intro α _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [fderiv_fun_smul (hc α) (hν α)]
      change inner ℝ (b i : E)
          (c α x • (fderiv ℝ (ν α) x) (b i : E) +
            (fderiv ℝ (c α) x) (b i : E) • ν α x) = _
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
        T.inner_right_of_mem_orthogonal (b i).property (hnormal α)]
      ring
    _ = ∑ α, inner ℝ (ν α x) (X x) *
          ∑ i, inner ℝ (b i : E) ((fderiv ℝ (ν α) x) (b i : E)) := rfl

/-- Simon (4.29): the tangential divergence of the normal component is
`-X·H`, proved from the actual moving-frame derivative and the traced second
fundamental form. -/
theorem submanifoldDivergenceAt_normalFrameComponent_eq_neg_inner_meanCurvature
    {ι κ : Type*} [Fintype ι] [Fintype κ] {T : Submodule ℝ E}
    (b : OrthonormalBasis κ ℝ T) (ν : ι → E → E) (X : E → E) (x : E)
    (hν : ∀ α, DifferentiableAt ℝ (ν α) x)
    (hX : DifferentiableAt ℝ X x)
    (hnormal : ∀ α, ν α x ∈ Tᗮ) :
    submanifoldDivergenceAt T (normalFrameComponent ν X) x =
      -inner ℝ (X x)
        (meanCurvatureVector T
          (secondFundamentalFormFromNormalFrame T
            (fun α ↦ ⟨ν α x, hnormal α⟩)
            (fun α ↦ (fderiv ℝ (ν α) x).toLinearMap.domRestrict T)) : E) := by
  have htrace (α : ι) :
      tangentialDivergenceLinear T
          ((fderiv ℝ (ν α) x).toLinearMap.domRestrict T) =
        submanifoldDivergenceAt T (ν α) x := by
    calc
      tangentialDivergenceLinear T
          ((fderiv ℝ (ν α) x).toLinearMap.domRestrict T) =
          ∑ i, inner ℝ (b i : E) ((fderiv ℝ (ν α) x) (b i : E)) :=
        tangentialDivergenceLinear_eq_sum_inner b _
      _ = submanifoldDivergenceAt T (ν α) x :=
        (submanifoldDivergenceAt_eq_sum_inner b (ν α) x).symm
  rw [submanifoldDivergenceAt_normalFrameComponent b ν X x hν hX hnormal,
    meanCurvatureVector_fromNormalFrame b]
  simp_rw [htrace]
  have hcoe :
      (((-∑ α, submanifoldDivergenceAt T (ν α) x •
          ⟨ν α x, hnormal α⟩) : Tᗮ) : E) =
        -∑ α, submanifoldDivergenceAt T (ν α) x • ν α x := by
    simp
  rw [hcoe, inner_neg_right, neg_neg, inner_sum]
  apply Finset.sum_congr rfl
  intro α _
  rw [real_inner_smul_right, real_inner_comm (X x) (ν α x)]
  ring

end Poincare.SimonGMT.Chapter02
