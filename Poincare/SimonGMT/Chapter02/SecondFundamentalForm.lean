module

public import Mathlib.Analysis.InnerProductSpace.CanonicalTensor
public import Poincare.SimonGMT.Chapter02.SubmanifoldCalculus

@[expose] public section

/-!
# Simon GMT, Chapter 2, §4: second fundamental form and mean curvature

This module isolates the finite-dimensional tensor algebra in Simon
(4.23)--(4.28).  The second fundamental form takes two tangent vectors and
has values in the normal space.  Its trace is defined without choosing a
basis, by contraction with the canonical covariant tensor, and is then proved
to equal Simon's sum in every orthonormal tangent basis.
-/

open InnerProductSpace Module TensorProduct

namespace Poincare.SimonGMT.Chapter02

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Simon (4.23): an ambient-vector-valued bilinear form on a tangent plane,
whose values lie in the normal space. -/
abbrev SecondFundamentalForm (T : Submodule ℝ E) :=
  T →ₗ[ℝ] T →ₗ[ℝ] Tᗮ

/-- Symmetry of the second fundamental form, obtained geometrically in Simon
from the mixed-derivative formula (4.26). -/
def IsSymmetricSecondFundamentalForm {T : Submodule ℝ E}
    (B : SecondFundamentalForm T) : Prop :=
  ∀ τ η, B τ η = B η τ

/-- Simon (4.27): mean curvature is the basis-free trace of the second
fundamental form.  The canonical tensor performs the contraction in the two
tangent variables. -/
noncomputable def meanCurvatureVector (T : Submodule ℝ E)
    (B : SecondFundamentalForm T) : Tᗮ :=
  TensorProduct.lift B (canonicalCovariantTensor T)

/-- The orthonormal-basis formula printed in Simon (4.27). -/
theorem meanCurvatureVector_eq_sum
    {ι : Type*} [Fintype ι] {T : Submodule ℝ E}
    (b : OrthonormalBasis ι ℝ T) (B : SecondFundamentalForm T) :
    meanCurvatureVector T B = ∑ i, B (b i) (b i) := by
  rw [meanCurvatureVector, canonicalCovariantTensor_eq_sum T b]
  simp

/-- Simon (4.24), as a bilinear map: a local orthonormal normal frame and
its directional derivatives determine the second fundamental form by
`B(τ,η) = -∑α ⟪η, Dτ να⟫ να`. -/
noncomputable def secondFundamentalFormFromNormalFrame
    {ι : Type*} [Fintype ι] (T : Submodule ℝ E)
    (ν : ι → Tᗮ) (Dν : ι → T →ₗ[ℝ] E) : SecondFundamentalForm T :=
  LinearMap.mk₂ ℝ
    (fun τ η ↦ -∑ α, inner ℝ (η : E) (Dν α τ) • ν α)
    (by
      intro τ₁ τ₂ η
      simp [map_add, inner_add_right, add_smul, Finset.sum_add_distrib]
      ac_rfl)
    (by
      intro c τ η
      simp [map_smul, inner_smul_right, Finset.smul_sum, smul_smul])
    (by
      intro τ η₁ η₂
      simp [inner_add_left, add_smul, Finset.sum_add_distrib]
      ac_rfl)
    (by
      intro c τ η
      simp [real_inner_smul_left, Finset.smul_sum, smul_smul])

omit [FiniteDimensional ℝ E] in
@[simp]
theorem secondFundamentalFormFromNormalFrame_apply
    {ι : Type*} [Fintype ι] (T : Submodule ℝ E)
    (ν : ι → Tᗮ) (Dν : ι → T →ₗ[ℝ] E) (τ η : T) :
    secondFundamentalFormFromNormalFrame T ν Dν τ η =
      -∑ α, inner ℝ (η : E) (Dν α τ) • ν α :=
  rfl

/-- Tangential divergence of a linear differential, in the same trace form
as (4.18), but accepting an algebraic linear map for use with (4.24). -/
noncomputable def tangentialDivergenceLinear (T : Submodule ℝ E)
    (D : T →ₗ[ℝ] E) : ℝ :=
  LinearMap.trace ℝ T (T.orthogonalProjectionOnto.toLinearMap.comp D)

/-- Orthonormal tangent-basis expression for linear tangential divergence. -/
theorem tangentialDivergenceLinear_eq_sum_inner
    {ι : Type*} [Fintype ι] {T : Submodule ℝ E}
    (b : OrthonormalBasis ι ℝ T) (D : T →ₗ[ℝ] E) :
    tangentialDivergenceLinear T D =
      ∑ i, inner ℝ (b i : E) (D (b i)) := by
  rw [tangentialDivergenceLinear, LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℝ (b i) (T.orthogonalProjectionOnto (D (b i))) = _
  exact T.inner_orthogonalProjectionOnto_eq_of_mem_left (b i) (D (b i))

/-- Simon (4.28): tracing the normal-frame formula (4.24) gives mean
curvature as minus the normal-frame expansion of the tangential divergences. -/
theorem meanCurvatureVector_fromNormalFrame
    {ι κ : Type*} [Fintype ι] [Fintype κ] {T : Submodule ℝ E}
    (b : OrthonormalBasis κ ℝ T) (ν : ι → Tᗮ)
    (Dν : ι → T →ₗ[ℝ] E) :
    meanCurvatureVector T (secondFundamentalFormFromNormalFrame T ν Dν) =
      -∑ α, tangentialDivergenceLinear T (Dν α) • ν α := by
  rw [meanCurvatureVector_eq_sum b]
  simp_rw [secondFundamentalFormFromNormalFrame_apply,
    tangentialDivergenceLinear_eq_sum_inner b]
  calc
    ∑ j, -∑ α, inner ℝ (b j : E) (Dν α (b j)) • ν α =
        -∑ j, ∑ α, inner ℝ (b j : E) (Dν α (b j)) • ν α := by
      simp
    _ = -∑ α, ∑ j, inner ℝ (b j : E) (Dν α (b j)) • ν α := by
      rw [Finset.sum_comm]
    _ = -∑ α, (∑ j, inner ℝ (b j : E) (Dν α (b j))) • ν α := by
      congr 1
      apply Finset.sum_congr rfl
      intro α _
      rw [Finset.sum_smul]

end Poincare.SimonGMT.Chapter02
