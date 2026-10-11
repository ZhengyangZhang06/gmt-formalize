module

public import Poincare.SimonGMT.Chapter02.CoareaProjection

@[expose] public section

/-!
# The actual orthogonal factorization and Jacobian for linear coarea

A surjective linear map is factored through orthogonal projection onto the
orthogonal complement of its kernel, followed by a linear isomorphism.
The Jacobian of this isomorphism is proved to be `sqrt(det(L L*))`.
-/

open Function Module Set
open scoped ENNReal InnerProductSpace

namespace Poincare.SimonGMT.Chapter02
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Simon's linear coarea Jacobian, expressed as the area Jacobian of the adjoint. -/
def coareaLinearJacobian (L : E →ₗ[ℝ] F) : ℝ := L.adjoint.normDet

theorem coareaLinearJacobian_nonneg (L : E →ₗ[ℝ] F) :
    0 ≤ coareaLinearJacobian L := L.adjoint.normDet_nonneg

/-- The coarea Jacobian vanishes exactly at deficient target rank. -/
theorem coareaLinearJacobian_eq_zero_iff (L : E →ₗ[ℝ] F) :
    coareaLinearJacobian L = 0 ↔ ¬ Surjective L := by
  rw [coareaLinearJacobian, LinearMap.normDet_eq_zero_iff_ker_ne_bot,
    ← L.orthogonal_range, ne_eq, Submodule.orthogonal_eq_bot_iff,
    LinearMap.range_eq_top]

/-- The literal determinant appearing in (6.2). -/
theorem coareaLinearJacobian_eq_sqrt_det (L : E →ₗ[ℝ] F) :
    coareaLinearJacobian L = Real.sqrt (L ∘ₗ L.adjoint).det := by
  have hsq : coareaLinearJacobian L ^ 2 = (L ∘ₗ L.adjoint).det := by
    simpa [coareaLinearJacobian] using
      L.adjoint.normDet_sq
  rw [← hsq]
  exact (Real.sqrt_sq (coareaLinearJacobian_nonneg L)).symm

/-- The normal and kernel coordinates in the order used for projection coarea. -/
def coareaCoordinates (L : E →ₗ[ℝ] F) : E ≃ₗᵢ[ℝ] WithLp 2 (L.kerᗮ × L.ker) :=
  L.ker.orthogonalDecomposition.trans (LinearIsometryEquiv.withLpProdComm 2 ℝ _ _)

theorem coareaCoordinates_symm_apply (L : E →ₗ[ℝ] F)
    (p : WithLp 2 (L.kerᗮ × L.ker)) :
    (coareaCoordinates L).symm p = (p.fst : E) + (p.snd : E) := by
  change (p.snd : E) + (p.fst : E) = _
  exact add_comm _ _

/-- The restriction to the normal complement, which has no kernel. -/
def coareaHorizontalLinear (L : E →ₗ[ℝ] F) : L.kerᗮ →ₗ[ℝ] F :=
  L.domRestrict L.kerᗮ

theorem coareaHorizontalLinear_injective (L : E →ₗ[ℝ] F) :
    Injective (coareaHorizontalLinear L) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  have hz : (x : E) ∈ L.ker ⊓ L.kerᗮ := ⟨hx, x.property⟩
  rw [L.ker.inf_orthogonal_eq_bot] at hz
  apply Subtype.ext
  simpa using hz

/-- The exact factorization `L = σ ∘ p ∘ q`. -/
theorem coareaHorizontalLinear_coordinates (L : E →ₗ[ℝ] F) (x : E) :
    coareaHorizontalLinear L (coareaCoordinates L x).fst = L x := by
  have h := congrArg L ((coareaCoordinates L).symm_apply_apply x)
  rw [coareaCoordinates_symm_apply, map_add,
    show L (((coareaCoordinates L) x).snd : E) = 0 from
      ((coareaCoordinates L) x).snd.property, add_zero] at h
  exact h

theorem coareaHorizontalLinear_bijective {L : E →ₗ[ℝ] F} (hL : Surjective L) :
    Bijective (coareaHorizontalLinear L) := by
  refine ⟨coareaHorizontalLinear_injective L, ?_⟩
  intro y
  obtain ⟨x, rfl⟩ := hL y
  exact ⟨(coareaCoordinates L x).fst, coareaHorizontalLinear_coordinates L x⟩

/-- The nonsingular factor is constructed from the actual map. -/
def coareaHorizontalEquiv (L : E →ₗ[ℝ] F) (hL : Surjective L) : L.kerᗮ ≃ₗ[ℝ] F :=
  LinearEquiv.ofBijective (coareaHorizontalLinear L) (coareaHorizontalLinear_bijective hL)

/-- Equal-dimensional maps and their adjoints have the same metric determinant. -/
theorem normDet_adjoint_of_finrank_eq (L : E →ₗ[ℝ] F)
    (hd : finrank ℝ E = finrank ℝ F) : L.adjoint.normDet = L.normDet := by
  classical
  let bE := stdOrthonormalBasis ℝ E
  let bF := (stdOrthonormalBasis ℝ F).reindex (finCongr hd.symm)
  rw [L.adjoint.normDet_eq_norm_det_toMatrix bF bE,
    L.normDet_eq_norm_det_toMatrix bE bF, LinearMap.toMatrix_adjoint,
    Matrix.det_conjTranspose]
  simp

/-- The Jacobian of the constructed nonsingular factor is the coarea
Jacobian, including the exact square-root determinant normalization. -/
theorem coareaHorizontalLinear_normDet {L : E →ₗ[ℝ] F} (hL : Surjective L) :
    (coareaHorizontalLinear L).normDet = coareaLinearJacobian L := by
  have hm (y : F) : L.adjoint y ∈ L.kerᗮ := by
    rw [LinearMap.orthogonal_ker]
    exact ⟨y, rfl⟩
  have ha : L.adjoint.codRestrict L.kerᗮ hm = (coareaHorizontalLinear L).adjoint := by
    apply (LinearMap.eq_adjoint_iff _ _).mpr
    intro y x
    exact L.adjoint_inner_left x y
  rw [← normDet_adjoint_of_finrank_eq (coareaHorizontalLinear L)
    (coareaHorizontalEquiv L hL).finrank_eq, ← ha, LinearMap.normDet_codRestrict]
  rfl

/-- The kernel has the expected fiber dimension. -/
theorem coarea_kernel_finrank {L : E →ₗ[ℝ] F} (hL : Surjective L) :
    finrank ℝ L.ker = finrank ℝ E - finrank ℝ F := by
  have h := L.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hL, finrank_top] at h
  omega

end
end Poincare.SimonGMT.Chapter02
