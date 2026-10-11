module

public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import Mathlib.Topology.Algebra.Module.Alternating.Topology
public import Poincare.SimonGMT.Chapter06.Currents

@[expose] public section

/-!
# Continuous exterior products of covectors and test forms

This supplies the analytic exterior-product bridge needed in Simon (6.2.17)
and (6.2.18). The product is the usual alternating sum with normalization
`1 / (s! t!)`, constructed as an actual continuous bilinear map. In
particular, exterior products of test forms on separate factors are smooth
and have compact support in the product of the original supports.
-/

open Function Set
open scoped Topology

namespace Poincare.SimonGMT.Chapter06

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]

-- These local aliases keep inference from traversing the two nested
-- operator spaces repeatedly; the structures are the existing operator norms.
local instance nestedMultilinearSeminormed (s t : ℕ) :
    SeminormedAddCommGroup (E [×s]→L[ℝ] (E [×t]→L[ℝ] ℝ)) := inferInstance

local instance nestedMultilinearNormedSpace (s t : ℕ) :
    NormedSpace ℝ (E [×s]→L[ℝ] (E [×t]→L[ℝ] ℝ)) := inferInstance

/-- Reindexing, alternation, and the source normalization of the exterior
product, as one fixed continuous linear operator. -/
def covectorWedgeAlternation (s t : ℕ) :
    (E [×s]→L[ℝ] (E [×t]→L[ℝ] ℝ)) →L[ℝ] Covector E (s + t) :=
  (((s.factorial * t.factorial : ℕ) : ℝ)⁻¹) •
    (ContinuousMultilinearMap.alternatizationL.comp
      ((ContinuousMultilinearMap.domDomCongrL finSumFinEquiv).comp
        (ContinuousMultilinearMap.currySumEquiv ℝ (Fin s) (Fin t) E ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap))

/-- The genuine continuous bilinear exterior product of arbitrary-degree
continuous covectors. -/
def covectorWedgeCLM (s t : ℕ) :
    Covector E s →L[ℝ] Covector E t →L[ℝ] Covector E (s + t) := by
  let A := covectorWedgeAlternation (E := E) s t
  let W (alpha : Covector E s) (beta : Covector E t) : Covector E (s + t) :=
    A (alpha.toContinuousMultilinearMap.smulRight beta.toContinuousMultilinearMap)
  let B : Covector E s →ₗ[ℝ] Covector E t →ₗ[ℝ] Covector E (s + t) :=
    LinearMap.mk₂ ℝ W
      (by
        intro a a' b
        dsimp [W]
        rw [← map_add]
        congr 1
        ext v
        simp [add_smul])
      (by
        intro c a b
        dsimp [W]
        rw [← map_smul]
        congr 1
        ext v
        simp [smul_smul])
      (by
        intro a b b'
        dsimp [W]
        rw [← map_add]
        congr 1
        ext v
        simp [smul_add])
      (by
        intro c a b
        dsimp [W]
        rw [← map_smul]
        congr 1
        ext v
        simp [smul_smul, mul_comm])
  exact B.mkContinuous₂ ‖A‖ (fun a b => by
    simpa only [B, LinearMap.mk₂_apply, W, ContinuousMultilinearMap.norm_smulRight,
      ContinuousAlternatingMap.norm_toContinuousMultilinearMap, mul_assoc] using
      A.le_opNorm (a.toContinuousMultilinearMap.smulRight b.toContinuousMultilinearMap))

/-- Exterior product of covectors, with the unnormalized alternating sum
divided by the factorials of the two degrees. -/
def covectorWedge {s t : ℕ} (alpha : Covector E s) (beta : Covector E t) :
    Covector E (s + t) := covectorWedgeCLM s t alpha beta

/-- The explicit permutation formula fixes the normalization and order of
the two factors. -/
theorem covectorWedge_apply {s t : ℕ} (alpha : Covector E s) (beta : Covector E t)
    (v : Fin (s + t) → E) :
    covectorWedge alpha beta v =
      (((s.factorial * t.factorial : ℕ) : ℝ)⁻¹) *
        ∑ σ : Equiv.Perm (Fin (s + t)), Equiv.Perm.sign σ •
          (alpha (fun i => v (σ (finSumFinEquiv (Sum.inl i)))) *
            beta (fun i => v (σ (finSumFinEquiv (Sum.inr i))))) := by
  change ((((s.factorial * t.factorial : ℕ) : ℝ)⁻¹) •
    (((alpha.toContinuousMultilinearMap.smulRight beta.toContinuousMultilinearMap).uncurrySum).domDomCongr
      finSumFinEquiv).alternatization) v = _
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    ContinuousMultilinearMap.alternatization_apply_apply,
    ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.uncurrySum_apply,
    ContinuousMultilinearMap.smulRight_apply, smul_apply, Function.comp_def]
  rfl

@[simp] theorem covectorWedge_zero_left {s t : ℕ} (beta : Covector E t) :
    covectorWedge (0 : Covector E s) beta = 0 := by
  simp [covectorWedge]

@[simp] theorem covectorWedge_zero_right {s t : ℕ} (alpha : Covector E s) :
    covectorWedge alpha (0 : Covector E t) = 0 := by
  simp [covectorWedge]

theorem covectorWedge_add_left {s t : ℕ}
    (alpha alpha' : Covector E s) (beta : Covector E t) :
    covectorWedge (alpha + alpha') beta =
      covectorWedge alpha beta + covectorWedge alpha' beta := by
  simp [covectorWedge]

theorem covectorWedge_add_right {s t : ℕ}
    (alpha : Covector E s) (beta beta' : Covector E t) :
    covectorWedge alpha (beta + beta') =
      covectorWedge alpha beta + covectorWedge alpha beta' := by
  simp [covectorWedge]

theorem covectorWedge_smul_left {s t : ℕ} (c : ℝ)
    (alpha : Covector E s) (beta : Covector E t) :
    covectorWedge (c • alpha) beta = c • covectorWedge alpha beta := by
  simp [covectorWedge]

theorem covectorWedge_smul_right {s t : ℕ} (c : ℝ)
    (alpha : Covector E s) (beta : Covector E t) :
    covectorWedge alpha (c • beta) = c • covectorWedge alpha beta := by
  simp [covectorWedge]

/-- A uniform bilinear norm estimate, with a constant depending only on
the two degrees and the fixed exterior-product operator. -/
theorem norm_covectorWedge_le {s t : ℕ}
    (alpha : Covector E s) (beta : Covector E t) :
    ‖covectorWedge alpha beta‖ ≤ ‖covectorWedgeAlternation (E := E) s t‖ * ‖alpha‖ * ‖beta‖ := by
  change ‖covectorWedgeAlternation (E := E) s t
    (alpha.toContinuousMultilinearMap.smulRight beta.toContinuousMultilinearMap)‖ ≤ _
  simpa only [ContinuousMultilinearMap.norm_smulRight,
    ContinuousAlternatingMap.norm_toContinuousMultilinearMap, mul_assoc] using
    (covectorWedgeAlternation (E := E) s t).le_opNorm
      (alpha.toContinuousMultilinearMap.smulRight beta.toContinuousMultilinearMap)

/-- Pullback by a continuous linear map commutes with the binary exterior
product in arbitrary degrees. -/
theorem covectorWedge_compContinuousLinearMap {s t : ℕ}
    (L : E →L[ℝ] F) (alpha : Covector F s) (beta : Covector F t) :
    (covectorWedge alpha beta).compContinuousLinearMap L =
      covectorWedge (alpha.compContinuousLinearMap L) (beta.compContinuousLinearMap L) := by
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, covectorWedge_apply]
  rfl

/-- Pointwise exterior product of differential forms on a common ambient
space. -/
def wedgeForm {s t : ℕ} (omega : DifferentialForm E s) (eta : DifferentialForm E t) :
    DifferentialForm E (s + t) := fun x => covectorWedge (omega x) (eta x)

/-- Smoothness follows from the actual continuous bilinear operator. -/
theorem wedgeForm_isSmoothForm {s t : ℕ}
    {omega : DifferentialForm E s} {eta : DifferentialForm E t}
    (homega : IsSmoothForm omega) (heta : IsSmoothForm eta) :
    IsSmoothForm (wedgeForm omega eta) := by
  exact ((covectorWedgeCLM (E := E) s t).contDiff.comp homega).clm_apply heta

/-- Wedge support is contained in the intersection, not merely the union,
of the factor supports. -/
theorem tsupport_wedgeForm_subset {s t : ℕ}
    (omega : DifferentialForm E s) (eta : DifferentialForm E t) :
    tsupport (wedgeForm omega eta) ⊆ tsupport omega ∩ tsupport eta := by
  apply closure_minimal _ ((isClosed_tsupport omega).inter (isClosed_tsupport eta))
  intro x hx
  constructor
  · apply subset_closure
    intro hzero
    exact hx (by simp [wedgeForm, hzero])
  · apply subset_closure
    intro hzero
    exact hx (by simp [wedgeForm, hzero])

/-- The wedge of two test forms is again a test form. -/
theorem wedgeForm_isTestForm {s t : ℕ}
    {omega : DifferentialForm E s} {eta : DifferentialForm E t}
    (homega : IsTestForm omega) (heta : IsTestForm eta) :
    IsTestForm (wedgeForm omega eta) :=
  ⟨wedgeForm_isSmoothForm homega.1 heta.1,
    homega.2.of_isClosed_subset (isClosed_tsupport _)
      ((tsupport_wedgeForm_subset omega eta).trans inter_subset_left)⟩

/-- The exterior product `P* omega ∧ Q* eta` on a Cartesian product. -/
def cartesianWedgeForm {s t : ℕ}
    (omega : DifferentialForm E s) (eta : DifferentialForm F t) :
    DifferentialForm (E × F) (s + t) := fun z =>
  covectorWedge
    ((omega z.1).compContinuousLinearMap (ContinuousLinearMap.fst ℝ E F))
    ((eta z.2).compContinuousLinearMap (ContinuousLinearMap.snd ℝ E F))

/-- Cartesian exterior products of smooth forms are smooth. -/
theorem cartesianWedgeForm_isSmoothForm {s t : ℕ}
    {omega : DifferentialForm E s} {eta : DifferentialForm F t}
    (homega : IsSmoothForm omega) (heta : IsSmoothForm eta) :
    IsSmoothForm (cartesianWedgeForm omega eta) := by
  change IsSmoothForm (wedgeForm
    (fun z : E × F => (omega z.1).compContinuousLinearMap (ContinuousLinearMap.fst ℝ E F))
    (fun z : E × F => (eta z.2).compContinuousLinearMap (ContinuousLinearMap.snd ℝ E F)))
  apply wedgeForm_isSmoothForm
  · exact (ContinuousAlternatingMap.compContinuousLinearMapCLM (ι := Fin s) (F := ℝ)
      (ContinuousLinearMap.fst ℝ E F)).contDiff.comp (homega.comp contDiff_fst)
  · exact (ContinuousAlternatingMap.compContinuousLinearMapCLM (ι := Fin t) (F := ℝ)
      (ContinuousLinearMap.snd ℝ E F)).contDiff.comp (heta.comp contDiff_snd)

/-- The support required for the pure test forms in Simon (6.2.18). -/
theorem tsupport_cartesianWedgeForm_subset {s t : ℕ}
    (omega : DifferentialForm E s) (eta : DifferentialForm F t) :
    tsupport (cartesianWedgeForm omega eta) ⊆ tsupport omega ×ˢ tsupport eta := by
  apply closure_minimal _ ((isClosed_tsupport omega).prod (isClosed_tsupport eta))
  intro z hz
  constructor
  · apply subset_closure
    intro hzero
    exact hz (by simp [cartesianWedgeForm, hzero,
      ← ContinuousAlternatingMap.compContinuousLinearMapCLM_apply])
  · apply subset_closure
    intro hzero
    exact hz (by simp [cartesianWedgeForm, hzero,
      ← ContinuousAlternatingMap.compContinuousLinearMapCLM_apply])

/-- Unlike either projection pullback separately, their exterior product
has compact support. This proves the test-form part of Simon (6.2.18). -/
theorem cartesianWedgeForm_isTestForm {s t : ℕ}
    {omega : DifferentialForm E s} {eta : DifferentialForm F t}
    (homega : IsTestForm omega) (heta : IsTestForm eta) :
    IsTestForm (cartesianWedgeForm omega eta) :=
  ⟨cartesianWedgeForm_isSmoothForm homega.1 heta.1,
    (homega.2.prod heta.2).of_isClosed_subset (isClosed_tsupport _)
      (tsupport_cartesianWedgeForm_subset omega eta)⟩

/-- A genuine compactly supported smooth test form on the product domain. -/
def cartesianWedgeTestOn {U : Set E} {V : Set F} {s t : ℕ}
    (omega : TestFormOn U s) (eta : TestFormOn V t) : TestFormOn (U ×ˢ V) (s + t) := by
  refine ⟨cartesianWedgeForm (omega : DifferentialForm E s) (eta : DifferentialForm F t), ?_⟩
  change IsTestForm (cartesianWedgeForm (omega : DifferentialForm E s) (eta : DifferentialForm F t)) ∧
    tsupport (cartesianWedgeForm (omega : DifferentialForm E s) (eta : DifferentialForm F t)) ⊆ U ×ˢ V
  exact ⟨cartesianWedgeForm_isTestForm (s := s) (t := t) omega.property.1 eta.property.1,
    (tsupport_cartesianWedgeForm_subset (omega : DifferentialForm E s) (eta : DifferentialForm F t)).trans
      (prod_mono omega.property.2 eta.property.2)⟩

@[simp] theorem cartesianWedgeTestOn_coe {U : Set E} {V : Set F} {s t : ℕ}
    (omega : TestFormOn U s) (eta : TestFormOn V t) :
    (cartesianWedgeTestOn omega eta : DifferentialForm (E × F) (s + t)) =
      cartesianWedgeForm omega eta := rfl

end

end Poincare.SimonGMT.Chapter06
