module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Topology.Algebra.Module.Alternating.Topology
public import Poincare.SimonGMT.Chapter06.Currents

@[expose] public section

/-!
# Simon GMT, Chapter 6, §2.17--§2.22: a genuine product-current case

The full Cartesian product of two arbitrary currents requires the LF-topology
continuity argument for slicing a test form.  This file implements the important
degree-zero factor exactly: the point current `{p}` and Simon formula (6.2.22)
for `{p} × T`.  This is a real construction on test forms, not an abstract
product-operation interface.  The general `(s,t)` product and its Leibniz
boundary formula remain pending.
-/

open Filter Function Set
open scoped ContDiff Topology

namespace Poincare.SimonGMT.Chapter06

noncomputable section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Restrict a form on `E × F` to the slice `{p} × F`, retaining only vectors
in the `F` direction. -/
def pointSlice (p : E) {n : ℕ} (omega : DifferentialForm (E × F) n) :
    DifferentialForm F n :=
  fun y ↦ (omega (p, y)).compContinuousLinearMap
    (ContinuousLinearMap.inr ℝ E F)

/-- Slicing at a point preserves smoothness and compact support. -/
theorem pointSlice_isTestForm (p : E) {n : ℕ}
    {omega : DifferentialForm (E × F) n} (homega : IsTestForm omega) :
    IsTestForm (pointSlice p omega) := by
  change IsSmoothForm omega ∧ HasCompactSupport omega at homega
  constructor
  · change ContDiff ℝ ∞ (fun y ↦
      (omega (p, y)).compContinuousLinearMap (ContinuousLinearMap.inr ℝ E F))
    simpa only [← ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
      Function.comp_def, id_eq] using
      (ContinuousAlternatingMap.compContinuousLinearMapCLM
        (ContinuousLinearMap.inr ℝ E F)).contDiff.comp
          (homega.1.comp (contDiff_const.prodMk contDiff_id))
  · have hemb : Topology.IsClosedEmbedding (fun y : F ↦ (p, y)) := by
      refine ⟨isEmbedding_prodMkRight p, ?_⟩
      have hrange : range (fun y : F ↦ (p, y)) = {z : E × F | z.1 = p} := by
        ext z
        constructor
        · rintro ⟨y, rfl⟩
          rfl
        · intro hz
          exact ⟨z.2, Prod.ext hz.symm rfl⟩
      rw [hrange]
      exact isClosed_eq continuous_fst continuous_const
    have hcompact : IsCompact ((fun y : F ↦ (p, y)) ⁻¹' tsupport omega) :=
      hemb.isCompact_preimage homega.2
    apply IsCompact.of_isClosed_subset hcompact (isClosed_tsupport _)
    intro y hy
    change y ∈ tsupport
      ((fun alpha ↦ alpha.compContinuousLinearMap (ContinuousLinearMap.inr ℝ E F)) ∘
        (fun y : F ↦ omega (p, y))) at hy
    have hy' : y ∈ tsupport (fun y : F ↦ omega (p, y)) :=
      (tsupport_comp_subset (g := fun alpha ↦
        alpha.compContinuousLinearMap (ContinuousLinearMap.inr ℝ E F)) rfl _) hy
    exact tsupport_comp_subset_preimage
      (f := fun y : F ↦ (p, y)) omega (by fun_prop) hy'

/-- The slice operation as a linear map of test-form spaces. -/
def pointSliceTest (p : E) (n : ℕ) :
    TestForm (E × F) n →ₗ[ℝ] TestForm F n where
  toFun omega := ⟨pointSlice p omega, pointSlice_isTestForm p omega.property⟩
  map_add' omega eta := by
    apply Subtype.ext
    funext y
    ext v
    simp [pointSlice]
  map_smul' c omega := by
    apply Subtype.ext
    funext y
    ext v
    simp [pointSlice]

/-- The Dirac point `0`-current `{p}` used in Simon (6.2.21)--(6.2.22). -/
def pointCurrent (p : E) : Current E 0 where
  toFun omega := (omega : DifferentialForm E 0) p 0
  map_add' omega eta := by simp
  map_smul' c omega := by simp

@[simp] theorem pointCurrent_apply (p : E) (omega : TestForm E 0) :
    pointCurrent p omega = (omega : DifferentialForm E 0) p 0 :=
  rfl

/-- Simon (6.2.22): Cartesian product with a point current, defined by slicing
the test form at that point. -/
def Current.pointProduct {n : ℕ} (p : E) (T : Current F n) :
    Current (E × F) n :=
  T.comp (pointSliceTest p n)

@[simp] theorem Current.pointProduct_apply {n : ℕ} (p : E)
    (T : Current F n) (omega : TestForm (E × F) n) :
    T.pointProduct p omega = T ((pointSliceTest p n) omega) :=
  rfl

end

end Poincare.SimonGMT.Chapter06
