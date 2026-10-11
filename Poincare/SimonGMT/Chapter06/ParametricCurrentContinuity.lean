module

public import Mathlib.Topology.UniformSpace.HeineCantor
public import Poincare.SimonGMT.Chapter06.FixedSupportCurrentTopology

@[expose] public section

/-!
# Continuous parameter-dependent slices of a current

For a genuinely smooth compactly supported covector-valued function on `E × F`,
fixing the second variable gives a test form on `E`. These slices depend
continuously on the parameter in the topology of all derivatives, and applying
any geometric current gives a continuous compactly supported scalar function.

This proves the continuity and support part of the analytic assertion in the
construction (6.2.17). Smoothness of the scalar function, including interchange
of all parameter derivatives with the current, is a further obligation and is
not asserted here.
-/

open Filter Function Set TopologicalSpace
open scoped ContDiff Distributions Topology Uniformity

namespace Poincare.SimonGMT.Chapter06

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Joint continuity of all spatial derivatives implies continuity into the
fixed-support smooth-form topology. The parameter can be any topological space. -/
theorem continuous_fixedSupportTestForm_of_joint_derivatives
    {P : Type w} [TopologicalSpace P] (K : Compacts E) {n : ℕ}
    (omega : P → FixedSupportTestForm K n)
    (h : ∀ k : ℕ, Continuous (fun z : P × E =>
      iteratedFDeriv ℝ k (omega z.1 : DifferentialForm E n) z.2)) :
    Continuous omega := by
  apply continuous_iff_continuousAt.mpr
  intro y
  apply (fixedSupportTestForm_tendsto_iff K).mpr
  intro k V hV
  obtain ⟨W, hW, hclose⟩ := K.isCompact.mem_uniformity_of_prod
    (f := fun p x => iteratedFDeriv ℝ k (omega p : DifferentialForm E n) x)
    (s := univ) (h k).continuousOn (mem_univ y) (symm_le_uniformity hV)
  rw [nhdsWithin_univ] at hW
  filter_upwards [hW] with p hp x hx
  exact hclose p hp x hx

/-- Fix the parameter in a smooth compactly supported covector-valued function
on the product. The resulting genuine test form is supported in the first
projection of the original compact support. -/
def fixedSupportParameterSlice (K : Compacts (E × F)) {n : ℕ}
    (omega : ContDiffMapSupportedIn (E × F) (Covector E n) (⊤ : ℕ∞) K) (y : F) :
    FixedSupportTestForm (K.map Prod.fst continuous_fst) n where
  toFun x := omega (x, y)
  contDiff' := omega.contDiff.comp (contDiff_id.prodMk contDiff_const)
  zero_on_compl' := by
    intro x hx
    apply omega.zero_on_compl
    intro hxy
    exact hx ⟨(x, y), hxy, rfl⟩

@[simp] theorem fixedSupportParameterSlice_apply (K : Compacts (E × F)) {n : ℕ}
    (omega : ContDiffMapSupportedIn (E × F) (Covector E n) (⊤ : ℕ∞) K)
    (y : F) (x : E) : fixedSupportParameterSlice K omega y x = omega (x, y) := rfl

/-- The spatial jets of a slice are obtained by inserting first-factor
vectors into the corresponding total jets. This is an exact chain rule. -/
theorem iteratedFDeriv_fixedSupportParameterSlice (K : Compacts (E × F)) {n : ℕ}
    (omega : ContDiffMapSupportedIn (E × F) (Covector E n) (⊤ : ℕ∞) K)
    (y : F) (k : ℕ) (x : E) :
    iteratedFDeriv ℝ k (fixedSupportParameterSlice K omega y : DifferentialForm E n) x =
      (iteratedFDeriv ℝ k (omega : E × F → Covector E n) (x, y)).compContinuousLinearMap
        (fun _ : Fin k => ContinuousLinearMap.inl ℝ E F) := by
  let L := ContinuousLinearMap.inl ℝ E F
  have hshift : ContDiff ℝ ∞ (fun z : E × F => omega ((0, y) + z)) :=
    omega.contDiff.comp (contDiff_const.add contDiff_id)
  have hchain := L.iteratedFDeriv_comp_right hshift x (i := k) (by simp)
  change iteratedFDeriv ℝ k (fun x => omega (x, y)) x = _
  simpa only [Function.comp_def, L, ContinuousLinearMap.inl_apply,
    Prod.mk_add_mk, zero_add, add_zero, iteratedFDeriv_comp_add_left] using hchain

/-- A smooth compactly supported product function is continuous as a family
of fixed-support test forms in its remaining parameter. -/
theorem continuous_fixedSupportParameterSlice (K : Compacts (E × F)) {n : ℕ}
    (omega : ContDiffMapSupportedIn (E × F) (Covector E n) (⊤ : ℕ∞) K) :
    Continuous (fixedSupportParameterSlice K omega) := by
  apply continuous_fixedSupportTestForm_of_joint_derivatives
  intro k
  simp_rw [iteratedFDeriv_fixedSupportParameterSlice]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin k => ContinuousLinearMap.inl ℝ E F)).continuous.comp
      ((omega.contDiff.continuous_iteratedFDeriv (by simp)).comp continuous_swap)

/-- Applying a current to a parameter slice. The support hypothesis only
ensures that the original product function lies over the current's domain. -/
def GeometricCurrentOn.parameterSliceValue {U : Set E} {n : ℕ}
    (T : GeometricCurrentOn U n) (K : Compacts (E × F))
    (hKU : Prod.fst '' (K : Set (E × F)) ⊆ U)
    (omega : ContDiffMapSupportedIn (E × F) (Covector E n) (⊤ : ℕ∞) K) : F → ℝ :=
  fun y => T (fixedSupportTestFormInclusion (K.map Prod.fst continuous_fst) hKU n
    (fixedSupportParameterSlice K omega y))

/-- The current's slice evaluation is continuous; this uses the current's
proved fixed-support continuity, not an extra parameter-continuity hypothesis. -/
theorem GeometricCurrentOn.continuous_parameterSliceValue {U : Set E} {n : ℕ}
    (T : GeometricCurrentOn U n) (K : Compacts (E × F))
    (hKU : Prod.fst '' (K : Set (E × F)) ⊆ U)
    (omega : ContDiffMapSupportedIn (E × F) (Covector E n) (⊤ : ℕ∞) K) :
    Continuous (T.parameterSliceValue K hKU omega) :=
  (T.fixedSupportCLM (K.map Prod.fst continuous_fst) hKU).continuous.comp
    (continuous_fixedSupportParameterSlice K omega)

/-- Slice evaluation has support in the second projection of the original
compact support, exactly as required in the product-current construction. -/
theorem GeometricCurrentOn.tsupport_parameterSliceValue_subset {U : Set E} {n : ℕ}
    (T : GeometricCurrentOn U n) (K : Compacts (E × F))
    (hKU : Prod.fst '' (K : Set (E × F)) ⊆ U)
    (omega : ContDiffMapSupportedIn (E × F) (Covector E n) (⊤ : ℕ∞) K) :
    tsupport (T.parameterSliceValue K hKU omega) ⊆ Prod.snd '' (K : Set (E × F)) := by
  apply closure_minimal _ (K.isCompact.image continuous_snd).isClosed
  intro y hy
  by_contra hyK
  have hslice : fixedSupportParameterSlice K omega y = 0 := by
    apply DFunLike.ext
    intro x
    change omega (x, y) = 0
    apply omega.zero_on_compl
    intro hxy
    exact hyK ⟨(x, y), hxy, rfl⟩
  apply hy
  simp only [GeometricCurrentOn.parameterSliceValue, hslice, map_zero]

/-- The continuity part of (6.2.17) produces an actual compactly supported
scalar function, ready for the remaining parameter-differentiation argument. -/
theorem GeometricCurrentOn.hasCompactSupport_parameterSliceValue {U : Set E} {n : ℕ}
    (T : GeometricCurrentOn U n) (K : Compacts (E × F))
    (hKU : Prod.fst '' (K : Set (E × F)) ⊆ U)
    (omega : ContDiffMapSupportedIn (E × F) (Covector E n) (⊤ : ℕ∞) K) :
    HasCompactSupport (T.parameterSliceValue K hKU omega) :=
  (K.isCompact.image continuous_snd).of_isClosed_subset (isClosed_tsupport _)
    (T.tsupport_parameterSliceValue_subset K hKU omega)

end

end Poincare.SimonGMT.Chapter06
