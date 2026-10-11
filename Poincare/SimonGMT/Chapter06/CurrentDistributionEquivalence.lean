module

public import Mathlib.Analysis.Distribution.TestFunction
public import Poincare.SimonGMT.Chapter06.FixedSupportCurrentTopology

@[expose] public section

/-!
# Currents as the continuous dual of the actual test-form LF space

Simon's sequential definition and the continuous-dual definition agree. This
file proves the equivalence, rather than assuming continuity in a second
topology. Its fixed-support input is the topology of all uniform derivative
seminorms, and its global input is Mathlib's locally convex inductive-limit
topology on compactly supported `C∞` functions with values in covectors.
-/

open Filter Function Set TopologicalSpace
open scoped ContDiff Distributions Topology

namespace Poincare.SimonGMT.Chapter06

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The algebraic identification of Simon's test forms with Mathlib's actual
covector-valued `C∞` test functions on an open domain. -/
def testFormOnEquivTestFunction (U : Opens E) (n : ℕ) :
    TestFormOn (U : Set E) n ≃ₗ[ℝ] 𝓓(U, Covector E n) where
  toFun omega :=
    { toFun := omega
      contDiff' := omega.property.1.1
      hasCompactSupport' := omega.property.1.2
      tsupport_subset' := omega.property.2 }
  invFun omega := ⟨omega, ⟨omega.contDiff, omega.hasCompactSupport⟩, omega.tsupport_subset⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := TestFunction.ext (fun _ => rfl)
  map_add' _ _ := TestFunction.ext (fun _ => rfl)
  map_smul' _ _ := TestFunction.ext (fun _ => rfl)

@[simp] theorem testFormOnEquivTestFunction_apply (U : Opens E) (n : ℕ)
    (omega : TestFormOn (U : Set E) n) (x : E) :
    testFormOnEquivTestFunction U n omega x = (omega : DifferentialForm E n) x := rfl

@[simp] theorem testFormOnEquivTestFunction_symm_apply (U : Opens E) (n : ℕ)
    (omega : 𝓓(U, Covector E n)) :
    (testFormOnEquivTestFunction U n |>.symm omega : DifferentialForm E n) = omega := rfl

/-- A geometric current is a genuine continuous linear functional on the
locally convex inductive-limit topology of all compactly supported test forms. -/
def GeometricCurrentOn.distributionCLM (U : Opens E) {n : ℕ}
    (T : GeometricCurrentOn (U : Set E) n) : 𝓓(U, Covector E n) →L[ℝ] ℝ where
  toLinearMap := T.toCurrent.comp (testFormOnEquivTestFunction U n).symm.toLinearMap
  cont := by
    apply (TestFunction.continuous_iff_continuous_comp _).mpr
    intro K hKU
    exact T.continuous_fixedSupport K hKU

@[simp] theorem GeometricCurrentOn.distributionCLM_apply (U : Opens E) {n : ℕ}
    (T : GeometricCurrentOn (U : Set E) n) (omega : 𝓓(U, Covector E n)) :
    T.distributionCLM U omega = T ((testFormOnEquivTestFunction U n).symm omega) := rfl

/-- Simon's common-support, all-derivatives convergence implies convergence
in the actual LF test-function topology. -/
theorem TestFormOnConverges.tendsto_testFunction (U : Opens E) {n : ℕ}
    {omegaSeq : ℕ → TestFormOn (U : Set E) n} {omega : TestFormOn (U : Set E) n}
    (h : TestFormOnConverges omegaSeq omega) :
    Tendsto (fun j => testFormOnEquivTestFunction U n (omegaSeq j)) atTop
      (𝓝 (testFormOnEquivTestFunction U n omega)) := by
  rcases h with ⟨K, hK, hKU, hseq, homega, hderiv⟩
  let Kc : Compacts E := ⟨K, hK⟩
  let seqK : ℕ → FixedSupportTestForm Kc n := fun j =>
    ContDiffMapSupportedIn.of_support_subset (omegaSeq j).property.1.1
      ((subset_tsupport (omegaSeq j : DifferentialForm E n)).trans (hseq j))
  let omegaK : FixedSupportTestForm Kc n :=
    ContDiffMapSupportedIn.of_support_subset omega.property.1.1
      ((subset_tsupport (omega : DifferentialForm E n)).trans homega)
  have hconv : Tendsto seqK atTop (𝓝 omegaK) :=
    (fixedSupportTestForm_tendsto_iff Kc).mpr hderiv
  exact (TestFunction.continuous_ofSupportedIn hKU).tendsto omegaK |>.comp hconv

/-- Every continuous linear functional on the actual LF test-form space
satisfies Simon's sequential condition, with the identical action on forms. -/
def geometricCurrentOnOfDistribution (U : Opens E) (n : ℕ)
    (L : 𝓓(U, Covector E n) →L[ℝ] ℝ) : GeometricCurrentOn (U : Set E) n where
  toCurrent := L.toLinearMap.comp (testFormOnEquivTestFunction U n).toLinearMap
  continuous' := by
    intro omegaSeq h
    change Tendsto (fun j => L (testFormOnEquivTestFunction U n (omegaSeq j))) atTop (𝓝 0)
    simpa only [map_zero, Function.comp_def] using
      (L.continuous.tendsto (testFormOnEquivTestFunction U n 0)).comp
        (h.tendsto_testFunction U)

@[simp] theorem geometricCurrentOnOfDistribution_apply (U : Opens E) (n : ℕ)
    (L : 𝓓(U, Covector E n) →L[ℝ] ℝ) (omega : TestFormOn (U : Set E) n) :
    geometricCurrentOnOfDistribution U n L omega = L (testFormOnEquivTestFunction U n omega) := rfl

/-- Simon's geometric currents are exactly the continuous dual of the
covector-valued test-function LF space. Both inverse laws hold on actual
forms; there is no assumed bridge or abstract replacement for a current. -/
def geometricCurrentOnEquivDistribution (U : Opens E) (n : ℕ) :
    GeometricCurrentOn (U : Set E) n ≃ (𝓓(U, Covector E n) →L[ℝ] ℝ) where
  toFun := GeometricCurrentOn.distributionCLM U
  invFun := geometricCurrentOnOfDistribution U n
  left_inv _ := GeometricCurrentOn.ext (fun _ => rfl)
  right_inv _ := ContinuousLinearMap.ext (fun _ => rfl)

/-- Exterior differentiation as a continuous linear map of the genuine LF
test-function spaces. It is the derivative followed by alternation. -/
def testFunctionExteriorDerivativeCLM (U : Opens E) (n : ℕ) :
    𝓓(U, Covector E n) →L[ℝ] 𝓓(U, Covector E (n + 1)) :=
  (TestFunction.postcompCLM (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ)).comp
    (TestFunction.fderivCLM ℝ (⊤ : ℕ∞) (⊤ : ℕ∞))

@[simp] theorem testFunctionExteriorDerivativeCLM_coe (U : Opens E) (n : ℕ)
    (omega : 𝓓(U, Covector E n)) :
    (testFunctionExteriorDerivativeCLM U n omega : DifferentialForm E (n + 1)) =
      exteriorDerivative (omega : DifferentialForm E n) := by
  simp only [testFunctionExteriorDerivativeCLM, ContinuousLinearMap.comp_apply,
    TestFunction.postcompCLM_apply, TestFunction.fderivCLM_apply_of_le omega (by simp)]
  rfl

/-- The LF exterior derivative agrees with the previously constructed
exterior derivative on Simon's test forms, with no change of convention. -/
theorem testFormOnEquivTestFunction_exteriorDerivative (U : Opens E) (n : ℕ)
    (omega : TestFormOn (U : Set E) n) :
    testFunctionExteriorDerivativeCLM U n (testFormOnEquivTestFunction U n omega) =
      testFormOnEquivTestFunction U (n + 1) (exteriorDerivativeTestOn (U : Set E) n omega) := by
  apply TestFunction.ext
  intro x
  rw [← DFunLike.coe_fn_eq, testFunctionExteriorDerivativeCLM_coe]
  rfl

/-- Under the continuous-dual equivalence, boundary is the transpose of
exterior differentiation, exactly as in Simon (6.2.3). -/
theorem GeometricCurrentOn.distributionCLM_boundary (U : Opens E) {n : ℕ}
    (T : GeometricCurrentOn (U : Set E) (n + 1)) :
    T.boundary.distributionCLM U =
      (T.distributionCLM U).comp (testFunctionExteriorDerivativeCLM U n) := by
  apply ContinuousLinearMap.ext
  intro omega
  change T (exteriorDerivativeTestOn (U : Set E) n
      ((testFormOnEquivTestFunction U n).symm omega)) =
    T ((testFormOnEquivTestFunction U (n + 1)).symm
      (testFunctionExteriorDerivativeCLM U n omega))
  exact congrArg T (Subtype.ext (testFunctionExteriorDerivativeCLM_coe U n omega).symm)

end

end Poincare.SimonGMT.Chapter06
