module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Topology.Algebra.Support

@[expose] public section

/-!
# Simon GMT, Chapter 6, §1: covectors and differential forms

Mathlib represents an `n`-covector by a continuous alternating map indexed by
`Fin n`, exactly the analytic object used by Simon.  This file connects the
book's notation to that representation and verifies the exterior-derivative
identities, including `d² = 0` (6.1.12) and naturality under pullback
(6.1.14), on open domains.
-/

open Function Set
open scoped ContDiff Topology

namespace Poincare.SimonGMT.Chapter06

noncomputable section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Simon §6.1: an `n`-covector on `E`. -/
abbrev Covector (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) :=
  E [⋀^Fin n]→L[ℝ] ℝ

/-- Simon §6.1: a differential `n`-form on an open Euclidean domain.  We
represent it on the ambient space; support conditions specify the domain used
by a current. -/
abbrev DifferentialForm (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) := E → Covector E n

/-- Smooth forms `ℰⁿ(U)` in Simon's notation (here on the ambient space).
The order is `∞` (all finite derivatives), not `⊤ = ω` (real analyticity). -/
def IsSmoothForm {n : ℕ} (omega : DifferentialForm E n) : Prop :=
  ContDiff ℝ ∞ omega

/-- Compactly supported smooth forms `ᶟⁿ(U)` in Simon's notation. -/
def IsTestForm {n : ℕ} (omega : DifferentialForm E n) : Prop :=
  IsSmoothForm omega ∧ HasCompactSupport omega

/-! ### Forms on open domains -/

/-- A smooth `n`-form on a domain `U`, represented by an ambient form smooth
on `U`. All domain operations below use within-derivatives and are asserted
only on `U`, so they depend only on the restriction to the open domain. -/
abbrev SmoothFormOn (U : Set E) (n : ℕ) :=
  {omega : DifferentialForm E n // ContDiffOn ℝ ∞ omega U}

/-- Simon (6.1.11) on a domain: exterior differentiation uses the derivative
within the domain. -/
def exteriorDerivativeOn {n : ℕ} (U : Set E) (omega : DifferentialForm E n) :
    DifferentialForm E (n + 1) :=
  extDerivWithin omega U

/-- Pullback of an `n`-form by `f`, using the derivative of `f` within its
domain `U`. This is Simon's `fⁿω` from (6.1.13). -/
def pullbackFormWithin {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} (U : Set E) (f : E → F) (omega : DifferentialForm F n) :
    DifferentialForm E n :=
  fun x ↦ (omega (f x)).compContinuousLinearMap (fderivWithin ℝ f U x)

/-- Simon (6.1.11), expanded on a domain as the alternating sum of
within-directional derivatives. -/
theorem exteriorDerivativeOn_apply {n : ℕ} {U : Set E}
    {omega : DifferentialForm E n} {x : E}
    (homega : DifferentiableWithinAt ℝ omega U x)
    (hU : UniqueDiffWithinAt ℝ U x) (w : Fin (n + 1) → E) :
    exteriorDerivativeOn U omega x w =
      ∑ i, (-1 : ℤ) ^ i.val •
        fderivWithin ℝ (omega · (i.removeNth w)) U x (w i) :=
  extDerivWithin_apply homega hU w

/-- Simon (6.1.12) on an open domain: `d(dω)=0` at every point of the
domain. -/
theorem exteriorDerivativeOn_sq {n : ℕ} {U : Set E} (hU : IsOpen U)
    (omega : SmoothFormOn (E := E) U n) :
    EqOn (exteriorDerivativeOn U
      (exteriorDerivativeOn U (omega : DifferentialForm E n))) 0 U := by
  intro x hx
  apply extDerivWithin_extDerivWithin_apply
    (omega.property x hx) (by simp) hU.uniqueDiffOn
  · rw [hU.interior_eq]
    exact subset_closure hx
  · exact hx

/-- Simon (6.1.14): exterior differentiation commutes with pullback by a
smooth map between open domains, `d(fⁿω)=fⁿ(dω)`. -/
theorem exteriorDerivativeOn_pullbackFormWithin
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {U : Set E} {V : Set F} (hU : IsOpen U) (_hV : IsOpen V)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (hmap : MapsTo f U V)
    (omega : SmoothFormOn (E := F) V n) :
    EqOn
      (exteriorDerivativeOn U
        (pullbackFormWithin U f (omega : DifferentialForm F n)))
      (pullbackFormWithin U f
        (exteriorDerivativeOn V (omega : DifferentialForm F n))) U := by
  intro x hx
  exact extDerivWithin_pullback
    ((omega.property (f x) (hmap hx)).differentiableWithinAt (by simp))
    (hf x hx) (by simp) hU.uniqueDiffOn
    (by rw [hU.interior_eq]; exact subset_closure hx) hx hmap

/-- Simon (6.1.11): exterior derivative. -/
abbrev exteriorDerivative {n : ℕ} (omega : DifferentialForm E n) :
    DifferentialForm E (n + 1) :=
  extDeriv omega

/-- Simon (6.1.11), expanded as the alternating sum of directional
derivatives. -/
theorem exteriorDerivative_apply {n : ℕ} {omega : DifferentialForm E n}
    {x : E} (homega : DifferentiableAt ℝ omega x) (v : Fin (n + 1) → E) :
    exteriorDerivative omega x v =
      ∑ i, (-1 : ℤ) ^ i.val •
        fderiv ℝ (omega · (i.removeNth v)) x (v i) :=
  extDeriv_apply homega v

/-- Exterior derivative is additive on smooth forms. -/
theorem exteriorDerivative_add {n : ℕ} {omega eta : DifferentialForm E n}
    (homega : IsSmoothForm omega) (heta : IsSmoothForm eta) :
    exteriorDerivative (omega + eta) =
      exteriorDerivative omega + exteriorDerivative eta := by
  funext x
  exact extDeriv_add (homega.differentiable (by simp)).differentiableAt
    (heta.differentiable (by simp)).differentiableAt

/-- Exterior derivative commutes with scalar multiplication. -/
theorem exteriorDerivative_smul {n : ℕ} (c : ℝ) (omega : DifferentialForm E n) :
    exteriorDerivative (c • omega) = c • exteriorDerivative omega := by
  funext x
  exact extDeriv_smul c omega

/-- Simon (6.1.12): the second exterior derivative vanishes for smooth forms. -/
theorem exteriorDerivative_sq {n : ℕ} {omega : DifferentialForm E n}
    (homega : IsSmoothForm omega) :
    exteriorDerivative (exteriorDerivative omega) = 0 := by
  exact extDeriv_extDeriv homega (by simp)

end

end Poincare.SimonGMT.Chapter06
