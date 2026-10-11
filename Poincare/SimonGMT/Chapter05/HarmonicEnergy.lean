module

public import Poincare.SimonGMT.Chapter05.GraphAreaExpansion

public section

/-!
# Simon GMT, Chapter 5, §1: the harmonic-comparison energy estimate

This module isolates the rigorous Hilbert-space argument behind (1.5).  The
geometric input is the weak equation for the difference between the minimal
graph and its harmonic replacement.  Once the residual field is cubically
bounded, Young's inequality gives the sixth-power energy estimate exactly.

The construction of the residual from the derivative of the graph-area
remainder is a separate part of (1.2)--(1.3), so it is not assumed silently
here.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace Poincare.SimonGMT.Chapter05

noncomputable section

universe u v

variable {X : Type u} {F : Type v} [MeasurableSpace X]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The pointwise Dirichlet density of a finite family of vector fields. -/
@[expose] def dirichletDensity {n : ℕ} (w : X → Fin n → F) (x : X) : ℝ :=
  ∑ i, ‖w x i‖ ^ 2

/-- The pointwise pairing of a residual field with a test gradient. -/
def residualPairing {n : ℕ} (A w : X → Fin n → F) (x : X) : ℝ :=
  ∑ i, inner ℝ (A x i) (w x i)

/-- Finite-dimensional Cauchy--Young, in the exact form used in the proof of
Simon (1.5). -/
theorem two_mul_residualPairing_le {n : ℕ} (A w : Fin n → F) :
    2 * (∑ i, inner ℝ (A i) (w i)) ≤
      (∑ i, ‖A i‖ ^ 2) + ∑ i, ‖w i‖ ^ 2 := by
  calc
    2 * (∑ i, inner ℝ (A i) (w i)) =
        ∑ i, 2 * inner ℝ (A i) (w i) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ i, (‖A i‖ ^ 2 + ‖w i‖ ^ 2) := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      calc
        2 * inner ℝ (A i) (w i) ≤ 2 * (‖A i‖ * ‖w i‖) := by
          gcongr
          exact real_inner_le_norm _ _
        _ ≤ ‖A i‖ ^ 2 + ‖w i‖ ^ 2 := by
          simpa [mul_assoc] using two_mul_le_sq_add_sq ‖A i‖ ‖w i‖
    _ = (∑ i, ‖A i‖ ^ 2) + ∑ i, ‖w i‖ ^ 2 := by
      rw [Finset.sum_add_distrib]

/-- A weak residual identity controls the full Dirichlet energy by the
residual energy.  This is the absorption step in Simon (1.5). -/
theorem weakResidual_energy_le {n : ℕ} (μ : Measure X)
    (A w : X → Fin n → F)
    (hA : Integrable (dirichletDensity A) μ)
    (hw : Integrable (dirichletDensity w) μ)
    (hpair : Integrable (residualPairing A w) μ)
    (hweak : (∫ x, dirichletDensity w x ∂μ) =
      ∫ x, residualPairing A w x ∂μ) :
    (∫ x, dirichletDensity w x ∂μ) ≤
      ∫ x, dirichletDensity A x ∂μ := by
  have hpoint : ∀ x, residualPairing A w x ≤
      (1 / 2 : ℝ) * dirichletDensity A x +
        (1 / 2 : ℝ) * dirichletDensity w x := by
    intro x
    have h := two_mul_residualPairing_le (A x) (w x)
    dsimp [residualPairing, dirichletDensity] at h ⊢
    linarith
  have hright : Integrable
      (fun x ↦ (1 / 2 : ℝ) * dirichletDensity A x +
        (1 / 2 : ℝ) * dirichletDensity w x) μ :=
    (hA.const_mul _).add (hw.const_mul _)
  have hmono : (∫ x, residualPairing A w x ∂μ) ≤
      ∫ x, ((1 / 2 : ℝ) * dirichletDensity A x +
        (1 / 2 : ℝ) * dirichletDensity w x) ∂μ :=
    integral_mono hpair hright hpoint
  rw [integral_add (hA.const_mul _) (hw.const_mul _),
    integral_const_mul, integral_const_mul] at hmono
  rw [hweak]
  linarith

/-- Simon (1.5), abstracted only over the preceding weak equation: a cubic
pointwise residual bound yields the sixth-power harmonic-comparison estimate.
-/
theorem harmonicComparison_energy_le_sixthPower {n : ℕ} (μ : Measure X)
    (Du Dv A : X → Fin n → F) (C : ℝ)
    (hA : Integrable (dirichletDensity A) μ)
    (hdiff : Integrable
      (dirichletDensity (fun x i ↦ Du x i - Dv x i)) μ)
    (hpair : Integrable
      (residualPairing A (fun x i ↦ Du x i - Dv x i)) μ)
    (hcubic : Integrable (fun x ↦ C * (dirichletDensity Du x) ^ 3) μ)
    (hweak : (∫ x, dirichletDensity (fun y i ↦ Du y i - Dv y i) x ∂μ) =
      ∫ x, residualPairing A (fun y i ↦ Du y i - Dv y i) x ∂μ)
    (hbound : ∀ x, dirichletDensity A x ≤
      C * (dirichletDensity Du x) ^ 3) :
    (∫ x, dirichletDensity (fun y i ↦ Du y i - Dv y i) x ∂μ) ≤
      C * ∫ x, (dirichletDensity Du x) ^ 3 ∂μ := by
  calc
    (∫ x, dirichletDensity (fun y i ↦ Du y i - Dv y i) x ∂μ) ≤
        ∫ x, dirichletDensity A x ∂μ :=
      weakResidual_energy_le μ A (fun x i ↦ Du x i - Dv x i)
        hA hdiff hpair hweak
    _ ≤ ∫ x, C * (dirichletDensity Du x) ^ 3 ∂μ :=
      integral_mono hA hcubic hbound
    _ = C * ∫ x, (dirichletDensity Du x) ^ 3 ∂μ := by
      rw [integral_const_mul]

end

end Poincare.SimonGMT.Chapter05
