module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Support
public import Poincare.SimonGMT.Chapter06.Currents

@[expose] public section

/-!
# Simon GMT, Chapter 6, §2.7--§2.12: finite-mass representations

This file packages conditional representation data for the algebraic
comass-mass API: a locally finite measure, a measurable unit orientation
functional, the integral action formula, and the characterization by local
mass. Simon uses the Euclidean coefficient norm, as implemented for domain
currents in `Chapter06.Mass`; the bridge to that convention and the analytic
existence theorem from LF continuity remain pending.

Once a representation is supplied, restrictions and locally integrable
weights are constructed as genuine currents and their action formulas are
proved from the Bochner integral.
-/

open Filter Function Set
open scoped ENNReal MeasureTheory Topology

namespace Poincare.SimonGMT.Chapter06

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A generalized oriented `n`-vector is represented by its continuous action
on the fibre of `n`-covectors. -/
abbrev OrientationFunctional (E : Type u) [NormedAddCommGroup E]
    [NormedSpace ℝ E] (n : ℕ) :=
  Covector E n →L[ℝ] ℝ

namespace Current

/-- Conditional representation data analogous to Simon (6.2.7)--(6.2.8),
for the algebraic comass API. `pairing_integrable` ensures that each displayed
Bochner integral exists and that the restrictions below remain linear; no
representation existence theorem is claimed here. -/
structure MassRepresentation {n : ℕ} (T : Current E n) where
  measure : MeasureTheory.Measure E
  locallyFinite_measure : MeasureTheory.IsLocallyFiniteMeasure measure
  orientation : E → OrientationFunctional E n
  weaklyAEMeasurable_orientation : ∀ alpha : Covector E n,
    AEMeasurable (fun x ↦ orientation x alpha) measure
  unit_orientation : ∀ᵐ x ∂measure, ‖orientation x‖ = 1
  pairing_integrable : ∀ omega : TestForm E n,
    MeasureTheory.Integrable
      (fun x ↦ orientation x ((omega : DifferentialForm E n) x)) measure
  action : ∀ omega : TestForm E n,
    T omega = ∫ x, orientation x ((omega : DifferentialForm E n) x) ∂measure
  mass_characterization : ∀ W : Set E, IsOpen W → IsCompact (closure W) →
    T.massOn W = measure W
  total_mass : T.mass = measure univ

namespace MassRepresentation

variable {n : ℕ} {T : Current E n} (R : T.MassRepresentation)

instance instIsLocallyFiniteMeasure :
    MeasureTheory.IsLocallyFiniteMeasure R.measure :=
  R.locallyFinite_measure

/-- Simon (6.2.9): restriction of a represented current to a measurable set.
The same formula makes sense for an arbitrary set because Mathlib's restricted
measure uses its measurable hull. -/
def restrict (A : Set E) : Current E n where
  toFun omega :=
    ∫ x in A, R.orientation x ((omega : DifferentialForm E n) x) ∂R.measure
  map_add' omega eta := by
    rw [show (fun x ↦ R.orientation x
        (((omega + eta : TestForm E n) : DifferentialForm E n) x)) =
        (fun x ↦ R.orientation x ((omega : DifferentialForm E n) x) +
          R.orientation x ((eta : DifferentialForm E n) x)) by
      funext x
      simp]
    rw [MeasureTheory.integral_add
      (R.pairing_integrable omega).integrableOn
      (R.pairing_integrable eta).integrableOn]
  map_smul' c omega := by
    rw [show (fun x ↦ R.orientation x
        (((c • omega : TestForm E n) : DifferentialForm E n) x)) =
        (fun x ↦ c • R.orientation x ((omega : DifferentialForm E n) x)) by
      funext x
      simp]
    exact MeasureTheory.integral_smul c _

@[simp] theorem restrict_apply (A : Set E) (omega : TestForm E n) :
    R.restrict A omega =
      ∫ x in A, R.orientation x ((omega : DifferentialForm E n) x) ∂R.measure :=
  rfl

/-- Restriction to the whole space recovers the represented current. -/
@[simp] theorem restrict_univ : R.restrict univ = T := by
  apply LinearMap.ext
  intro omega
  simpa using (R.action omega).symm

/-- The boundary of a restricted represented current is evaluated by first
applying the exterior derivative, exactly as in (6.2.3). -/
theorem restrict_boundary_apply {k : ℕ}
    {S : Current E (k + 1)} (Q : S.MassRepresentation)
    (A : Set E) (omega : TestForm E k) :
    (Q.restrict A).boundary omega =
      ∫ x in A, Q.orientation x
        (exteriorDerivative (omega : DifferentialForm E k) x) ∂Q.measure :=
  rfl

/-- Simon (6.2.10): multiplication by a scalar weight.  The explicit
integrability witness is exactly what is needed for the Bochner formula; in
the source it follows from local integrability of `phi`, unit orientation, and
compact support of each test form. -/
def weighted (phi : E → ℝ)
    (hphi : ∀ omega : TestForm E n,
      MeasureTheory.Integrable
        (fun x ↦ phi x * R.orientation x
          ((omega : DifferentialForm E n) x)) R.measure) : Current E n where
  toFun omega :=
    ∫ x, phi x * R.orientation x ((omega : DifferentialForm E n) x) ∂R.measure
  map_add' omega eta := by
    rw [show (fun x ↦ phi x * R.orientation x
        (((omega + eta : TestForm E n) : DifferentialForm E n) x)) =
        (fun x ↦ phi x * R.orientation x ((omega : DifferentialForm E n) x) +
          phi x * R.orientation x ((eta : DifferentialForm E n) x)) by
      funext x
      simp [mul_add]]
    exact MeasureTheory.integral_add (hphi omega) (hphi eta)
  map_smul' c omega := by
    rw [show (fun x ↦ phi x * R.orientation x
        (((c • omega : TestForm E n) : DifferentialForm E n) x)) =
        (fun x ↦ c • (phi x * R.orientation x
          ((omega : DifferentialForm E n) x))) by
      funext x
      simp [mul_left_comm]]
    exact MeasureTheory.integral_smul c _

@[simp] theorem weighted_apply (phi : E → ℝ)
    (hphi : ∀ omega : TestForm E n,
      MeasureTheory.Integrable
        (fun x ↦ phi x * R.orientation x
          ((omega : DifferentialForm E n) x)) R.measure)
    (omega : TestForm E n) :
    R.weighted phi hphi omega =
      ∫ x, phi x * R.orientation x
        ((omega : DifferentialForm E n) x) ∂R.measure :=
  rfl

end MassRepresentation

end Current

end

end Poincare.SimonGMT.Chapter06
