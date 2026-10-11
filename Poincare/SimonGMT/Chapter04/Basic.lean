module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.WithDensityFinite
public import Mathlib.Topology.Semicontinuity.Basic
public import Poincare.SimonGMT.Chapter03.Rectifiable

public section

/-!
# Simon GMT, Chapter 4: rectifiable varifolds

This file starts the missing Mathlib layer needed by Chapter 4.  The definitions
use Mathlib's Euclidean Hausdorff measure, measurable densities, Radon support,
and finite-dimensional real subspaces.  Source tags refer to the printed book.

The first-variation definitions and the concrete stationary monotonicity chain
are developed in `Chapter04.FirstVariation`. The radial-cutoff argument there
derives the fundamental identity from stationarity; it is not a field of the
varifold structure.
-/

open Filter Function Set
open scoped ENNReal MeasureTheory Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Chapter 4 uses the countable-rectifiability definition from Chapter 3. -/
abbrev CountablyRectifiable (n : ℕ) (s : Set E) : Prop :=
  Poincare.SimonGMT.Chapter03.CountablyRectifiable n s

/-- Concrete data for Simon's rectifiable `n`-varifold `v(M,θ)`.

The tangent is not arbitrary rank-`n` data: `approximate_tangent` links it to
Chapter 3's blow-up definition almost everywhere, and its orthogonal projection
is measurable for the weight measure. This is a strengthened representative
of Simon's a.e.-equivalence class. Tangent-representative independence follows
from Chapter 3 uniqueness and is proved below; existence for every rectifiable
carrier and the full carrier/multiplicity null-change quotient remain open. -/
structure RectifiableVarifold (n : ℕ) where
  carrier : Set E
  measurable_carrier : MeasurableSet carrier
  rectifiable_carrier : CountablyRectifiable n carrier
  multiplicity : E → ℝ
  multiplicity_hypotheses :
    Poincare.SimonGMT.Chapter03.IsLocallyIntegrableMultiplicity
      n carrier multiplicity
  tangent : E → Submodule ℝ E
  approximate_tangent : ∀ᵐ x
    ∂(MeasureTheory.Measure.euclideanHausdorffMeasure n).restrict carrier,
      Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt
        n carrier x (tangent x)
  tangentProjection_aemeasurable : AEMeasurable
      (fun x ↦ (tangent x).starProjection)
      (MeasureTheory.Measure.euclideanHausdorffMeasure n |>.withDensity
        (carrier.indicator fun x ↦ ENNReal.ofReal (multiplicity x)))
  locallyFiniteWeight : MeasureTheory.IsLocallyFiniteMeasure
    (MeasureTheory.Measure.euclideanHausdorffMeasure n |>.withDensity
      (carrier.indicator fun x ↦ ENNReal.ofReal (multiplicity x)))

namespace RectifiableVarifold

variable {n : ℕ} (V : RectifiableVarifold (E := E) n)

/-- Simon (4.1.1): `μ_V = θ ℓ H^n` (with `θ=0` off the carrier). -/
def weight : MeasureTheory.Measure E :=
  MeasureTheory.Measure.euclideanHausdorffMeasure n |>.withDensity
    (V.carrier.indicator fun x ↦ ENNReal.ofReal (V.multiplicity x))

/-- The local-finiteness hypothesis in the definition of a rectifiable
varifold makes its weight finite on compact sets. -/
instance weight.instIsLocallyFiniteMeasure :
    MeasureTheory.IsLocallyFiniteMeasure V.weight :=
  V.locallyFiniteWeight

/-- The chosen tangent projection is measurable for the concrete weight
measure. -/
theorem tangentProjection_aemeasurable_weight :
    AEMeasurable (fun x ↦ (V.tangent x).starProjection) V.weight :=
  V.tangentProjection_aemeasurable

/-- The density defining the weight is measurable modulo Euclidean Hausdorff
null sets. This follows from the multiplicity hypotheses on the carrier and
the zero extension off it. -/
theorem weightDensity_aemeasurable :
    AEMeasurable
      (V.carrier.indicator fun x ↦ ENNReal.ofReal (V.multiplicity x))
      (MeasureTheory.Measure.euclideanHausdorffMeasure n) := by
  rw [aemeasurable_indicator_iff V.measurable_carrier]
  exact ENNReal.measurable_ofReal.comp_aemeasurable
    V.multiplicity_hypotheses.aemeasurable

/-- An almost-everywhere statement for Hausdorff measure restricted to the
carrier also holds almost everywhere for the varifold weight. -/
theorem ae_weight_of_ae_restrict {p : E → Prop}
    (hp : ∀ᵐ x
      ∂(MeasureTheory.Measure.euclideanHausdorffMeasure n).restrict V.carrier,
        p x) :
    ∀ᵐ x ∂V.weight, p x := by
  rw [weight, MeasureTheory.ae_withDensity_iff' V.weightDensity_aemeasurable]
  rw [MeasureTheory.ae_restrict_iff' V.measurable_carrier] at hp
  filter_upwards [hp] with x hx hdensity
  apply hx
  by_contra hxc
  simp [hxc] at hdensity

/-- The approximate tangent plane has the declared dimension almost
everywhere for the varifold weight. -/
theorem tangent_finrank_ae_weight :
    ∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangent x) = n := by
  apply V.ae_weight_of_ae_restrict
  filter_upwards [V.approximate_tangent] with x hx
  exact hx.finrank_eq

/-- Any other almost-everywhere approximate-tangent representative agrees
with the chosen tangent field almost everywhere for the varifold weight.
Thus all weight integrals formed from the tangent plane are independent of
this representative. -/
theorem tangentField_ae_eq_weight (Q : E → Submodule ℝ E)
    (hQ : ∀ᵐ x
      ∂(MeasureTheory.Measure.euclideanHausdorffMeasure n).restrict V.carrier,
        Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt
          n V.carrier x (Q x)) :
    Q =ᵐ[V.weight] V.tangent := by
  have heq := Poincare.SimonGMT.Chapter03.approximateTangentField_ae_eq
    hQ V.approximate_tangent
  change ∀ᵐ x ∂V.weight, Q x = V.tangent x
  rw [weight, MeasureTheory.ae_withDensity_iff' V.weightDensity_aemeasurable]
  change ∀ᵐ x
    ∂(MeasureTheory.Measure.euclideanHausdorffMeasure n).restrict V.carrier,
      Q x = V.tangent x at heq
  rw [MeasureTheory.ae_restrict_iff' V.measurable_carrier] at heq
  filter_upwards [heq] with x hx hdensity
  apply hx
  by_contra hxc
  simp [hxc] at hdensity

/-- Simon (4.1.2): the mass is the weight measure of the whole ambient space. -/
def mass : ℝ≥0∞ := V.weight univ

/-- Simon (4.1.3): notation for the tangent space of a rectifiable varifold. -/
abbrev tangentAt (x : E) : Submodule ℝ E := V.tangent x

/-- Simon (4.1.4): support of a varifold is support of its weight measure. -/
def support : Set E := V.weight.support

/-- Simon (4.1.5), on weight measures: restriction of `V` to a measurable set. -/
def restrictedWeight (A : Set E) : MeasureTheory.Measure E := V.weight.restrict A

/-- The weight formula in Simon (4.1.1), evaluated on a measurable set. -/
theorem weight_apply {A : Set E} (hA : MeasurableSet A) :
    V.weight A = ∫⁻ x in A,
      V.carrier.indicator (fun x ↦ ENNReal.ofReal (V.multiplicity x)) x
      ∂MeasureTheory.Measure.euclideanHausdorffMeasure n := by
  rw [weight, MeasureTheory.withDensity_apply _ hA]

/-- The integral form of Simon's mass identity (4.1.2). -/
theorem mass_eq_lintegral :
    V.mass = ∫⁻ x,
      V.carrier.indicator (fun x ↦ ENNReal.ofReal (V.multiplicity x)) x
      ∂MeasureTheory.Measure.euclideanHausdorffMeasure n := by
  rw [mass, weight_apply V MeasurableSet.univ, MeasureTheory.setLIntegral_univ]

/-- Evaluation of Simon's restriction (4.1.5). -/
theorem restrictedWeight_apply {A B : Set E} (hB : MeasurableSet B) :
    V.restrictedWeight A B = V.weight (B ∩ A) := by
  rw [restrictedWeight, MeasureTheory.Measure.restrict_apply hB]

/-- The measure underlying the image construction (4.1.6)--(4.1.8).

`J` is the tangential Jacobian.  The Jacobian factor is essential: the image
weight is the pushforward of `J · μ_V`, not merely the pushforward of `μ_V`. -/
def pushforwardWeight (f : E → E) (J : E → ℝ≥0∞) : MeasureTheory.Measure E :=
  MeasureTheory.Measure.map f (V.weight.withDensity J)

/-- Simon (4.1.7), in measure form, for a measurable image set. -/
theorem pushforwardWeight_apply (f : E → E) (J : E → ℝ≥0∞)
    (hf : Measurable f) {A : Set E}
    (hA : MeasurableSet A) :
    V.pushforwardWeight f J A = ∫⁻ x in f ⁻¹' A, J x ∂V.weight := by
  rw [pushforwardWeight, MeasureTheory.Measure.map_apply hf hA,
    MeasureTheory.withDensity_apply _ (hA.preimage hf)]

/-- Simon (4.1.8): mass of the pushed-forward weight equals the integral of
the tangential Jacobian. -/
theorem pushforwardWeight_mass (f : E → E) (J : E → ℝ≥0∞)
    (hf : Measurable f) :
    V.pushforwardWeight f J univ = ∫⁻ x, J x ∂V.weight := by
  rw [pushforwardWeight_apply V f J hf MeasurableSet.univ, preimage_univ,
    MeasureTheory.setLIntegral_univ]

end RectifiableVarifold

/-- Simon (4.3.13): superlevel sets of a globally upper-semicontinuous density
are closed. -/
theorem isClosed_density_superlevel {X : Type*} [TopologicalSpace X]
    {density : X → ℝ} (h : UpperSemicontinuous density) (α : ℝ) :
    IsClosed {x | α ≤ density x} := by
  change IsClosed (density ⁻¹' Ici α)
  exact h.isClosed_preimage α

/-- Simon Lemma (4.4.11), in Mathlib's standard layer-cake form.  This is the
Fubini identity used by Simon; his power and logarithmic formulas follow by
choosing the one-variable integrand and restricting to `Ioi t₀`. -/
theorem layerCake_meas_lt {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) {f : X → ℝ}
    (hf0 : 0 ≤ᵐ[μ] f) (hf : AEMeasurable f μ) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ =
      ∫⁻ t in Ioi (0 : ℝ), μ {x | t < f x} :=
  MeasureTheory.lintegral_eq_lintegral_meas_lt μ hf0 hf

end

end Poincare.SimonGMT.Chapter04
