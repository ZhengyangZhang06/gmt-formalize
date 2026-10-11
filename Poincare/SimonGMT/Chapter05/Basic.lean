module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Poincare.SimonGMT.Chapter04.Basic

@[expose] public section

/-!
# Simon GMT, Chapter 5: analytic foundations for Allard regularity

This module formalizes the concrete area integrand from §1, the harmonic
objects used in §1 and §3, and the scale-invariant tilt-excess of §4.  The
compactness, Lipschitz approximation, excess-decay, and Allard regularity
theorems require substantial GMT/PDE infrastructure not currently in Mathlib;
they are deliberately not introduced as axioms.
-/

open Filter Function Set
open scoped ENNReal MeasureTheory RealInnerProductSpace Topology

namespace Poincare.SimonGMT.Chapter05

noncomputable section

universe u v

/-! ## §1: the area functional of a graph -/

/-- The Gram matrix `δᵢⱼ + Dᵢu · Dⱼu` in Simon Chapter 5, §1. -/
def graphGram {n ℓ : ℕ} (P : Fin n → EuclideanSpace ℝ (Fin ℓ)) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ (1 : Matrix (Fin n) (Fin n) ℝ) i j + inner ℝ (P i) (P j)

/-- The graph Jacobian `sqrt (det (δᵢⱼ + Pᵢ·Pⱼ))` appearing before (5.1.1). -/
def graphAreaIntegrand {n ℓ : ℕ}
    (P : Fin n → EuclideanSpace ℝ (Fin ℓ)) : ℝ :=
  Real.sqrt (Matrix.det (graphGram P))

/-- Squared Frobenius norm of the derivative matrix in (5.1.1). -/
def frobeniusSq {n ℓ : ℕ}
    (P : Fin n → EuclideanSpace ℝ (Fin ℓ)) : ℝ :=
  ∑ i, ‖P i‖ ^ 2

/-- The exact Taylor remainder `F(P)` isolated in Simon (5.1.1). -/
def areaRemainder {n ℓ : ℕ}
    (P : Fin n → EuclideanSpace ℝ (Fin ℓ)) : ℝ :=
  graphAreaIntegrand P - 1 - (1 / 2 : ℝ) * frobeniusSq P

/-- The flat graph has Gram matrix equal to the identity. -/
@[simp] theorem graphGram_zero {n ℓ : ℕ} :
    graphGram (0 : Fin n → EuclideanSpace ℝ (Fin ℓ)) = 1 := by
  ext i j
  simp [graphGram]

/-- Normalization of the graph area integrand at the zero matrix. -/
@[simp] theorem graphAreaIntegrand_zero {n ℓ : ℕ} :
    graphAreaIntegrand (0 : Fin n → EuclideanSpace ℝ (Fin ℓ)) = 1 := by
  simp [graphAreaIntegrand]

/-- The remainder in Simon (5.1.1) vanishes at the flat plane. -/
@[simp] theorem areaRemainder_zero {n ℓ : ℕ} :
    areaRemainder (0 : Fin n → EuclideanSpace ℝ (Fin ℓ)) = 0 := by
  simp [areaRemainder, frobeniusSq]

/-- Simon (5.1.1): the graph area functional, written with Mathlib's Bochner
integral and the exact determinant integrand above. -/
def graphArea {n ℓ : ℕ} (center : EuclideanSpace ℝ (Fin n)) (radius : ℝ)
    (Du : EuclideanSpace ℝ (Fin n) → Fin n → EuclideanSpace ℝ (Fin ℓ)) : ℝ :=
  ∫ x in Metric.ball center radius, graphAreaIntegrand (Du x)
    ∂MeasureTheory.Measure.euclideanHausdorffMeasure n

/-- The elementary Cauchy--Young inequality used in the proof of Simon (5.1.5). -/
theorem two_mul_le_sq_add_sq (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-! ## §3: harmonic approximation vocabulary -/

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Simon §3 uses harmonic maps componentwise.  Mathlib's predicate is already
vector-valued, so no coordinate encoding is needed. -/
abbrev HarmonicOn (u : E → F) (s : Set E) : Prop :=
  InnerProductSpace.HarmonicOnNhd u s

/-- Constant maps are harmonic, a base case used throughout the affine
approximation argument. -/
theorem harmonicOn_const (c : F) (s : Set E) :
    HarmonicOn (fun _ : E ↦ c) s :=
  InnerProductSpace.harmonicOnNhd_const c

/-- Harmonic maps are closed under addition. -/
theorem HarmonicOn.add {u v : E → F} {s : Set E}
    (hu : HarmonicOn u s) (hv : HarmonicOn v s) :
    HarmonicOn (u + v) s :=
  InnerProductSpace.HarmonicOnNhd.add hu hv

/-- Harmonic maps are closed under real scalar multiplication. -/
theorem HarmonicOn.smul {u : E → F} {s : Set E}
    (hu : HarmonicOn u s) (c : ℝ) :
    HarmonicOn (c • u) s :=
  hu.const_smul

/-- Every harmonic map in Mathlib's sense is continuous on its domain. -/
theorem HarmonicOn.continuousOn {u : E → F} {s : Set E}
    (hu : HarmonicOn u s) : ContinuousOn u s :=
  InnerProductSpace.HarmonicOnNhd.continuousOn hu

/-! ## §4: tilt excess -/

variable [MeasurableSpace E]

/-- Simon (5.4.1): unnormalised squared tilt against a fixed plane projection.
The projection field is explicit because Chapter 3's approximate-tangent
construction is a separate dependency. -/
def tiltEnergy (proj : E → E →L[ℝ] E) (target : E →L[ℝ] E)
    (μ : MeasureTheory.Measure E) (center : E) (radius : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Metric.ball center radius,
    ENNReal.ofReal (‖proj x - target‖ ^ 2) ∂μ

/-- The tilt energy is nonnegative (as an extended nonnegative real). -/
theorem tiltEnergy_nonneg (proj : E → E →L[ℝ] E) (target : E →L[ℝ] E)
    (μ : MeasureTheory.Measure E) (center : E) (radius : ℝ) :
    0 ≤ tiltEnergy proj target μ center radius :=
  bot_le

/-- The tilt energy vanishes identically when the tangent projection field is
the target projection. -/
@[simp] theorem tiltEnergy_const_target (target : E →L[ℝ] E)
    (μ : MeasureTheory.Measure E) (center : E) (radius : ℝ) :
    tiltEnergy (fun _ ↦ target) target μ center radius = 0 := by
  simp [tiltEnergy]

/-- Simon's scale-normalised tilt excess (5.4.1), without the harmless factor
`ρ⁻ⁿ` being hidden in notation. -/
def tiltExcess (n : ℕ) (proj : E → E →L[ℝ] E) (target : E →L[ℝ] E)
    (μ : MeasureTheory.Measure E) (center : E) (radius : ℝ) : ℝ≥0∞ :=
  tiltEnergy proj target μ center radius / ENNReal.ofReal (radius ^ n)

@[simp] theorem tiltExcess_const_target (n : ℕ) (target : E →L[ℝ] E)
    (μ : MeasureTheory.Measure E) (center : E) (radius : ℝ) :
    tiltExcess n (fun _ ↦ target) target μ center radius = 0 := by
  simp [tiltExcess]

end

end Poincare.SimonGMT.Chapter05
