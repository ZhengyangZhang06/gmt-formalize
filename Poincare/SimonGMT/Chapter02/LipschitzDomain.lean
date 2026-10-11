module

public import Poincare.SimonGMT.Chapter02.Lipschitz

public section

/-!
# Simon GMT, Chapter 2, Definition 1.11: Lipschitz domains

This module records the complete uniform local-chart definition used by Simon.
The chart direction is a unit vector, its horizontal variables lie in the
orthogonal slice, and the domain and its boundary are respectively the strict
hypograph and graph of one Lipschitz function inside a uniform cylinder.
-/

open Bornology Set
open scoped NNReal Topology

namespace Poincare.SimonGMT.Chapter02

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The radius-`σ` horizontal slice orthogonal to a chart direction `v`. -/
def orthogonalSlice (v : E) (σ : ℝ) : Set E :=
  Metric.ball 0 σ ∩ {x | inner ℝ x v = 0}

/-- Simon's coordinate cylinder `U_y` around a boundary point. -/
def lipschitzCoordinateCylinder (y v : E) (σ τ : ℝ) : Set E :=
  {z | ∃ (x : orthogonalSlice v σ) (t : ℝ),
    -τ < t ∧ t < τ ∧ z = y + (x : E) + t • v}

/-- The strict hypograph of `u` in Simon's coordinate cylinder. -/
def lipschitzChartHypograph (y v : E) {σ τ : ℝ}
    (u : orthogonalSlice v σ → ℝ) : Set E :=
  {z | ∃ (x : orthogonalSlice v σ) (t : ℝ),
    -τ < t ∧ t < u x ∧ z = y + (x : E) + t • v}

/-- The graph of `u` in Simon's coordinates. -/
def lipschitzChartGraph (y v : E) {σ : ℝ}
    (u : orthogonalSlice v σ → ℝ) : Set E :=
  {z | ∃ x : orthogonalSlice v σ,
    z = y + (x : E) + u x • v}

/-- The local data at one boundary point in Simon Definition 1.11. -/
def IsLipschitzBoundaryChart (Ω : Set E) (σ τ : ℝ) (y : E) : Prop :=
  ∃ v : E, ‖v‖ = 1 ∧
    ∃ (K : ℝ≥0) (u : orthogonalSlice v σ → ℝ),
      LipschitzWith K u ∧
      (∀ x, u x ∈ Ioo (-τ) τ) ∧
      lipschitzCoordinateCylinder y v σ τ ∩ Ω =
        lipschitzChartHypograph y v (τ := τ) u ∧
      lipschitzCoordinateCylinder y v σ τ ∩ frontier Ω =
        lipschitzChartGraph y v u

/-- Simon Definition 1.11.  The same positive radii `σ ≤ τ` work at every
boundary point, while the unit direction and graph function may depend on the
point. -/
def IsLipschitzDomain (Ω : Set E) : Prop :=
  IsBounded Ω ∧ IsOpen Ω ∧
    ∃ σ τ : ℝ, 0 < σ ∧ σ ≤ τ ∧
      ∀ y ∈ frontier Ω, IsLipschitzBoundaryChart Ω σ τ y

/-- A Lipschitz domain is open, as required explicitly in Definition 1.11. -/
theorem IsLipschitzDomain.isOpen { Ω : Set E } (hΩ : IsLipschitzDomain Ω) :
    IsOpen Ω :=
  hΩ.2.1

/-- A Lipschitz domain is bounded, as required explicitly in Definition 1.11. -/
theorem IsLipschitzDomain.isBounded { Ω : Set E } (hΩ : IsLipschitzDomain Ω) :
    IsBounded Ω :=
  hΩ.1

/-- The uniform local chart supplied at every boundary point. -/
theorem IsLipschitzDomain.exists_uniform_boundary_charts { Ω : Set E }
    (hΩ : IsLipschitzDomain Ω) :
    ∃ σ τ : ℝ, 0 < σ ∧ σ ≤ τ ∧
      ∀ y ∈ frontier Ω, IsLipschitzBoundaryChart Ω σ τ y :=
  hΩ.2.2

end Poincare.SimonGMT.Chapter02
