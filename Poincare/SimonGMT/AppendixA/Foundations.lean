module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Topology.MetricSpace.HausdorffDimension

@[expose] public section

/-!
# Simon GMT, Appendix A: scaling and Hausdorff-dimension foundations

This file formalizes the concrete rescaling operation at the start of Appendix
A and the Hausdorff-measure interpretation of the dimension estimate in A.4.
It deliberately does not package A.4 itself as an assumed implication: its
dimension-reduction proof remains an open obligation.

Source: `Simon-gmt new.pdf`, printed pp. 225--228.
-/

open scoped ENNReal NNReal
open Set MeasureTheory Filter

namespace Poincare.SimonGMT.AppendixA

/-- Euclidean coordinate space used in Appendix A, with its Euclidean norm
rather than the sup norm on an unbundled finite function space. -/
abbrev Euclidean (P : ℕ) := EuclideanSpace ℝ (Fin P)

/-- `φ_{y,λ}(x) = φ(y + λx)`, the rescaling preceding A.1. -/
def rescale {P Q : ℕ} (phi : Euclidean P → Euclidean Q)
    (y : Euclidean P) (lambda : ℝ) : Euclidean P → Euclidean Q :=
  fun x ↦ phi (y + lambda • x)

@[simp] theorem rescale_zero_one {P Q : ℕ} (phi : Euclidean P → Euclidean Q) :
    rescale phi 0 1 = phi := by
  funext x
  simp [rescale]

/-- Composition law for translation/dilation blow-ups. -/
theorem rescale_rescale {P Q : ℕ} (phi : Euclidean P → Euclidean Q)
    (y z : Euclidean P) (lambda mu : ℝ) :
    rescale (rescale phi y lambda) z mu =
      rescale phi (y + lambda • z) (lambda * mu) := by
  funext x
  apply congrArg phi
  module

/-- Degree-zero homogeneity used in A.2 and throughout the proof of A.4. -/
def HomogeneousDegreeZero {P Q : ℕ} (phi : Euclidean P → Euclidean Q) : Prop :=
  ∀ lambda : ℝ, 0 < lambda → rescale phi 0 lambda = phi

/-- The singular-set transform in A.3(2), expressed without informal set
subtraction/scalar notation. -/
def rescaleSet {P : ℕ} (S : Set (Euclidean P)) (y : Euclidean P) (lambda : ℝ) :
    Set (Euclidean P) :=
  (fun x ↦ y + lambda • x) ⁻¹' S

@[simp] theorem mem_rescaleSet {P : ℕ} {S : Set (Euclidean P)}
    {y x : Euclidean P} {lambda : ℝ} :
    x ∈ rescaleSet S y lambda ↔ y + lambda • x ∈ S :=
  Iff.rfl

/-- A.3(2) automatically respects two successive rescalings. -/
theorem rescaleSet_rescaleSet {P : ℕ} (S : Set (Euclidean P))
    (y z : Euclidean P) (lambda mu : ℝ) :
    rescaleSet (rescaleSet S y lambda) z mu =
      rescaleSet S (y + lambda • z) (lambda * mu) := by
  ext x
  change y + lambda • (z + mu • x) ∈ S ↔
    y + lambda • z + (lambda * mu) • x ∈ S
  rw [show y + lambda • (z + mu • x) =
    y + lambda • z + (lambda * mu) • x by module]

/-- Weak convergence against compactly supported continuous test functions,
exactly as specified in the preamble to Appendix A. -/
def WeaklyConverges (n : ℕ) {P Q : ℕ}
    (phi : ℕ → Euclidean P → Euclidean Q) (limit : Euclidean P → Euclidean Q) : Prop :=
  ∀ f : Euclidean P → ℝ, Continuous f → HasCompactSupport f →
    Tendsto
      (fun k ↦ ∫ x, f x • phi k x ∂μH[(n : ℝ)]) atTop
      (nhds (∫ x, f x • limit x ∂μH[(n : ℝ)]))

/-- A constant-vector multiple of the indicator of an `n`-plane, the flat
objects singled out in A.3(1). -/
def IsPlaneIndicator (n : ℕ) {P Q : ℕ} (phi : Euclidean P → Euclidean Q) : Prop :=
  ∃ L : Submodule ℝ (Euclidean P), Module.finrank ℝ L = n ∧
    ∃ c : Euclidean Q, phi = Set.indicator (L : Set (Euclidean P)) (fun _ ↦ c)

/-- The open `ε`-neighborhood used in A.3(3), written existentially so that
the neighborhood of the empty set is itself empty.  This differs importantly
from Mathlib's convention `Metric.infDist x ∅ = 0`. -/
def openEpsilonNeighborhood {P : ℕ} (S : Set (Euclidean P)) (epsilon : ℝ) :
    Set (Euclidean P) :=
  {x | ∃ y ∈ S, dist x y < epsilon}

@[simp] theorem openEpsilonNeighborhood_empty {P : ℕ} (epsilon : ℝ) :
    openEpsilonNeighborhood (∅ : Set (Euclidean P)) epsilon = ∅ := by
  ext x
  simp [openEpsilonNeighborhood]

/-- The data and the three hypotheses A.1--A.3.  This structure only records
the source assumptions; it does not assume the conclusion of A.4. -/
structure DimensionReductionSystem (P n Q : ℕ) where
  family : Set (Euclidean P → Euclidean Q)
  singular : (Euclidean P → Euclidean Q) → Set (Euclidean P)
  locallyIntegrable : ∀ {phi}, phi ∈ family → ∀ j,
    LocallyIntegrable (fun x ↦ phi x j) μH[(n : ℝ)]
  /-- A.1: closure under the permitted translations and dilations. -/
  rescale_mem : ∀ {phi}, phi ∈ family → ∀ y lambda,
    ‖y‖ ≤ 1 - lambda → 0 < lambda → lambda < 1 →
      rescale phi y lambda ∈ family
  /-- A.2: subsequential homogeneous degree-zero tangent functions. -/
  exists_tangent : ∀ {phi}, phi ∈ family → ∀ {y}, ‖y‖ < 1 →
    ∀ lambda : ℕ → ℝ, (∀ k, 0 < lambda k) → StrictAnti lambda →
      Tendsto lambda atTop (nhds 0) →
      ∃ (subseq : ℕ → ℕ) (psi : Euclidean P → Euclidean Q),
        StrictMono subseq ∧ psi ∈ family ∧
          WeaklyConverges n (fun k ↦ rescale phi y (lambda (subseq k))) psi ∧
          HomogeneousDegreeZero psi
  singular_closed : ∀ {phi}, phi ∈ family → IsClosed (singular phi)
  /-- A.3(1). -/
  singular_planeIndicator : ∀ {phi}, phi ∈ family →
    IsPlaneIndicator n phi → singular phi = ∅
  /-- A.3(2). -/
  singular_rescale : ∀ {phi}, phi ∈ family → ∀ y lambda,
    ‖y‖ ≤ 1 - lambda → 0 < lambda → lambda < 1 →
      singular (rescale phi y lambda) = rescaleSet (singular phi) y lambda
  /-- A.3(3), upper semicontinuity of singular sets under weak convergence. -/
  singular_upperSemicontinuous : ∀ {phi}, phi ∈ family →
    ∀ seq : ℕ → Euclidean P → Euclidean Q, (∀ k, seq k ∈ family) →
      WeaklyConverges n seq phi → ∀ {epsilon : ℝ}, 0 < epsilon →
        ∃ k₀, ∀ k ≥ k₀,
          Metric.ball (0 : Euclidean P) 1 ∩ singular (seq k) ⊆
            openEpsilonNeighborhood (singular phi) epsilon

/-- The essential empty-limit consequence of A.3(3): if the limiting
singular set is empty, the approximating singular sets are eventually empty
inside the unit ball. -/
theorem DimensionReductionSystem.eventually_singular_empty_in_unitBall
    (D : DimensionReductionSystem P n Q) {phi : Euclidean P → Euclidean Q}
    (hphi : phi ∈ D.family) (seq : ℕ → Euclidean P → Euclidean Q)
    (hseq : ∀ k, seq k ∈ D.family) (hconv : WeaklyConverges n seq phi)
    (hempty : D.singular phi = ∅) :
    ∃ k₀, ∀ k ≥ k₀,
      Metric.ball (0 : Euclidean P) 1 ∩ D.singular (seq k) = ∅ := by
  obtain ⟨k₀, hk₀⟩ :=
    D.singular_upperSemicontinuous hphi seq hseq hconv (epsilon := 1) zero_lt_one
  refine ⟨k₀, fun k hk ↦ ?_⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hx' := hk₀ k hk hx
  simpa [hempty] using hx'

/-- The measure-theoretic reading of `dim S ≤ d` used parenthetically in
A.4: every strictly higher-dimensional Hausdorff measure vanishes. -/
theorem hausdorffMeasure_zero_above_dimH {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {S : Set X} {d alpha : ℝ≥0} (hdim : dimH S ≤ (d : ℝ≥0∞)) (halpha : 0 < alpha) :
    μH[(d + alpha : ℝ≥0)] S = 0 := by
  apply hausdorffMeasure_of_dimH_lt
  exact hdim.trans_lt (ENNReal.coe_lt_coe.2 (lt_add_of_pos_right d halpha))

/-- The final `d = 0` conclusion in A.4 is stronger than dimension zero; this
records the easy converse fact that finiteness itself forces dimension zero. -/
theorem finite_set_dimH_zero {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {S : Set X} (hS : S.Finite) : dimH S = 0 :=
  hS.dimH_zero

/-- Consequently every positive-dimensional Hausdorff measure of a finite
singular set vanishes. -/
theorem finite_set_hausdorffMeasure_zero {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {S : Set X} (hS : S.Finite) {alpha : ℝ≥0} (halpha : 0 < alpha) :
    μH[alpha] S = 0 := by
  apply hausdorffMeasure_of_dimH_lt
  simpa [hS.dimH_zero] using ENNReal.coe_pos.2 halpha

end Poincare.SimonGMT.AppendixA
