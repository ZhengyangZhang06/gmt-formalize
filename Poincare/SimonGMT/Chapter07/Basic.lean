module

public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Topology.Basic
public import Poincare.SimonGMT.Chapter06.Currents

@[expose] public section

/-!
# Simon GMT, Chapter 7, §1: minimizing currents

This file records the variational content of Definition 1.1 and the complete
inequality argument in Lemma 1.4.  The current type is a parameter: this keeps
the statement usable by a concrete current construction while making every
algebraic and local-finiteness hypothesis explicit.

Source: `Simon-gmt new.pdf`, printed pp. 181--183.
-/

open scoped ENNReal
open Set

namespace Poincare.SimonGMT.Chapter07

universe u v w

/-- `W ⋐ U`: the closure of `W` is a compact subset of `U`. -/
def CompactlyContained [TopologicalSpace X] (W U : Set X) : Prop :=
  IsCompact (closure W) ∧ closure W ⊆ U

/-- An admissible compactly supported cycle used to perturb a current.

This is the cycle formulation of the competitors in Simon's Definition 1.1:
if the competitor is `T + X`, then equality of boundaries is `∂X = 0` and
the support condition is imposed on `X`. -/
def AdmissibleVariation [TopologicalSpace X] [AddCommGroup C] [AddCommGroup B]
    (boundary : C →+ B) (support : C → Set X) (integerMultiplicity : C → Prop)
    (A W : Set X) (X₀ : C) : Prop :=
  integerMultiplicity X₀ ∧ boundary X₀ = 0 ∧
    IsCompact (support X₀) ∧ support X₀ ⊆ A ∩ W

/-- A competitor `S` for `T` in Simon 7.1.1. -/
def IsCompetitor [TopologicalSpace X] [AddCommGroup C] [AddCommGroup B]
    (boundary : C →+ B) (support : C → Set X) (integerMultiplicity : C → Prop)
    (A W : Set X) (T S : C) : Prop :=
  integerMultiplicity S ∧ boundary S = boundary T ∧
    IsCompact (support (S - T)) ∧ support (S - T) ⊆ A ∩ W

/-- Simon 7.1.1 in its source presentation: `M_W(T) ≤ M_W(S)` whenever
`W ⋐ U`, `∂S = ∂T`, and `spt(S-T)` is a compact subset of `A ∩ W`.

`massOn W T` denotes `M_W(T)`. -/
def MinimizingIn [TopologicalSpace X] [AddCommGroup C] [AddCommGroup B]
    (boundary : C →+ B) (support : C → Set X) (integerMultiplicity : C → Prop)
    (massOn : Set X → C → ℝ≥0∞) (U A : Set X) (T : C) : Prop :=
  integerMultiplicity T ∧
    ∀ {W : Set X}, IsOpen W → CompactlyContained W U →
      ∀ S, IsCompetitor boundary support integerMultiplicity A W T S →
        massOn W T ≤ massOn W S

/-- The compactly-supported-cycle formulation of Definition 7.1.1. -/
def MinimizingByCycles [TopologicalSpace X] [AddCommGroup C] [AddCommGroup B]
    (boundary : C →+ B) (support : C → Set X) (integerMultiplicity : C → Prop)
    (massOn : Set X → C → ℝ≥0∞) (U A : Set X) (T : C) : Prop :=
  integerMultiplicity T ∧
    ∀ {W : Set X}, IsOpen W → CompactlyContained W U →
      ∀ X₀, AdmissibleVariation boundary support integerMultiplicity A W X₀ →
        massOn W T ≤ massOn W (T + X₀)

theorem minimizingIn_iff [TopologicalSpace X] [AddCommGroup C] [AddCommGroup B]
    {boundary : C →+ B} {support : C → Set X} {integerMultiplicity : C → Prop}
    {massOn : Set X → C → ℝ≥0∞} {U A : Set X} {T : C} :
    MinimizingIn boundary support integerMultiplicity massOn U A T ↔
      integerMultiplicity T ∧
        ∀ {W : Set X}, IsOpen W → CompactlyContained W U →
          ∀ S, IsCompetitor boundary support integerMultiplicity A W T S →
            massOn W T ≤ massOn W S :=
  Iff.rfl

/-- Candidate and cycle formulations of Simon 7.1.1 agree when integer
multiplicity is closed under addition and negation. -/
theorem minimizingIn_iff_minimizingByCycles [TopologicalSpace X] [AddCommGroup C]
    [AddCommGroup B]
    {boundary : C →+ B} {support : C → Set X} {integerMultiplicity : C → Prop}
    {massOn : Set X → C → ℝ≥0∞} {U A : Set X} {T : C}
    (integer_add : ∀ {R S}, integerMultiplicity R → integerMultiplicity S →
      integerMultiplicity (R + S))
    (integer_neg : ∀ {R}, integerMultiplicity R → integerMultiplicity (-R)) :
    MinimizingIn boundary support integerMultiplicity massOn U A T ↔
      MinimizingByCycles boundary support integerMultiplicity massOn U A T := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro W hWopen hWU X hX
    apply h.2 hWopen hWU (T + X)
    refine ⟨integer_add h.1 hX.1, ?_, ?_, ?_⟩
    · simp [hX.2.1]
    · simpa using hX.2.2.1
    · simpa using hX.2.2.2
  · intro h
    refine ⟨h.1, ?_⟩
    intro W hWopen hWU S hS
    have hST : integerMultiplicity (S - T) := by
      simpa [sub_eq_add_neg] using integer_add hS.1 (integer_neg h.1)
    have hvar : AdmissibleVariation boundary support integerMultiplicity A W (S - T) := by
      refine ⟨hST, ?_, hS.2.2.1, hS.2.2.2⟩
      simp [hS.2.1]
    simpa using h.2 hWopen hWU (S - T) hvar

/-- Algebraic cycle-form adapter for Simon 7.1.4: a mass-additive decomposition
of a minimizing current has minimizing summands.  Instantiation with the
concrete current construction is a separate obligation.

The proof is exactly Simon's chain
`M(T₁)+M(T₂) ≤ M(T₁+X)+M(T₂)` followed by cancellation.  Local
finiteness is stated as `massOn W Tᵢ ≠ ∞`, the precise condition needed
for cancellation in `ℝ≥0∞`. -/
theorem minimizing_summands [TopologicalSpace X] [AddCommGroup C] [AddCommGroup B]
    {boundary : C →+ B} {support : C → Set X} {integerMultiplicity : C → Prop}
    {massOn : Set X → C → ℝ≥0∞} {U A : Set X} {T₁ T₂ : C}
    (hT₁ : integerMultiplicity T₁) (hT₂ : integerMultiplicity T₂)
    (hmin : MinimizingByCycles boundary support integerMultiplicity massOn U A (T₁ + T₂))
    (hadd : ∀ W, massOn W (T₁ + T₂) = massOn W T₁ + massOn W T₂)
    (htriangle : ∀ W R S, massOn W (R + S) ≤ massOn W R + massOn W S)
    (hfinite₁ : ∀ {W : Set X}, CompactlyContained W U → massOn W T₁ ≠ ∞)
    (hfinite₂ : ∀ {W : Set X}, CompactlyContained W U → massOn W T₂ ≠ ∞) :
    MinimizingByCycles boundary support integerMultiplicity massOn U A T₁ ∧
      MinimizingByCycles boundary support integerMultiplicity massOn U A T₂ := by
  constructor
  · refine ⟨hT₁, ?_⟩
    intro W hWopen hWU X hX
    have hmin' := hmin.2 hWopen hWU X hX
    have hchain : massOn W T₁ + massOn W T₂ ≤
        massOn W (T₁ + X) + massOn W T₂ := by
      calc
        massOn W T₁ + massOn W T₂ = massOn W (T₁ + T₂) := (hadd W).symm
        _ ≤ massOn W ((T₁ + T₂) + X) := hmin'
        _ = massOn W ((T₁ + X) + T₂) := by rw [add_assoc, add_comm T₂ X, ← add_assoc]
        _ ≤ massOn W (T₁ + X) + massOn W T₂ := htriangle W _ _
    exact (ENNReal.add_le_add_iff_right (hfinite₂ hWU)).mp hchain
  · refine ⟨hT₂, ?_⟩
    intro W hWopen hWU X hX
    have hmin' := hmin.2 hWopen hWU X hX
    have hchain : massOn W T₂ + massOn W T₁ ≤
        massOn W (T₂ + X) + massOn W T₁ := by
      calc
        massOn W T₂ + massOn W T₁ = massOn W (T₁ + T₂) := by rw [hadd, add_comm]
        _ ≤ massOn W ((T₁ + T₂) + X) := hmin'
        _ = massOn W ((T₂ + X) + T₁) := by ac_rfl
        _ ≤ massOn W (T₂ + X) + massOn W T₁ := htriangle W _ _
    exact (ENNReal.add_le_add_iff_right (hfinite₁ hWU)).mp hchain

/-- Algebraic core of Simon 7.1.4 in the source's candidate-current
formulation.  All facts about integer currents and localized mass used in the
printed proof are visible hypotheses here; instantiation with concrete
currents remains a separate obligation. -/
theorem minimizing_summands_source [TopologicalSpace X] [AddCommGroup C]
    [AddCommGroup B]
    {boundary : C →+ B} {support : C → Set X} {integerMultiplicity : C → Prop}
    {massOn : Set X → C → ℝ≥0∞} {U A : Set X} {T₁ T₂ : C}
    (hT₁ : integerMultiplicity T₁) (hT₂ : integerMultiplicity T₂)
    (integer_add : ∀ {R S}, integerMultiplicity R → integerMultiplicity S →
      integerMultiplicity (R + S))
    (hmin : MinimizingIn boundary support integerMultiplicity massOn U A (T₁ + T₂))
    (hadd : ∀ W, massOn W (T₁ + T₂) = massOn W T₁ + massOn W T₂)
    (htriangle : ∀ W R S, massOn W (R + S) ≤ massOn W R + massOn W S)
    (hfinite₁ : ∀ {W : Set X}, CompactlyContained W U → massOn W T₁ ≠ ∞)
    (hfinite₂ : ∀ {W : Set X}, CompactlyContained W U → massOn W T₂ ≠ ∞) :
    MinimizingIn boundary support integerMultiplicity massOn U A T₁ ∧
      MinimizingIn boundary support integerMultiplicity massOn U A T₂ := by
  constructor
  · refine ⟨hT₁, ?_⟩
    intro W hWopen hWU S hS
    have hdiff : (S + T₂) - (T₁ + T₂) = S - T₁ := by abel
    have hcomp : IsCompetitor boundary support integerMultiplicity A W
        (T₁ + T₂) (S + T₂) := by
      refine ⟨integer_add hS.1 hT₂, ?_, ?_, ?_⟩
      · simp [hS.2.1]
      · rw [hdiff]
        exact hS.2.2.1
      · rw [hdiff]
        exact hS.2.2.2
    have hminimal := hmin.2 hWopen hWU (S + T₂) hcomp
    have hchain : massOn W T₁ + massOn W T₂ ≤ massOn W S + massOn W T₂ := by
      calc
        massOn W T₁ + massOn W T₂ = massOn W (T₁ + T₂) := (hadd W).symm
        _ ≤ massOn W (S + T₂) := hminimal
        _ ≤ massOn W S + massOn W T₂ := htriangle W _ _
    exact (ENNReal.add_le_add_iff_right (hfinite₂ hWU)).mp hchain
  · refine ⟨hT₂, ?_⟩
    intro W hWopen hWU S hS
    have hdiff : (T₁ + S) - (T₁ + T₂) = S - T₂ := by abel
    have hcomp : IsCompetitor boundary support integerMultiplicity A W
        (T₁ + T₂) (T₁ + S) := by
      refine ⟨integer_add hT₁ hS.1, ?_, ?_, ?_⟩
      · simp [hS.2.1]
      · rw [hdiff]
        exact hS.2.2.1
      · rw [hdiff]
        exact hS.2.2.2
    have hminimal := hmin.2 hWopen hWU (T₁ + S) hcomp
    have hchain : massOn W T₂ + massOn W T₁ ≤ massOn W S + massOn W T₁ := by
      calc
        massOn W T₂ + massOn W T₁ = massOn W (T₁ + T₂) := by rw [hadd, add_comm]
        _ ≤ massOn W (T₁ + S) := hminimal
        _ ≤ massOn W T₁ + massOn W S := htriangle W _ _
        _ = massOn W S + massOn W T₁ := add_comm _ _
    exact (ENNReal.add_le_add_iff_right (hfinite₁ hWU)).mp hchain

/-! ### Integration with the current layer from Chapter 6 -/

open Poincare.SimonGMT.Chapter06

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- An algebraic current represented by the integer-rectifiable data of
Chapter 6.  Chapter 6 still owes the continuity estimate turning every such
action into a `GeometricCurrent`; the name here makes that limitation explicit. -/
def IsAlgebraicIntegerMultiplicityCurrent (n : ℕ) (T : Current E n) : Prop :=
  ∃ D : IntegerRectifiableCurrentData (F := E) n,
    ∀ omega : TestForm E n,
      T omega = D.action (omega : DifferentialForm E n)

/-- The genuine degree-changing boundary homomorphism on the algebraic current
layer, `C_{n+1} → C_n`. -/
noncomputable def algebraicCurrentBoundaryHom (n : ℕ) : Current E (n + 1) →+ Current E n where
  toFun := Current.boundary
  map_zero' := Current.boundary_zero n
  map_add' := Current.boundary_add

/-- Definition 7.1.1 instantiated with Chapter 6's algebraic currents,
degree-changing boundary, current support, and local mass.  This is a concrete
prerequisite rather than full source credit because `Current` does not yet
carry Simon's test-form-topology continuity. -/
noncomputable def AlgebraicCurrentMinimizingIn (n : ℕ) (U A : Set E)
    (T : Current E (n + 1)) : Prop :=
  MinimizingIn (algebraicCurrentBoundaryHom (E := E) n) Current.support
    (IsAlgebraicIntegerMultiplicityCurrent (E := E) (n + 1))
    (fun W R ↦ R.massOn W) U A T

end Poincare.SimonGMT.Chapter07
