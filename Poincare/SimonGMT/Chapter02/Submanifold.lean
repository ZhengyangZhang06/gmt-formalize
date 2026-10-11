module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Poincare.SimonGMT.Chapter02.Area

public section

/-!
# Simon GMT, Chapter 2, §4: Euclidean submanifolds

The definitions below preserve Simon's local parametrization model.  In
particular, relative properness is not discarded: compact subsets of the
ambient chart have compact preimage inside the parameter domain.
-/

open Function Module Set
open scoped ENNReal

namespace Poincare.SimonGMT.Chapter02

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Relative properness of a parametrization `φ : V → W`, in the precise
sense used in Simon's definition preceding (4.1). -/
def IsProperOnInto (φ : E → F) (V : Set E) (W : Set F) : Prop :=
  ∀ K : Set F, IsCompact K → K ⊆ W → IsCompact (V ∩ φ ⁻¹' K)

/-- The local representation in Simon (4.1): `φ` is a one-to-one `C^r`
parametrization of exactly `M ∩ W`, proper relative to the two chart sets,
and has maximal rank everywhere on `V`.  Maximal rank is expressed as
injectivity because the parameter space is the `n`-dimensional source. -/
def IsSimonLocalRepresentation (r : ℕ∞) (M : Set F)
    (V : Set E) (W : Set F) (φ : E → F) : Prop :=
  IsOpen V ∧ IsOpen W ∧
    ContDiffOn ℝ r φ V ∧
    InjOn φ V ∧
    φ '' V = W ∩ M ∧
    IsProperOnInto φ V W ∧
    ∀ x ∈ V, Injective (fderiv ℝ φ x)

/-- Simon's definition of an `n`-dimensional `C^r` submanifold of an
ambient Euclidean space, with `E` playing the role of `ℝ^n`. -/
def IsSimonSubmanifold (r : ℕ∞) (M : Set F) : Prop :=
  1 ≤ r ∧
    ∀ y ∈ M, ∃ (V : Set E) (W : Set F) (φ : E → F),
      y ∈ W ∧ IsSimonLocalRepresentation r M V W φ

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Extract the local parametrization promised by Simon's submanifold
definition.  Keeping this as an explicit public accessor lets downstream
geometric arguments use the witnesses without unfolding the definition. -/
theorem IsSimonSubmanifold.exists_localRepresentation {r : ℕ∞} {M : Set F}
    (h : IsSimonSubmanifold (E := E) r M) {y : F} (hy : y ∈ M) :
    ∃ (V : Set E) (W : Set F) (φ : E → F),
      y ∈ W ∧ IsSimonLocalRepresentation r M V W φ :=
  h.2 y hy

/-- The parameter domain of a Simon local representation is open. -/
theorem IsSimonLocalRepresentation.isOpen_source {r : ℕ∞} {M : Set F}
    {V : Set E} {W : Set F} {φ : E → F}
    (h : IsSimonLocalRepresentation r M V W φ) :
    IsOpen V :=
  h.1

/-- The ambient target chart of a Simon local representation is open. -/
theorem IsSimonLocalRepresentation.isOpen_target {r : ℕ∞} {M : Set F}
    {V : Set E} {W : Set F} {φ : E → F}
    (h : IsSimonLocalRepresentation r M V W φ) :
    IsOpen W :=
  h.2.1

/-- A Simon local representation has the stipulated smoothness on its
parameter domain. -/
theorem IsSimonLocalRepresentation.contDiffOn {r : ℕ∞} {M : Set F}
    {V : Set E} {W : Set F} {φ : E → F}
    (h : IsSimonLocalRepresentation r M V W φ) :
    ContDiffOn ℝ r φ V :=
  h.2.2.1

/-- The relative-properness field of a Simon local representation. -/
theorem IsSimonLocalRepresentation.isProperOnInto {r : ℕ∞} {M : Set F}
    {V : Set E} {W : Set F} {φ : E → F}
    (h : IsSimonLocalRepresentation r M V W φ) :
    IsProperOnInto φ V W :=
  h.2.2.2.2.2.1

/-- Compact-preimage consequence of the relative-properness field, exposed
for use by downstream modules. -/
theorem IsSimonLocalRepresentation.isCompact_source_inter_preimage
    {r : ℕ∞} {M : Set F} {V : Set E} {W : Set F} {φ : E → F}
    (h : IsSimonLocalRepresentation r M V W φ)
    (K : Set F) (hK : IsCompact K) (hKW : K ⊆ W) :
    IsCompact (V ∩ φ ⁻¹' K) :=
  h.2.2.2.2.2.1 K hK hKW

/-- A local representation has the image identity printed as Simon (4.1). -/
theorem IsSimonLocalRepresentation.image_eq {r : ℕ∞} {M : Set F}
    {V : Set E} {W : Set F} {φ : E → F}
    (h : IsSimonLocalRepresentation r M V W φ) :
    φ '' V = W ∩ M :=
  h.2.2.2.2.1

/-- A local representation is one-to-one on its parameter domain. -/
theorem IsSimonLocalRepresentation.injOn {r : ℕ∞} {M : Set F}
    {V : Set E} {W : Set F} {φ : E → F}
    (h : IsSimonLocalRepresentation r M V W φ) :
    InjOn φ V :=
  h.2.2.2.1

/-- The derivative of a Simon local representation has maximal rank. -/
theorem IsSimonLocalRepresentation.injective_fderiv {r : ℕ∞} {M : Set F}
    {V : Set E} {W : Set F} {φ : E → F}
    (h : IsSimonLocalRepresentation r M V W φ) {x : E} (hx : x ∈ V) :
    Injective (fderiv ℝ φ x) :=
  h.2.2.2.2.2.2 x hx

/-- The tangent space at the parameter point `x`, as the range of the
derivative of the local representation.  This is Simon's definition just
before (4.3). -/
noncomputable def parametrizedTangentSpace (φ : E → F) (x : E) :
    Submodule ℝ F :=
  LinearMap.range (fderiv ℝ φ x).toLinearMap

/-- Simon (4.3): the derivative images of any basis of the parameter space
form a basis of the tangent space.  For the standard basis of `ℝⁿ` these are
the printed vectors `D₁ φ(x), …, Dₙ φ(x)`. -/
theorem IsSimonLocalRepresentation.basis_parametrizedTangentSpace
    {ι : Type*} [Fintype ι] {r : ℕ∞} {M : Set F}
    {V : Set E} {W : Set F} {φ : E → F}
    (h : IsSimonLocalRepresentation r M V W φ) {x : E} (hx : x ∈ V)
    (b : Basis ι ℝ E) :
    ∃ bT : Basis ι ℝ (parametrizedTangentSpace φ x),
      ∀ i, ((bT i : parametrizedTangentSpace φ x) : F) =
        fderiv ℝ φ x (b i) := by
  let e : E ≃ₗ[ℝ] parametrizedTangentSpace φ x :=
    LinearEquiv.ofInjective (fderiv ℝ φ x).toLinearMap (h.injective_fderiv hx)
  refine ⟨b.map e, fun i ↦ ?_⟩
  rfl

end Poincare.SimonGMT.Chapter02
