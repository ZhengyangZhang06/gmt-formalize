module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Poincare.SimonGMT.Chapter04.Basic
public import Poincare.SimonGMT.Chapter06.Forms

@[expose] public section

/-!
# Simon GMT, Chapter 6, §§2--3: currents and integer rectifiable currents

The test-form space is constructed as an actual real submodule of smooth,
compactly supported differential forms.  `Current` is the algebraic dual used
by the computational APIs.  `GeometricCurrent` adds Simon's sequential
continuity condition for the test-form topology.  This is enough to define the
boundary and prove `∂² = 0` without axioms.  The representation theorem and
Federer--Fleming compactness remain separate analytic obligations.
-/

open Filter Function Set
open scoped ContDiff ENNReal MeasureTheory Topology

namespace Poincare.SimonGMT.Chapter06

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The vector subspace `ᶟⁿ(E)` of smooth compactly supported `n`-forms. -/
def testFormSubmodule (n : ℕ) : Submodule ℝ (DifferentialForm E n) where
  carrier := IsTestForm
  zero_mem' := by
    change IsSmoothForm (0 : DifferentialForm E n) ∧
      HasCompactSupport (0 : DifferentialForm E n)
    constructor
    · change ContDiff ℝ ∞ (fun _ : E ↦ (0 : Covector E n))
      exact contDiff_const
    · simp [HasCompactSupport]
  add_mem' := by
    intro omega eta homega heta
    change IsSmoothForm omega ∧ HasCompactSupport omega at homega
    change IsSmoothForm eta ∧ HasCompactSupport eta at heta
    rcases homega with ⟨homega, hcomega⟩
    rcases heta with ⟨heta, hceta⟩
    exact ⟨homega.add heta, hcomega.add hceta⟩
  smul_mem' := by
    intro c omega homega
    change IsSmoothForm omega ∧ HasCompactSupport omega at homega
    rcases homega with ⟨homega, hcomega⟩
    exact ⟨homega.const_smul c, hcomega.smul_left⟩

/-- Simon §6.2: compactly supported smooth test `n`-forms. -/
abbrev TestForm (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) :=
  testFormSubmodule (E := E) n

/-- Simon Definition 6.2.1, algebraic core: an `n`-current acts linearly on
compactly supported smooth `n`-forms.  Simon additionally imposes continuity
in the test-form topology. -/
abbrev Current (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) :=
  TestForm E n →ₗ[ℝ] ℝ

/-- The sequence characterization of the test-form topology stated immediately
before Simon Definition 6.2.1: all forms have support in one compact set and
every iterated derivative converges uniformly there. -/
def TestFormConverges {n : ℕ} (omegaSeq : ℕ → TestForm E n)
    (omega : TestForm E n) : Prop :=
  ∃ K : Set E, IsCompact K ∧
    (∀ j, tsupport (omegaSeq j : DifferentialForm E n) ⊆ K) ∧
    tsupport (omega : DifferentialForm E n) ⊆ K ∧
    ∀ k : ℕ,
      TendstoUniformlyOn
        (fun j x ↦ iteratedFDeriv ℝ k (omegaSeq j : DifferentialForm E n) x)
        (fun x ↦ iteratedFDeriv ℝ k (omega : DifferentialForm E n) x) atTop K

/-- Simon Definition 6.2.1 with its continuity requirement.  We retain the
algebraic functional separately so boundary and mass formulas can reuse the
ordinary `LinearMap` API. -/
structure GeometricCurrent (E : Type u) [NormedAddCommGroup E]
    [NormedSpace ℝ E] (n : ℕ) where
  toCurrent : Current E n
  continuous' : ∀ (omegaSeq : ℕ → TestForm E n) (omega : TestForm E n),
    TestFormConverges omegaSeq omega →
      Tendsto (fun j ↦ toCurrent (omegaSeq j)) atTop (𝓝 (toCurrent omega))

instance {n : ℕ} : CoeFun (GeometricCurrent E n) (fun _ ↦ TestForm E n → ℝ) :=
  ⟨fun T ↦ T.toCurrent⟩

/-! ### Currents on an open domain -/

/-- The source test-form space `ᵏⁿ(U)`: globally smooth zero-extensions of
compactly supported smooth forms on `U`. The support condition makes this
equivalent to the usual domain-local presentation when `U` is open. -/
def testFormOnSubmodule (U : Set E) (n : ℕ) :
    Submodule ℝ (DifferentialForm E n) where
  carrier := fun omega ↦ IsTestForm omega ∧ tsupport omega ⊆ U
  zero_mem' := by
    constructor
    · change IsSmoothForm (0 : DifferentialForm E n) ∧
        HasCompactSupport (0 : DifferentialForm E n)
      exact ⟨by change ContDiff ℝ ∞ (fun _ : E ↦ (0 : Covector E n)); exact contDiff_const,
        by simp [HasCompactSupport]⟩
    · simp
  add_mem' := by
    intro omega eta homega heta
    rcases homega with ⟨⟨homega, hcomega⟩, hsomega⟩
    rcases heta with ⟨⟨heta, hceta⟩, hseta⟩
    exact ⟨⟨homega.add heta, hcomega.add hceta⟩,
      (tsupport_add omega eta).trans (union_subset hsomega hseta)⟩
  smul_mem' := by
    intro c omega homega
    rcases homega with ⟨⟨homega, hcomega⟩, hsomega⟩
    exact ⟨⟨homega.const_smul c, hcomega.smul_left⟩,
      (tsupport_smul_subset_right (fun _ : E ↦ c) omega).trans hsomega⟩

/-- Compactly supported smooth `n`-forms in the domain `U`. -/
abbrev TestFormOn (U : Set E) (n : ℕ) :=
  testFormOnSubmodule (E := E) U n

/-- Algebraic functional underlying a current on the domain `U`. -/
abbrev CurrentOn (U : Set E) (n : ℕ) :=
  TestFormOn (E := E) U n →ₗ[ℝ] ℝ

/-- The sequential topology on `ᵏⁿ(U)`: all supports lie in one compact
subset of `U`, and every iterated derivative converges uniformly there. -/
def TestFormOnConverges {U : Set E} {n : ℕ}
    (omegaSeq : ℕ → TestFormOn (E := E) U n)
    (omega : TestFormOn (E := E) U n) : Prop :=
  ∃ K : Set E, IsCompact K ∧ K ⊆ U ∧
    (∀ j, tsupport (omegaSeq j : DifferentialForm E n) ⊆ K) ∧
    tsupport (omega : DifferentialForm E n) ⊆ K ∧
    ∀ k : ℕ,
      TendstoUniformlyOn
        (fun j x ↦ iteratedFDeriv ℝ k (omegaSeq j : DifferentialForm E n) x)
        (fun x ↦ iteratedFDeriv ℝ k (omega : DifferentialForm E n) x) atTop K

/-- Simon Definition 6.2.1: a continuous linear functional on `ᵏⁿ(U)`,
with continuity expressed by Simon's sequential convergence criterion. -/
structure GeometricCurrentOn (U : Set E) (n : ℕ) where
  toCurrent : CurrentOn (E := E) U n
  continuous' : ∀ (omegaSeq : ℕ → TestFormOn (E := E) U n),
    TestFormOnConverges omegaSeq 0 →
      Tendsto (fun j ↦ toCurrent (omegaSeq j)) atTop (nhds 0)

instance {U : Set E} {n : ℕ} :
    CoeFun (GeometricCurrentOn (E := E) U n)
      (fun _ ↦ TestFormOn (E := E) U n → ℝ) :=
  ⟨fun T ↦ T.toCurrent⟩

/-- Simon (6.2.13): weak convergence of currents in an open domain is
pointwise convergence on every test form in that domain. -/
def WeaklyConvergesOn {U : Set E} {n : ℕ}
    (Tseq : ℕ → GeometricCurrentOn (E := E) U n)
    (T : GeometricCurrentOn (E := E) U n) : Prop :=
  ∀ omega, Tendsto (fun j ↦ Tseq j omega) atTop (nhds (T omega))

/-- Exterior differentiation preserves smooth compact support. -/
theorem exteriorDerivative_isTestForm {n : ℕ} {omega : DifferentialForm E n}
    (homega : IsTestForm omega) : IsTestForm (exteriorDerivative omega) := by
  change IsSmoothForm omega ∧ HasCompactSupport omega at homega
  change IsSmoothForm (exteriorDerivative omega) ∧
    HasCompactSupport (exteriorDerivative omega)
  constructor
  · change ContDiff ℝ ∞
      (fun x ↦ ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ omega x))
    simpa only [← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply,
      Function.comp_def] using
      (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ).contDiff.comp
        (homega.1.fderiv_right (by simp))
  · change HasCompactSupport
      (fun x ↦ ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ omega x))
    apply (homega.2.fderiv ℝ).comp_left
    exact map_zero _

/-- Exterior differentiation does not enlarge topological support. -/
theorem tsupport_exteriorDerivative_subset {n : ℕ}
    (omega : DifferentialForm E n) :
    tsupport (exteriorDerivative omega) ⊆ tsupport omega := by
  change tsupport
    (fun x ↦ ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ omega x)) ⊆
      tsupport omega
  exact (tsupport_comp_subset
    (g := ContinuousAlternatingMap.alternatizeUncurryFin) (map_zero _) _).trans
      (tsupport_fderiv_subset ℝ)

/-- Exterior derivative as a linear map on test forms supported in `U`. -/
def exteriorDerivativeTestOn (U : Set E) (n : ℕ) :
    TestFormOn (E := E) U n →ₗ[ℝ] TestFormOn (E := E) U (n + 1) where
  toFun omega := ⟨exteriorDerivative (omega : DifferentialForm E n), by
    constructor
    · exact exteriorDerivative_isTestForm omega.property.1
    · exact (tsupport_exteriorDerivative_subset
        (omega : DifferentialForm E n)).trans omega.property.2⟩
  map_add' omega eta := by
    apply Subtype.ext
    exact exteriorDerivative_add omega.property.1.1 eta.property.1.1
  map_smul' c omega := by
    apply Subtype.ext
    exact exteriorDerivative_smul c (omega : DifferentialForm E n)

/-- The operator on jets induced by postcomposing the derivative with a
fixed continuous linear map. -/
def derivativePostcomposeJet {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (k : ℕ) (L : (E →L[ℝ] F) →L[ℝ] G) :
    (E [×(k + 1)]→L[ℝ] F) →L[ℝ] (E [×k]→L[ℝ] G) :=
  (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin k ↦ E)
    (E →L[ℝ] F) G L).comp
      (continuousMultilinearCurryRightEquiv' ℝ k E F).toContinuousLinearEquiv.toContinuousLinearMap

theorem derivativePostcomposeJet_uniformContinuous {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (k : ℕ) (L : (E →L[ℝ] F) →L[ℝ] G) :
    UniformContinuous (derivativePostcomposeJet k L) :=
  (derivativePostcomposeJet k L).uniformContinuous

/-- The fixed continuous linear operator taking the `(k+1)`-jet of a form
to the `k`-jet of its exterior derivative. It curries the last derivative
slot and then alternates that slot with the covector slots. -/
def exteriorDerivativeJet (n k : ℕ) :
    (E [×(k + 1)]→L[ℝ] Covector E n) →L[ℝ]
      (E [×k]→L[ℝ] Covector E (n + 1)) :=
  derivativePostcomposeJet k (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ)

/-- Every derivative of `dω` is a fixed continuous linear image of the next
derivative of `ω`. This is the analytic estimate behind continuity of the
boundary operator in Simon (6.2.3). -/
theorem iteratedFDeriv_exteriorDerivative {n : ℕ}
    {omega : DifferentialForm E n} (homega : IsSmoothForm omega)
    (k : ℕ) (x : E) :
    iteratedFDeriv ℝ k (exteriorDerivative omega) x =
      exteriorDerivativeJet n k (iteratedFDeriv ℝ (k + 1) omega x) := by
  change iteratedFDeriv ℝ k
    ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ) ∘ fderiv ℝ omega) x = _
  rw [ContinuousLinearMap.iteratedFDeriv_comp_left _
    (homega.fderiv_right (m := ∞) (by simp)).contDiffAt (by simp)]
  rw [iteratedFDeriv_succ_eq_comp_right]
  simp [exteriorDerivativeJet, derivativePostcomposeJet]

/-- Exterior differentiation is sequentially continuous in Simon's topology
on test forms in an open domain: it keeps the common compact support and
uses one additional derivative of the convergent sequence. -/
theorem TestFormOnConverges.exteriorDerivative
    {U : Set E} {n : ℕ}
    {omegaSeq : ℕ → TestFormOn (E := E) U n}
    {omega : TestFormOn (E := E) U n}
    (h : TestFormOnConverges omegaSeq omega) :
    TestFormOnConverges
      (fun j ↦ exteriorDerivativeTestOn U n (omegaSeq j))
      (exteriorDerivativeTestOn U n omega) := by
  rcases h with ⟨K, hK, hKU, hseq, homega, hderiv⟩
  refine ⟨K, hK, hKU, fun j ↦ ?_, ?_, fun k ↦ ?_⟩
  · exact (tsupport_exteriorDerivative_subset
      (omegaSeq j : DifferentialForm E n)).trans (hseq j)
  · exact (tsupport_exteriorDerivative_subset
      (omega : DifferentialForm E n)).trans homega
  · have hcomp := (derivativePostcomposeJet_uniformContinuous k
      (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ)).comp_tendstoUniformlyOn
        (hderiv (k + 1))
    change TendstoUniformlyOn
      (fun j x ↦ exteriorDerivativeJet n k
        (iteratedFDeriv ℝ (k + 1) (omegaSeq j : DifferentialForm E n) x))
      (fun x ↦ exteriorDerivativeJet n k
        (iteratedFDeriv ℝ (k + 1) (omega : DifferentialForm E n) x)) atTop K at hcomp
    simpa only [Function.comp_def, exteriorDerivativeTestOn,
      LinearMap.coe_mk, AddHom.coe_mk, ← iteratedFDeriv_exteriorDerivative
      (omega.property.1.1) k,
      ← iteratedFDeriv_exteriorDerivative (omegaSeq _ |>.property.1.1) k]
      using hcomp

/-- Simon (6.2.3), on the algebraic functional underlying a current in `U`:
`∂T(ω)=T(dω)`. -/
def CurrentOn.boundary {U : Set E} {n : ℕ}
    (T : CurrentOn (E := E) U (n + 1)) : CurrentOn (E := E) U n :=
  T.comp (exteriorDerivativeTestOn U n)

@[simp] theorem CurrentOn.boundary_apply {U : Set E} {n : ℕ}
    (T : CurrentOn (E := E) U (n + 1))
    (omega : TestFormOn (E := E) U n) :
    T.boundary omega = T ((exteriorDerivativeTestOn U n) omega) :=
  rfl

/-- The algebraic boundaries of domain currents satisfy `∂²=0`. -/
theorem CurrentOn.boundary_boundary {U : Set E} {n : ℕ}
    (T : CurrentOn (E := E) U ((n + 1) + 1)) :
    T.boundary.boundary = 0 := by
  apply LinearMap.ext
  intro omega
  change T ((exteriorDerivativeTestOn U (n + 1))
    ((exteriorDerivativeTestOn U n) omega)) = (0 : ℝ)
  rw [← T.map_zero]
  apply congrArg T
  apply Subtype.ext
  exact exteriorDerivative_sq omega.property.1.1

/-- Continuous currents are determined by their values on test forms. -/
@[ext] theorem GeometricCurrentOn.ext {U : Set E} {n : ℕ}
    {S T : GeometricCurrentOn (E := E) U n}
    (h : ∀ omega, S omega = T omega) : S = T := by
  cases S
  cases T
  congr 1
  exact LinearMap.ext h

instance {U : Set E} {n : ℕ} : Zero (GeometricCurrentOn (E := E) U n) :=
  ⟨{ toCurrent := 0
     continuous' := fun _ _ ↦ tendsto_const_nhds }⟩

@[simp] theorem GeometricCurrentOn.zero_apply {U : Set E} {n : ℕ}
    (omega : TestFormOn (E := E) U n) :
    (0 : GeometricCurrentOn (E := E) U n) omega = 0 :=
  rfl

/-- Simon (6.2.3): the boundary of a continuous `(n+1)`-current is a
continuous `n`-current in the same domain. Continuity is derived from the
continuity of exterior differentiation in the test-form topology. -/
def GeometricCurrentOn.boundary {U : Set E} {n : ℕ}
    (T : GeometricCurrentOn (E := E) U (n + 1)) :
    GeometricCurrentOn (E := E) U n where
  toCurrent := T.toCurrent.boundary
  continuous' omegaSeq h := by
    apply T.continuous'
    simpa only [map_zero] using h.exteriorDerivative

@[simp] theorem GeometricCurrentOn.boundary_apply {U : Set E} {n : ℕ}
    (T : GeometricCurrentOn (E := E) U (n + 1))
    (omega : TestFormOn (E := E) U n) :
    T.boundary omega = T (exteriorDerivativeTestOn U n omega) :=
  rfl

/-- The degree of the boundary of an `n`-current. In degree zero the target
is the trivial space, implementing Simon's convention `ᵏ₋₁(U)=0` after
(6.2.3); for positive degree it is the space of currents one degree lower. -/
def CurrentBoundarySpaceOn (U : Set E) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => GeometricCurrentOn (E := E) U n

/-- Simon's boundary operation in every nonnegative degree, including the
zero-dimensional convention. -/
def GeometricCurrentOn.boundaryAtDegree {U : Set E} :
    (n : ℕ) → GeometricCurrentOn (E := E) U n → CurrentBoundarySpaceOn U n
  | 0, _ => PUnit.unit
  | _ + 1, T => T.boundary

@[simp] theorem GeometricCurrentOn.boundaryAtDegree_zero {U : Set E}
    (T : GeometricCurrentOn (E := E) U 0) :
    boundaryAtDegree 0 T = PUnit.unit :=
  rfl

@[simp] theorem GeometricCurrentOn.boundaryAtDegree_succ {U : Set E} {n : ℕ}
    (T : GeometricCurrentOn (E := E) U (n + 1)) :
    boundaryAtDegree (n + 1) T = T.boundary :=
  rfl

/-- The boundary of the boundary vanishes as a continuous current, as noted
immediately after Simon (6.2.3). -/
@[simp] theorem GeometricCurrentOn.boundary_boundary {U : Set E} {n : ℕ}
    (T : GeometricCurrentOn (E := E) U ((n + 1) + 1)) :
    T.boundary.boundary = 0 := by
  apply GeometricCurrentOn.ext
  intro omega
  change T.toCurrent.boundary.boundary omega = 0
  rw [CurrentOn.boundary_boundary]
  rfl

/-- Weak convergence of continuous currents implies pointwise convergence of
their underlying boundary functionals. -/
theorem WeaklyConvergesOn.boundary_pointwise
    {U : Set E} {n : ℕ}
    {Tseq : ℕ → GeometricCurrentOn (E := E) U (n + 1)}
    {T : GeometricCurrentOn (E := E) U (n + 1)}
    (h : WeaklyConvergesOn Tseq T) :
    ∀ omega : TestFormOn (E := E) U n,
      Tendsto (fun j ↦ (Tseq j).toCurrent.boundary omega) atTop
        (nhds (T.toCurrent.boundary omega)) := by
  intro omega
  exact h ((exteriorDerivativeTestOn U n) omega)

/-- Boundary preserves weak convergence in Simon's space of continuous
currents on `U`, by (6.2.3) and (6.2.13). -/
theorem WeaklyConvergesOn.boundary {U : Set E} {n : ℕ}
    {Tseq : ℕ → GeometricCurrentOn (E := E) U (n + 1)}
    {T : GeometricCurrentOn (E := E) U (n + 1)}
    (h : WeaklyConvergesOn Tseq T) :
    WeaklyConvergesOn (fun j ↦ (Tseq j).boundary) T.boundary :=
  h.boundary_pointwise

/-- Exterior derivative as a linear map between test-form spaces. -/
def exteriorDerivativeTest (n : ℕ) : TestForm E n →ₗ[ℝ] TestForm E (n + 1) where
  toFun omega := ⟨exteriorDerivative omega, exteriorDerivative_isTestForm omega.property⟩
  map_add' omega eta := by
    apply Subtype.ext
    have homega := omega.property
    have heta := eta.property
    change IsSmoothForm (omega : DifferentialForm E n) ∧
      HasCompactSupport (omega : DifferentialForm E n) at homega
    change IsSmoothForm (eta : DifferentialForm E n) ∧
      HasCompactSupport (eta : DifferentialForm E n) at heta
    exact exteriorDerivative_add homega.1 heta.1
  map_smul' c omega := by
    apply Subtype.ext
    exact exteriorDerivative_smul c (omega : DifferentialForm E n)

/-- Simon (6.2.3): boundary of a current, `∂T(ω)=T(dω)`. -/
def Current.boundary {n : ℕ} (T : Current E (n + 1)) : Current E n :=
  T.comp (exteriorDerivativeTest n)

@[simp] theorem Current.boundary_apply {n : ℕ} (T : Current E (n + 1))
    (omega : TestForm E n) :
    T.boundary omega = T ⟨exteriorDerivative omega, exteriorDerivative_isTestForm omega.property⟩ :=
  rfl

/-- The current-level consequence of Simon (6.1.12): `∂²T=0`. -/
theorem Current.boundary_boundary {n : ℕ} (T : Current E ((n + 1) + 1)) :
    T.boundary.boundary = 0 := by
  apply LinearMap.ext
  intro omega
  have homega := omega.property
  change IsSmoothForm (omega : DifferentialForm E n) ∧
    HasCompactSupport (omega : DifferentialForm E n) at homega
  change T ((exteriorDerivativeTest (n + 1)) ((exteriorDerivativeTest n) omega)) = (0 : ℝ)
  rw [← T.map_zero]
  apply congrArg T
  apply Subtype.ext
  exact exteriorDerivative_sq homega.1

@[simp] theorem Current.boundary_zero (n : ℕ) :
    Current.boundary (E := E) (n := n) 0 = 0 :=
  rfl

@[simp] theorem Current.boundary_add {n : ℕ} (S T : Current E (n + 1)) :
    (S + T).boundary = S.boundary + T.boundary :=
  rfl

@[simp] theorem Current.boundary_smul {n : ℕ} (c : ℝ) (T : Current E (n + 1)) :
    (c • T).boundary = c • T.boundary :=
  rfl

@[simp] theorem Current.boundary_sub {n : ℕ} (S T : Current E (n + 1)) :
    (S - T).boundary = S.boundary - T.boundary :=
  rfl

/-- Simon (6.2.13): weak convergence of currents is pointwise convergence on
every compactly supported smooth form. -/
def WeaklyConverges {n : ℕ} (Tseq : ℕ → Current E n) (T : Current E n) : Prop :=
  ∀ omega, Tendsto (fun j ↦ Tseq j omega) atTop (𝓝 (T omega))

/-- Boundary is continuous for weak convergence, the immediate consequence of
Simon (6.2.3) and (6.2.13). -/
theorem WeaklyConverges.boundary {n : ℕ} {Tseq : ℕ → Current E (n + 1)}
    {T : Current E (n + 1)} (h : WeaklyConverges Tseq T) :
    WeaklyConverges (fun j ↦ (Tseq j).boundary) T.boundary := by
  intro omega
  exact h ((exteriorDerivativeTest n) omega)

/-- Unit-comass tests for the algebraic whole-space current API. Simon's
coefficient-norm admissible tests are `massAdmissibleOn` in `Chapter06.Mass`.
-/
def massAdmissible (n : ℕ) (W : Set E) : Set (TestForm E n) :=
  {omega | tsupport (omega : DifferentialForm E n) ⊆ W ∧
    ∀ x, ‖(omega : DifferentialForm E n) x‖ ≤ 1}

/-- Conventional comass local mass for algebraic currents: the supremum of
`|T(ω)|` over unit-comass test forms supported in `W`. Simon (6.2.5) chooses
the Euclidean coefficient norm, implemented by `GeometricCurrentOn.massOn`.
-/
def Current.massOn {n : ℕ} (T : Current E n) (W : Set E) : ℝ≥0∞ :=
  sSup (ENNReal.ofReal ∘ abs ∘ T '' massAdmissible n W)

/-- Local mass is monotone in the region. -/
theorem Current.massOn_mono {n : ℕ} (T : Current E n) {W₁ W₂ : Set E}
    (hW : W₁ ⊆ W₂) : T.massOn W₁ ≤ T.massOn W₂ := by
  apply sSup_le_sSup
  rintro z ⟨omega, homega, rfl⟩
  exact ⟨omega, ⟨homega.1.trans hW, homega.2⟩, rfl⟩

/-- Global comass mass as local mass on the whole ambient space. The
source norm convention of Simon (6.2.4) is `GeometricCurrentOn.mass`. -/
def Current.mass {n : ℕ} (T : Current E n) : ℝ≥0∞ := T.massOn univ

/-! ## Support (§2.11) -/

/-- A current vanishes in `W` when it kills every test form supported there. -/
def Current.VanishesOn {n : ℕ} (T : Current E n) (W : Set E) : Prop :=
  ∀ omega : TestForm E n, tsupport (omega : DifferentialForm E n) ⊆ W → T omega = 0

/-- The union of relatively compact open sets on which the current vanishes. -/
def Current.zeroRegion {n : ℕ} (T : Current E n) : Set E :=
  ⋃₀ {W : Set E | IsOpen W ∧ IsCompact (closure W) ∧ T.VanishesOn W}

/-- Simon (6.2.11): support is the complement of the relatively compact open
zero region. -/
def Current.support {n : ℕ} (T : Current E n) : Set E :=
  (T.zeroRegion)ᶜ

theorem Current.isOpen_zeroRegion {n : ℕ} (T : Current E n) :
    IsOpen T.zeroRegion := by
  apply isOpen_sUnion
  intro W hW
  exact hW.1

theorem Current.isClosed_support {n : ℕ} (T : Current E n) :
    IsClosed T.support :=
  T.isOpen_zeroRegion.isClosed_compl

/-! ## Integer-multiplicity rectifiable data (§3) -/

variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- Source-faithful data in Simon Definition 6.3.1.  The positive natural-valued
multiplicity is locally integrable, and the measurable orthonormal frame spans
the declared approximate tangent plane almost everywhere. -/
structure IntegerRectifiableCurrentData (n : ℕ) where
  carrier : Set F
  measurable_carrier : MeasurableSet carrier
  rectifiable_carrier : Poincare.SimonGMT.Chapter04.CountablyRectifiable n carrier
  multiplicity : F → ℕ
  measurable_multiplicity : Measurable multiplicity
  positive_multiplicity : ∀ᵐ x
    ∂(MeasureTheory.Measure.euclideanHausdorffMeasure n).restrict carrier,
      multiplicity x ≠ 0
  locallyIntegrable_multiplicity : MeasureTheory.LocallyIntegrable
    (carrier.indicator fun x ↦ (multiplicity x : ℝ))
      (MeasureTheory.Measure.euclideanHausdorffMeasure n)
  tangent : F → Submodule ℝ F
  tangent_dimension : ∀ᵐ x
    ∂(MeasureTheory.Measure.euclideanHausdorffMeasure n).restrict carrier,
      Module.finrank ℝ (tangent x) = n
  frame : F → Fin n → F
  measurable_frame : ∀ i, Measurable (fun x ↦ frame x i)
  frame_orthonormal : ∀ᵐ x
    ∂(MeasureTheory.Measure.euclideanHausdorffMeasure n).restrict carrier,
      Orthonormal ℝ (frame x)
  frame_spans_tangent : ∀ᵐ x
    ∂(MeasureTheory.Measure.euclideanHausdorffMeasure n).restrict carrier,
      Submodule.span ℝ (range (frame x)) = tangent x

/-- The integral action `∫_M θ ⟨ω,ξ⟩ dℓHⁿ` from Simon Definition 6.3.1.
The data above contain the positivity, measurability, local integrability, and
oriented tangent-frame conditions needed by the source definition.  Turning
this action into a `GeometricCurrent` still requires the standard integral
continuity estimate. -/
def IntegerRectifiableCurrentData.action {n : ℕ}
    (T : IntegerRectifiableCurrentData (F := F) n)
    (omega : DifferentialForm F n) : ℝ :=
  ∫ x in T.carrier, (T.multiplicity x : ℝ) * omega x (T.frame x)
    ∂MeasureTheory.Measure.euclideanHausdorffMeasure n

end

end Poincare.SimonGMT.Chapter06
