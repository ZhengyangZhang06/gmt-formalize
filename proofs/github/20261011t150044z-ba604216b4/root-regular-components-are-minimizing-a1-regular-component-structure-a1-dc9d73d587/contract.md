<!-- theorem-id: gmt-ch07/root.regular_components_are_minimizing-a1.regular_component_structure-a1 -->

## Theorem `Submission.regcomp_regular_component_structure`

Let U ⊆ ℝ^P be open, n = m + 1 ≥ 1, let the IMRep R = (C, θ, ξ) in U represent T ∈ 𝒟_n(U), let y ∈ reg T (Simon 7.4.1 as formalized by regularSet), let M₁ be the connected component of reg T containing y, and let T₁ ∈ 𝒟_n(U) satisfy T₁(ω) = ∫_{M₁} ⟨ω, ξ⟩ dH^n for all ω ∈ 𝒟^n(U). Then (i) M₁ is Borel; (ii) H^n(M₁ ∖ C) = 0; (iii) closure(M₁) ∩ U ⊆ M₁ ∪ sing T; (iv) sing T ∩ K is compact for every compact K ⊆ U; (v) every z ∈ M₁ has an open neighbourhood G and a constant c ∈ ℝ with T₁(ω) = c·T(ω) for all ω ∈ 𝒟^n(U) with tsupport ω ⊆ G.

Node: `root.regular_components_are_minimizing-a1.regular_component_structure-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/383

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.regcomp_regular_component_structure`

```lean
∀ (P m : ℕ) (U : Set (Euclid P)) (T T₁ : GeometricCurrentOn U (m + 1)) (R : IMRep U (m + 1)) (y : Euclid P), IsOpen U → R.Represents T → y ∈ regularSet T → (∀ ω : TestFormOn U (m + 1), T₁ ω = ∫ x in connectedComponentIn (regularSet T) y, R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1]) → MeasurableSet (connectedComponentIn (regularSet T) y) ∧ μHE[m + 1] (connectedComponentIn (regularSet T) y \ R.carrier) = 0 ∧ closure (connectedComponentIn (regularSet T) y) ∩ U ⊆ connectedComponentIn (regularSet T) y ∪ singularSet T ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → IsCompact (singularSet T ∩ K)) ∧ ∀ z ∈ connectedComponentIn (regularSet T) y, ∃ G : Set (Euclid P), IsOpen G ∧ z ∈ G ∧ ∃ c : ℝ, ∀ ω : TestFormOn U (m + 1), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ G → T₁ ω = c * T ω
```

### Frozen project context

`GMT/Ch07/Contract.lean` at `b4d606db1da5da8fa2c0292ad4924d97de8b3c4b` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.LinearAlgebra.Trace
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter06.AffineCurrentPushforward

/-!
# Simon, *Introduction to Geometric Measure Theory*, Chapter 7 "Area Minimizing Currents"
(printed pp. 181–204)

Frozen contract.  Currents, boundary, mass, support and weak convergence are the clean SimonGMT
objects of `Poincare.SimonGMT.Chapter06`: `GeometricCurrentOn U n` (Simon 6.2.1), `T.boundary`
(6.2.3), `T.massOn W` = `M_W(T)` (6.2.5, Euclidean coefficient norm), `T.mass` (6.2.4),
`T.support` (6.2.11), `WeaklyConvergesOn` (6.2.13), and the proper affine push-forward
`GeometricCurrentOn.affinePushforward` (6.2.23).  Everything else (integer multiplicity currents,
minimizing currents, densities, blow-ups, tangent cones, `reg T`, `sing T`, the associated
varifold) is defined below from primitive data.  `Hⁿ` is Mathlib's normalized `μHE[n]`; null-set
statements use Mathlib's `μH[s]` (same null sets as Simon's `Hˢ`).

**Conventions.**  The ambient space is `ℝ^{n+k}` (`Euclid (n + k)`); when a submanifold `N` is
present it has dimension `n + ℓ`, `ℓ ≤ k` (Simon writes `N^{n+ℓ} ⊂ ℝ^{n+ℓ}`, `ℓ ≤ k`, a
misprint for `ℝ^{n+k}`; `N = ℝ^{n+k}` is the case `ℓ = k`).  For an `n`-current, `∂T = 0`,
`∂S = ∂T`, `spt ∂T`, `M_W(∂T)` are read with Simon's convention `∂T = 0` if `n = 0` (6.2.3).
-/

open Filter Function Set MeasureTheory Metric
open scoped ENNReal Topology

namespace GMT.Ch07

open Poincare.SimonGMT.Chapter06
open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt)

noncomputable section

/-- Euclidean space `ℝᴾ`. -/
abbrev Euclid (P : ℕ) := EuclideanSpace ℝ (Fin P)

variable {P : ℕ}

/-! ## Multivectors and integer multiplicity currents (Simon Ch. 6, §1 and 3.1) -/

/-- `n`-vectors `Λₙ(ℝᴾ)`, realized as the dual of `n`-covectors (Simon 6.1, `Λₙ ≅ (Λⁿ)*`);
`ξ α` is the pairing `⟨α, ξ⟩` of Simon (6.1.7). -/
abbrev MultiVector (P n : ℕ) := Covector (Euclid P) n →L[ℝ] ℝ

/-- `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal basis `τ` of the subspace `Q`, i.e.
`⟨α, ξ⟩ = ±α(τ₁, …, τₙ)` (Simon 6.1.1, 6.1.7; 6.2.2).  The sign matters only for `n = 0`. -/
def IsUnitOrientationOf {n : ℕ} (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)) : Prop :=
  ∃ τ : Fin n → Euclid P, Orthonormal ℝ τ ∧ Submodule.span ℝ (range τ) = Q ∧
    ((∀ α : Covector (Euclid P) n, ξ α = α τ) ∨ ∀ α : Covector (Euclid P) n, ξ α = -α τ)

/-- Simon Ch. 6, Definition 3.1 (p. 146): a triple `(M, θ, ξ)` in `U`.  `M ⊆ U` is
`Hⁿ`-measurable (taken Borel; this loses nothing, `Hⁿ⌞M` being σ-finite) and countably
`n`-rectifiable; `θ` is positive integer-valued on `M` and locally `Hⁿ`-integrable in `U`; `ξ` is
`Hⁿ`-measurable and, `Hⁿ`-a.e. on `M`, orients the approximate tangent space `TₓM`
(Ch. 3, 1.4). -/
structure IMRep (U : Set (Euclid P)) (n : ℕ) where
  carrier : Set (Euclid P)
  mult : Euclid P → ℕ
  orient : Euclid P → MultiVector P n
  measurableSet_carrier : MeasurableSet carrier
  carrier_subset : carrier ⊆ U
  rectifiable : CountablyRectifiable n carrier
  measurable_mult : Measurable mult
  mult_pos : ∀ x ∈ carrier, 0 < mult x
  locallyIntegrable_mult : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
    ∫⁻ x in carrier ∩ K, (mult x : ℝ≥0∞) ∂μHE[n] ≠ ∞
  aestronglyMeasurable_orient : AEStronglyMeasurable orient (μHE[n].restrict carrier)
  orients : ∀ᵐ x ∂(μHE[n].restrict carrier), ∃ Q : Submodule ℝ (Euclid P),
    HasApproximateTangentSpaceAt n carrier x Q ∧ IsUnitOrientationOf (orient x) Q

variable {U : Set (Euclid P)} {n : ℕ}

/-- `τ(M, θ, ξ)(ω) = ∫_M ⟨ω(x), ξ(x)⟩ θ(x) dHⁿ(x)` (Simon 6.3.1 (‡)). -/
def IMRep.action (R : IMRep U n) (ω : DifferentialForm (Euclid P) n) : ℝ :=
  ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (ω x) ∂μHE[n]

/-- `T = τ(M, θ, ξ)` in `U`. -/
def IMRep.Represents (R : IMRep U n) (T : GeometricCurrentOn U n) : Prop :=
  ∀ ω : TestFormOn U n, T ω = R.action (ω : DifferentialForm (Euclid P) n)

/-- The weight `μ_V = θ Hⁿ⌞M` of the associated varifold `V = v(M, θ)`; it equals the mass
measure `μ_T` of `T = τ(M, θ, ξ)` (Simon 6.3.2(3), 4.1.1). -/
def IMRep.measure (R : IMRep U n) : Measure (Euclid P) :=
  (μHE[n].restrict R.carrier).withDensity fun x => (R.mult x : ℝ≥0∞)

/-- Simon 6.3.1: `T` is an integer multiplicity (rectifiable) current. -/
def IsIntegerMultiplicity (T : GeometricCurrentOn U n) : Prop :=
  ∃ R : IMRep U n, R.Represents T

/-- Difference of currents (needed for `spt(S − T)` in 7.1.1). -/
instance : Sub (GeometricCurrentOn U n) where
  sub S T :=
    { toCurrent := S.toCurrent - T.toCurrent
      continuous' := fun ωs h => by
        simpa using (S.continuous' ωs h).sub (T.continuous' ωs h) }

/-! ## Boundary conventions in arbitrary degree -/

/-- `∂S = ∂T` in `U` (vacuous for `n = 0`, where `∂ = 0`). -/
def SameBoundary : {n : ℕ} → GeometricCurrentOn U n → GeometricCurrentOn U n → Prop
  | 0, _, _ => True
  | _ + 1, S, T => S.boundary = T.boundary

/-- `∂T = 0` in `U`. -/
def BoundaryVanishes : {n : ℕ} → GeometricCurrentOn U n → Prop
  | 0, _ => True
  | _ + 1, T => T.boundary = 0

/-- `spt ∂T` (empty for `n = 0`). -/
def boundarySupport : {n : ℕ} → GeometricCurrentOn U n → Set (Euclid P)
  | 0, _ => ∅
  | _ + 1, T => T.boundary.support

/-- `M_W(∂T)` (zero for `n = 0`). -/
def boundaryMassOn : {n : ℕ} → GeometricCurrentOn U n → Set (Euclid P) → ℝ≥0∞
  | 0, _, _ => 0
  | _ + 1, T, W => T.boundary.massOn W

/-! ## Minimizing currents (Simon 7.1.1) -/

/-- `W ⊂⊂ U`: `closure W` is a compact subset of `U`. -/
def CompactlyContained (W U : Set (Euclid P)) : Prop :=
  IsCompact (closure W) ∧ closure W ⊆ U

/-- **Simon 7.1.1 (p. 181).**  The integer multiplicity `T ∈ 𝒟ₙ(U)` is *minimizing in `A`*
(`A ⊆ U`): `M_W(T) ≤ M_W(S)` whenever `W ⊂⊂ U` is open, `S ∈ 𝒟ₙ(U)` is integer multiplicity,
`∂S = ∂T` in `U` and `spt(S − T)` is a compact subset of `A ∩ W`.  Competitors are integer
multiplicity, as required by Remark 7.2.2(1) and the proofs of 7.1.4 and 7.2.4. -/
def IsMinimizingIn (T : GeometricCurrentOn U n) (A : Set (Euclid P)) : Prop :=
  IsIntegerMultiplicity T ∧
    ∀ (W : Set (Euclid P)) (S : GeometricCurrentOn U n), IsOpen W → CompactlyContained W U →
      IsIntegerMultiplicity S → SameBoundary S T → IsCompact (S - T).support →
        (S - T).support ⊆ A ∩ W → T.massOn W ≤ S.massOn W

/-! ## Densities, blow-ups, tangent cones (Simon 7.3) -/

/-- `ωₙ`, the Lebesgue measure of the unit ball of `ℝⁿ`. -/
def unitBallVolume (n : ℕ) : ℝ≥0∞ := volume (ball (0 : Euclid n) 1)

/-- `Θⁿ(μ_T, x) = θ`: `(ωₙρⁿ)⁻¹ μ_T(B_ρ(x)) → θ` as `ρ ↓ 0`, with `μ_T(B_ρ(x)) = M_{B_ρ(x)}(T)`
for small `ρ` (Simon 6.2.8; open and closed balls give the same limit). -/
def HasMassDensity (T : GeometricCurrentOn U n) (x : Euclid P) (θ : ℝ) : Prop :=
  0 ≤ θ ∧ Tendsto (fun ρ : ℝ => T.massOn (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n)))
    (𝓝[>] 0) (𝓝 (ENNReal.ofReal θ))

/-- Value of a current in `U` on an ambient form: `T(ω)` if `ω ∈ 𝒟ⁿ(U)`, else `0`.  Used for
convergence of currents on varying domains (Simon: "`η_{x,λⱼ#}T ⇀ C` in `ℝ^{n+ℓ}`"). -/
def currentEval (T : GeometricCurrentOn U n) (ω : DifferentialForm (Euclid P) n) : ℝ := by
  classical
  exact if h : IsTestForm ω ∧ tsupport ω ⊆ U then T ⟨ω, h⟩ else 0

/-- `Tⱼ ⇀ T` in `V`, for currents `Tⱼ ∈ 𝒟ₙ(Uⱼ)` whose domains eventually contain every compact
subset of `V` (as for blow-ups): `Tⱼ(ω) → T(ω)` for every `ω ∈ 𝒟ⁿ(V)` (Simon 6.2.13). -/
def ConvergesWeakly {Us : ℕ → Set (Euclid P)} (Ts : (j : ℕ) → GeometricCurrentOn (Us j) n)
    {V : Set (Euclid P)} (T : GeometricCurrentOn V n) : Prop :=
  ∀ ω : TestFormOn V n,
    Tendsto (fun j => currentEval (Ts j) (ω : DifferentialForm (Euclid P) n)) atTop (𝓝 (T ω))

/-- `μ_{Tⱼ} → μ_T` as Radon measures in `V` (Simon 7.2.4, Remark 7.2.5(1)): for all integer
multiplicity representations of the `Tⱼ` and of `T`, `∫ f dμ_{Tⱼ} → ∫ f dμ_T` for every
continuous `f` with compact support in `V`. -/
def MassMeasuresConverge {Us : ℕ → Set (Euclid P)} (Ts : (j : ℕ) → GeometricCurrentOn (Us j) n)
    {V : Set (Euclid P)} (T : GeometricCurrentOn V n) : Prop :=
  ∀ Rs : (j : ℕ) → IMRep (Us j) n, (∀ j, (Rs j).Represents (Ts j)) →
    ∀ R : IMRep V n, R.Represents T →
      ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ V →
        Tendsto (fun j => ∫ x, f x ∂(Rs j).measure) atTop (𝓝 (∫ x, f x ∂R.measure))

/-- The linear part `y ↦ λ⁻¹y` of the dilation `η_{x,λ}`. -/
def dilationCLM (P : ℕ) (lam : ℝ) : Euclid P →L[ℝ] Euclid P :=
  lam⁻¹ • ContinuousLinearMap.id ℝ (Euclid P)

/-- Simon's dilation `η_{x,λ}(y) = λ⁻¹(y − x)`, written `y ↦ −λ⁻¹x + λ⁻¹y`. -/
def dilation (x : Euclid P) (lam : ℝ) : Euclid P → Euclid P :=
  fun y => -(lam⁻¹ • x) + dilationCLM P lam y

/-- The blow-up `η_{x,λ#}T ∈ 𝒟ₙ(η_{x,λ}(U))`, `η_{x,λ#}T(ω) = T(η_{x,λ}^# ω)` (Simon 6.2.23 for
the proper affine diffeomorphism `η_{x,λ}`, `λ ≠ 0`). -/
def blowUp (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : lam ≠ 0) :
    GeometricCurrentOn (dilation x lam '' U) n :=
  (T.restrictDomain (show (fun y => -(lam⁻¹ • x) + dilationCLM P lam y) ⁻¹'
      (dilation x lam '' U) ⊆ U by
    rintro y ⟨z, hz, hzy⟩
    have hzy' : lam⁻¹ • z = lam⁻¹ • y := by
      simpa [dilation, dilationCLM] using hzy
    rwa [← smul_right_injective (Euclid P) (inv_ne_zero hlam) hzy'])).affinePushforward
    (dilationCLM P lam) (-(lam⁻¹ • x)) (by
      convert ((Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam)).trans
        (Homeomorph.addLeft (-(lam⁻¹ • x)))).isProperMap using 1
      funext y
      simp [dilationCLM])

/-- `C ∈ 𝒟ₙ(ℝᴾ)` is a cone: `η_{0,λ#}C = C` for every `λ > 0` (Simon 7.3.1(2)). -/
def IsConeCurrent (C : GeometricCurrentOn (univ : Set (Euclid P)) n) : Prop :=
  ∀ (lam : ℝ) (hlam : 0 < lam) (ω : TestFormOn (univ : Set (Euclid P)) n),
    currentEval (blowUp C 0 lam hlam.ne') (ω : DifferentialForm (Euclid P) n) = C ω

/-- Simon 7.3.2(1): `C` is a tangent cone of `T` at `x`, i.e. `η_{x,λⱼ#}T ⇀ C` in `ℝᴾ` for some
sequence `λⱼ > 0`, `λⱼ → 0`. -/
def IsTangentConeAt (T : GeometricCurrentOn U n) (x : Euclid P)
    (C : GeometricCurrentOn (univ : Set (Euclid P)) n) : Prop :=
  ∃ (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), Tendsto lams atTop (𝓝 0) ∧
    ConvergesWeakly (fun j => blowUp T x (lams j) (hlams j).ne') C

/-- Simon 7.3.2(1): `T` has a (multiplicity `m`) tangent plane at `x`: some tangent cone has
support an `n`-dimensional subspace. -/
def HasTangentPlaneAt (T : GeometricCurrentOn U n) (x : Euclid P) : Prop :=
  ∃ C : GeometricCurrentOn (univ : Set (Euclid P)) n, IsTangentConeAt T x C ∧
    ∃ Q : Submodule ℝ (Euclid P), Module.finrank ℝ Q = n ∧ C.support = (Q : Set (Euclid P))

/-! ## Submanifolds, `reg T`, `sing T` (Simon Ch. 2, §4 and 7.4.1) -/

/-- Simon Ch. 2, §4, (4.1) (p. 55): `M ⊂ ℝᴾ` is a `d`-dimensional (embedded) `Cʳ` submanifold:
each `y ∈ M` has an open `W ∋ y` and a 1:1 `Cʳ` map `ψ : V → W`, `V ⊆ ℝᵈ` open, with
`ψ(V) = W ∩ M`, `ψ` proper, and `Dψ` of rank `d` on `V`. -/
def IsEmbeddedSubmanifold (r d : ℕ) (M : Set (Euclid P)) : Prop :=
  ∀ y ∈ M, ∃ (V : Set (Euclid d)) (W : Set (Euclid P)) (ψ : Euclid d → Euclid P),
    IsOpen V ∧ IsOpen W ∧ y ∈ W ∧ ContDiffOn ℝ r ψ V ∧ InjOn ψ V ∧ ψ '' V = W ∩ M ∧
      (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) ∧
      ∀ z ∈ V, Injective (fderiv ℝ ψ z)

/-- Simon Ch. 2, §4 (p. 55): `T_yM = {γ'(0) : γ ∈ C¹((−1,1); ℝᴾ), γ((−1,1)) ⊆ M, γ(0) = y}`. -/
def tangentSpace (M : Set (Euclid P)) (y : Euclid P) : Set (Euclid P) :=
  {v | ∃ γ : ℝ → Euclid P, ContDiffOn ℝ 1 γ (Ioo (-1) 1) ∧ MapsTo γ (Ioo (-1) 1) M ∧
    γ 0 = y ∧ HasDerivAt γ v 0}

/-- An orientation of the `d`-dimensional submanifold `M` (Simon 6.2.2): `ξ` is continuous on
`M` and `ξ(y) = ±τ₁ ∧ ⋯ ∧ τ_d` for an orthonormal basis `τ` of `T_yM`, for every `y ∈ M`. -/
def IsOrientation (d : ℕ) (M : Set (Euclid P)) (ξ : Euclid P → MultiVector P d) : Prop :=
  ContinuousOn ξ M ∧ ∀ y ∈ M, ∃ Q : Submodule ℝ (Euclid P),
    (Q : Set (Euclid P)) = tangentSpace M y ∧ IsUnitOrientationOf (ξ y) Q

/-- **Simon 7.4.1 (p. 193)**: `reg T` is the set of `y ∈ spt T` such that, for some `ρ > 0`
(with `B_ρ(y) ⊆ U`), `m ∈ ℤ \ {0}` and embedded `n`-dimensional oriented `C¹` submanifold `M`
(of locally finite `Hⁿ`-measure in `B_ρ(y)`, as `[[M]]` requires, 6.2.2), `T = m[[M]]` in
`B_ρ(y)` (6.2.16), i.e. `T(ω) = m ∫_M ⟨ω, ξ_M⟩ dHⁿ` whenever `spt ω ⊆ B_ρ(y)`.
The point `y` itself must lie on `M` (as in 4.4(8) and the proof of 5.8): otherwise a singular
point could be declared regular by deleting it from `M`, e.g. the vertex of the Simons cone. -/
def regularSet (T : GeometricCurrentOn U n) : Set (Euclid P) :=
  {y | y ∈ T.support ∧ ∃ ρ : ℝ, 0 < ρ ∧ ball y ρ ⊆ U ∧
    ∃ (m : ℤ) (M : Set (Euclid P)) (ξ : Euclid P → MultiVector P n), m ≠ 0 ∧ y ∈ M ∧
      IsEmbeddedSubmanifold 1 n M ∧ IsOrientation n M ξ ∧
      (∀ K : Set (Euclid P), IsCompact K → K ⊆ ball y ρ → μHE[n] (M ∩ K) ≠ ∞) ∧
      ∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ ball y ρ →
        T ω = m * ∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]}

/-- **Simon 7.4.1**: `sing T = spt T \ reg T`. -/
def singularSet (T : GeometricCurrentOn U n) : Set (Euclid P) :=
  T.support \ regularSet T

/-! ## The associated varifold `V = v(M, θ)` (Simon Ch. 4, 2.3–2.7 and 3.14) -/

/-- The approximate tangent plane `TₓM` (Ch. 3, 1.4; unique when it exists), `⊥` otherwise. -/
def approxTangentPlane (n : ℕ) (M : Set (Euclid P)) (x : Euclid P) :
    Submodule ℝ (Euclid P) := by
  classical
  exact if h : ∃ Q, HasApproximateTangentSpaceAt n M x Q then h.choose else ⊥

/-- `div_M X(x) = Σⱼ eⱼ · ∇^M Xʲ = trace(p_{TₓM} ∘ DX(x))` (Simon Ch. 4, 2.3). -/
def tangentialDivergence (n : ℕ) (M : Set (Euclid P)) (X : Euclid P → Euclid P)
    (x : Euclid P) : ℝ :=
  LinearMap.trace ℝ (Euclid P)
    ((approxTangentPlane n M x).starProjection.toLinearMap ∘ₗ (fderiv ℝ X x).toLinearMap)

/-- First variation `δV(X) = ∫_M div_M X dμ_V` of `V = v(M, θ)` (Simon Ch. 4, 2.2). -/
def IMRep.firstVariation (R : IMRep U n) (X : Euclid P → Euclid P) : ℝ :=
  ∫ x in R.carrier, (R.mult x : ℝ) * tangentialDivergence n R.carrier X x ∂μHE[n]

/-- Simon Ch. 4, 2.6 (computed form, p. 88): `V` is stationary in `U ∩ N`: `δV(X) = 0` for all
`X ∈ C¹_c(U; ℝᴾ)` with `X(x) ∈ TₓN` for every `x ∈ N ∩ U`. -/
def IMRep.IsStationaryAlong (R : IMRep U n) (N : Set (Euclid P)) : Prop :=
  ∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U →
    (∀ x ∈ N ∩ U, X x ∈ tangentSpace N x) → R.firstVariation X = 0

/-- Simon Ch. 4, 3.14: `V` has generalized mean curvature `H` in `U`
(`∫ div_M X dμ_V = −∫ X · H dμ_V`, `X ∈ C¹_c(U; ℝᴾ)`), with `H` bounded on compact subsets. -/
def IMRep.HasLocallyBoundedMeanCurvature (R : IMRep U n) : Prop :=
  ∃ H : Euclid P → Euclid P, AEStronglyMeasurable H R.measure ∧
    (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ Λ : ℝ, ∀ᵐ x ∂R.measure, x ∈ K → ‖H x‖ ≤ Λ) ∧
    ∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U →
      R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure

/-! ## Codimension one (Simon 7.5) -/

/-- Simon 7.5 (p. 197): `N ∈ 𝒪`, an oriented embedded `C²` submanifold of dimension `n + 1` with
`(N̄ \ N) ∩ U = ∅` and `N ∩ U ≠ ∅`, with chosen orientation `ξN`. -/
def InClassO (n : ℕ) (U N : Set (Euclid P)) (ξN : Euclid P → MultiVector P (n + 1)) : Prop :=
  IsEmbeddedSubmanifold 2 (n + 1) N ∧ IsOrientation (n + 1) N ξN ∧ (closure N \ N) ∩ U = ∅ ∧
    (N ∩ U).Nonempty

/-- Simon 7.5.1: `T = ∂[[E]]` in `U`, where `[[E]](ω) = ∫_E ⟨ω, ξ_N⟩ dH^{n+1}`. -/
def IsBoundaryOfRegion (T : GeometricCurrentOn U n) (E : Set (Euclid P))
    (ξN : Euclid P → MultiVector P (n + 1)) : Prop :=
  ∀ ω : TestFormOn U n,
    T ω = ∫ x in E, ξN x (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x) ∂μHE[n + 1]

/-! ## Headline results -/

/-- **Simon 7.1.2 (Lemma, pp. 181–182).**  Let `N` be an embedded `C²` `(n+ℓ)`-dimensional
submanifold of `ℝ^{n+k}`, `(N̄ \ N) ∩ U = ∅`.  If `T ∈ 𝒟ₙ(U)` is minimizing in `N ∩ U`,
`spt T ⊆ N` and `∂T = 0` in `U`, then the associated varifold `V = v(M, θ)` (for any
representation `T = τ(M, θ, ξ)`) is stationary in `N ∩ U` (Ch. 4, 2.6) and has locally bounded
generalized mean curvature in `U` (Ch. 4, 3.14).
*Correction*: `spt T ⊆ N` and `(N̄ \ N) ∩ U = ∅` are implicit in the book (they are part of the
setting of Ch. 4, 2.5–2.6 and of §3); without `spt T ⊆ N` the lemma is false. -/
def MinimizingImpliesStationary : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    T.support ⊆ N → IsMinimizingIn T (N ∩ U) → BoundaryVanishes T →
    ∀ R : IMRep U n, R.Represents T → R.IsStationaryAlong N ∧ R.HasLocallyBoundedMeanCurvature

/-- **Simon 7.2.1 (Lemma, p. 183).**  Let `S ∈ 𝒟_{n−1}(ℝ^{n+ℓ})` be integer multiplicity with
`spt S` compact and `∂S = 0`.  Then there is an integer multiplicity `T ∈ 𝒟ₙ(ℝ^{n+ℓ})` with
`spt T` compact, `∂T = S`, and `M(T) ≤ M(R)` for every integer multiplicity `R` with `spt R`
compact and `∂R = S`.  Here `n = m + 2`: integer multiplicity currents have dimension `≥ 1`
(Ch. 6, §3).  *Correction*: the printed statement omits the conclusion `∂T = S` (proved: `T ∈ 𝓘_S`);
without it `T = 0` would do. -/
def ExistenceOfMinimizingFilling : Prop :=
  ∀ (m ℓ : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid (m + 2 + ℓ))) (m + 1)),
    IsIntegerMultiplicity S → IsCompact S.support → S.boundary = 0 →
    ∃ T : GeometricCurrentOn (univ : Set (Euclid (m + 2 + ℓ))) (m + 2),
      IsIntegerMultiplicity T ∧ IsCompact T.support ∧ T.boundary = S ∧
      ∀ R : GeometricCurrentOn (univ : Set (Euclid (m + 2 + ℓ))) (m + 2),
        IsIntegerMultiplicity R → IsCompact R.support → R.boundary = S → T.mass ≤ R.mass

/-- **Simon 7.2.4 (Theorem, p. 184).**  If `Tⱼ` are minimizing in `U`,
`supⱼ (M_W(Tⱼ) + M_W(∂Tⱼ)) < ∞` for each open `W ⊂⊂ U`, and `Tⱼ ⇀ T ∈ 𝒟ₙ(U)`, then `T` is
(integer multiplicity, Remark 7.2.5(1), and) minimizing in `U`, and `μ_{Tⱼ} → μ_T` as Radon
measures in `U`. -/
def CompactnessOfMinimizingCurrents : Prop :=
  ∀ (n k : ℕ) (U : Set (Euclid (n + k))) (Ts : ℕ → GeometricCurrentOn U n)
      (T : GeometricCurrentOn U n),
    IsOpen U → (∀ j, IsMinimizingIn (Ts j) U) →
    (∀ W : Set (Euclid (n + k)), IsOpen W → CompactlyContained W U →
      ⨆ j, ((Ts j).massOn W + boundaryMassOn (Ts j) W) < ∞) →
    WeaklyConvergesOn Ts T → IsMinimizingIn T U ∧ MassMeasuresConverge (Us := fun _ => U) Ts T

/-- **Simon 7.3.1 (Theorem, p. 187).**  `N` as in 7.1.2 (`C²`).  If `T ∈ 𝒟ₙ(U)` is minimizing in
`U ∩ N` and `spt T ⊆ U ∩ N`, then (1) `Θⁿ(μ_T, x)` exists at every `x ∈ U \ spt ∂T` and is upper
semicontinuous there; (2) for `x ∈ spt T \ spt ∂T` and `λⱼ ↓ 0` (any `λⱼ > 0`, `λⱼ → 0`) there
are a subsequence `λⱼ'` and an integer multiplicity `C ∈ 𝒟ₙ(ℝ^{n+k})`, minimizing in `ℝ^{n+k}`,
with `η_{x,λⱼ'#}T ⇀ C`, `μ_{η_{x,λⱼ'#}T} → μ_C`, `η_{0,λ#}C = C` (`λ > 0`) and
`Θⁿ(μ_C, 0) = Θⁿ(μ_T, x)`.
*Correction*: the printed hypothesis "`x ∈ spt T \ spt ∂T`" and "(1) … everywhere in `U`" are
garbled; the monotonicity proof gives (1) on `U \ spt ∂T`, which is what is stated. -/
def DensityAndTangentCones : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N →
    (∃ Θ : Euclid (n + k) → ℝ, (∀ x ∈ U \ boundarySupport T, HasMassDensity T x (Θ x)) ∧
        UpperSemicontinuousOn Θ (U \ boundarySupport T)) ∧
    ∀ x ∈ T.support \ boundarySupport T, ∀ (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j),
      Tendsto lams atTop (𝓝 0) →
      ∃ (φ : ℕ → ℕ) (C : GeometricCurrentOn (univ : Set (Euclid (n + k))) n), StrictMono φ ∧
        ConvergesWeakly (fun j => blowUp T x (lams (φ j)) (hlams (φ j)).ne') C ∧
        MassMeasuresConverge (fun j => blowUp T x (lams (φ j)) (hlams (φ j)).ne') C ∧
        IsMinimizingIn C univ ∧ IsConeCurrent C ∧
        ∃ θ : ℝ, HasMassDensity T x θ ∧ HasMassDensity C 0 θ

/-- **Simon 7.3.3 (Theorem, p. 189).**  `N` as in 7.3.1.  If `T` is minimizing in `U ∩ N`,
`spt T ⊆ U ∩ N` and `∂T = 0` in `U`, then (1) `Θⁿ(μ_T, x) ∈ ℤ` for all `x ∈ U \ E`, where
`H^{n−3+α}(E) = 0` for all `α > 0`; (2) there is `F ⊇ E` with `H^{n−2+α}(F) = 0` for all `α > 0`
such that `T` has a tangent plane at each `x ∈ spt T \ F`.
*Correction*: printed "`F ⊂ E`" must read `F ⊃ E` (non-integer density excludes tangent planes). -/
def IntegerDensityAndTangentPlanes : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T →
    ∃ E F : Set (Euclid (n + k)), E ⊆ F ∧
      (∀ α : ℝ, 0 < α → μH[(n : ℝ) - 3 + α] E = 0) ∧
      (∀ x ∈ U \ E, ∃ m : ℤ, HasMassDensity T x m) ∧
      (∀ α : ℝ, 0 < α → μH[(n : ℝ) - 2 + α] F = 0) ∧
      ∀ x ∈ T.support \ F, HasTangentPlaneAt T x

/-- **Simon 7.4.2 (Theorem, p. 194).**  If `T ∈ 𝒟ₙ(U)` is integer multiplicity and minimizing in
`U ∩ N` (`N` an embedded `C²` `(n+ℓ)`-submanifold, `(N̄ \ N) ∩ U = ∅`), `spt T ⊆ U ∩ N` and
`∂T = 0` in `U`, then `reg T` is dense in `spt T`. -/
def RegularSetDense : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T →
    T.support ⊆ closure (regularSet T)

/-- **Simon 7.4.3 (Theorem, p. 194)**, for a fixed `N` (`Nᵢ = N`).  Let `Tᵢ, T` be minimizing in
`U ∩ N`, `spt Tᵢ, spt T ⊆ N`, `∂Tᵢ = ∂T = 0` in `U`, `Tᵢ ⇀ T`, with
`supᵢ M_W(Tᵢ) < ∞` for `W ⊂⊂ U`.  If `y ∈ N ∩ U`, `Θⁿ(μ_T, y) = 1`, `y = lim yⱼ`, `yⱼ ∈ spt Tⱼ`,
then `y ∈ reg T` and `yⱼ ∈ reg Tⱼ` for all large `j`.
*Deviations*: the book allows `Nᵢ → N` "in the `C²` sense" (not defined at this point of the
book); we take `Nᵢ = N`.  The local mass bound is the hypothesis of 7.2.4, which the proof uses
for `μ_{Tⱼ} → μ_T`; it is added explicitly. -/
def DensityOneImpliesRegular : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (Ts : ℕ → GeometricCurrentOn U n)
      (T : GeometricCurrentOn U n) (ys : ℕ → Euclid (n + k)) (y : Euclid (n + k)),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    (∀ j, IsMinimizingIn (Ts j) (U ∩ N)) → IsMinimizingIn T (U ∩ N) →
    (∀ j, (Ts j).support ⊆ N) → T.support ⊆ N →
    (∀ j, BoundaryVanishes (Ts j)) → BoundaryVanishes T →
    (∀ W : Set (Euclid (n + k)), IsOpen W → CompactlyContained W U → ⨆ j, (Ts j).massOn W < ∞) →
    WeaklyConvergesOn Ts T → y ∈ N ∩ U → HasMassDensity T y 1 →
    Tendsto ys atTop (𝓝 y) → (∀ j, ys j ∈ (Ts j).support) →
    y ∈ regularSet T ∧ ∀ᶠ j in atTop, ys j ∈ regularSet (Ts j)

/-- **Simon 7.4.4 (Theorem, p. 194).**  If `T` is as in 7.4.2 and `ξ ∈ spt T` has
`Θⁿ(μ_T, ξ) < 2`, then there is `ρ > 0` with `H^{n−2+α}(sing T ∩ B_ρ(ξ)) = 0` for all `α > 0`. -/
def SingularSetSmallWhereDensityBelowTwo : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T →
    ∀ ξ ∈ T.support, ∀ θ : ℝ, HasMassDensity T ξ θ → θ < 2 →
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ α : ℝ, 0 < α → μH[(n : ℝ) - 2 + α] (singularSet T ∩ ball ξ ρ) = 0

/-- **Simon 7.4.5 (Theorem, p. 195).**  If `C ∈ 𝒟ₙ(ℝ^{n+k})` is minimizing in `ℝ^{n+k}`, `∂C = 0`,
`C` is a cone, and `spt C ⊆ H̄` for an open half-space `H = {x : v · x > 0}` (`v ≠ 0`, so
`0 ∈ ∂H`), then `spt C ⊆ ∂H`. -/
def HalfSpaceConeLiesInBoundary : Prop :=
  ∀ (n k : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid (n + k))) n) (v : Euclid (n + k)),
    IsMinimizingIn C univ → BoundaryVanishes C → IsConeCurrent C → v ≠ 0 →
    C.support ⊆ closure {x | 0 < inner ℝ v x} → C.support ⊆ frontier {x | 0 < inner ℝ v x}

/-- **Simon 7.5.8 (Theorem, p. 200).**  Let `N ∈ 𝒪` (oriented by `ξN`), `E ⊆ N ∩ U`
`H^{n+1}`-measurable, `T = ∂[[E]] ∈ 𝒟ₙ(U)` integer multiplicity and minimizing in `N ∩ U`.  Then
`sing T = ∅` if `n ≤ 6`; `sing T` is locally finite in `U` (finite on compact subsets of `U`) if
`n = 7`; `H^{n−7+α}(sing T) = 0` for all `α > 0` if `n > 7`.  (`N = ℝ^{n+1}` is the case `k = 1`.)
-/
def CodimensionOneRegularity : Prop :=
  ∀ (n k : ℕ) (U N E : Set (Euclid (n + k))) (ξN : Euclid (n + k) → MultiVector (n + k) (n + 1))
      (T : GeometricCurrentOn U n),
    IsOpen U → InClassO n U N ξN → MeasurableSet E → E ⊆ N ∩ U → IsBoundaryOfRegion T E ξN →
    IsMinimizingIn T (N ∩ U) →
    (n ≤ 6 → singularSet T = ∅) ∧
    (n = 7 → ∀ K : Set (Euclid (n + k)), IsCompact K → K ⊆ U → (singularSet T ∩ K).Finite) ∧
    (7 < n → ∀ α : ℝ, 0 < α → μH[(n : ℝ) - 7 + α] (singularSet T) = 0)

/-- **Simon 7.5.11 (Corollary, p. 202).**  If `T` is as in 7.5.8, `T = τ(M, θ, ξ)`, and
`T₁ ∈ 𝒟ₙ(U)` is obtained by equipping a connected component `M₁` of `reg T` with multiplicity
`1` and the orientation `ξ` of `T`, then `∂T₁ = 0` in `U` and `T₁` is minimizing in `U ∩ N`. -/
def RegularComponentsAreMinimizing : Prop :=
  ∀ (n k : ℕ) (U N E : Set (Euclid (n + k))) (ξN : Euclid (n + k) → MultiVector (n + k) (n + 1))
      (T : GeometricCurrentOn U n),
    IsOpen U → InClassO n U N ξN → MeasurableSet E → E ⊆ N ∩ U → IsBoundaryOfRegion T E ξN →
    IsMinimizingIn T (N ∩ U) →
    ∀ R : IMRep U n, R.Represents T → ∀ y ∈ regularSet T, ∀ T₁ : GeometricCurrentOn U n,
      (∀ ω : TestFormOn U n, T₁ ω = ∫ x in connectedComponentIn (regularSet T) y,
        R.orient x ((ω : DifferentialForm (Euclid (n + k)) n) x) ∂μHE[n]) →
      BoundaryVanishes T₁ ∧ IsMinimizingIn T₁ (U ∩ N)

end

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `accepted`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_components_are_minimizing-a1`
- Child DAG node: `root.regular_components_are_minimizing-a1.regular_component_structure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 2 ('reg T is relatively open in spt T, and every z ∈ reg T has a ball B_r(z) with spt T ∩ B_r(z) = M' ∩ B_r(z) a connected C¹ graph …; (a) closure(M₁) ∖ M₁ ⊆ sing T; (b) …; on M₁, H^n(M₁ ∖ M) = 0 and ξ orients T_xM₁ a.e.'), Simon 7.4.1 (chapter-07.txt lines 590–612). The parent deduces T₁ = T near M₁ from θ = 1 a.e. (5.2(‡)); here only T₁ = |m_z|⁻¹·T near each z ∈ M₁ is proved, by uniqueness of the representation on a regular sheet, which is all the cut-off argument needs; 5.2(‡) is not used.
Notation: S := spt T = U ∖ Z(T), where Z(T) (zeroRegion) is the union of the open sets with compact closure in U on which T vanishes; Z(T) is open, so S is Borel and closure(S) ∩ U ⊆ S. reg := reg T ⊆ S and sing T = S ∖ reg. For z ∈ reg fix data (ρ_z, m_z, M_z, ξ_z) from the definition: ball(z, ρ_z) ⊆ U, m_z ∈ ℤ ∖ {0}, M_z an embedded C¹ n-submanifold with z ∈ M_z, oriented by ξ_z (continuous on M_z, each ξ_z(x) a unit orientation of T_xM_z), H^n(M_z ∩ K) < ∞ for compact K ⊆ ball(z, ρ_z), and T(ω) = m_z ∫_{M_z} ξ_z(ω) dH^n whenever tsupport ω ⊆ ball(z, ρ_z). For an orthonormal n-frame τ let β_τ ∈ Λ^n be β_τ(v_1, …, v_n) := det(⟨τ_i, v_j⟩) (the wedge of the covectors ⟨τ_i, ·⟩; SimonGMT Chapter06.wedgeCovectors_apply_det), so β_τ(τ) = 1; a unit orientation ε·ev_τ (ε = ±1, ev_τ(α) = α(τ)) satisfies |ε ev_τ(α)| ≤ ‖α‖ for all α and ε ev_τ(ε β_τ) = 1; in particular it is nonzero.

1. (Facts on an embedded C¹ n-submanifold M with a chart (V, W, ψ) at x ∈ M: V ⊆ ℝ^n and W ⊆ ℝ^P open, x ∈ W, ψ C¹ and injective on V with injective differential, ψ(V) = W ∩ M, and V ∩ ψ⁻¹(K) compact for every compact K ⊆ W.)
 (F1) ψ : V → W ∩ M is a homeomorphism, W ∩ M is relatively closed in W, and closure(M) ∩ W = M ∩ W. Proof: let F ⊆ V be relatively closed and let w ∈ W be a limit of ψ(f_j), f_j ∈ F. K := {ψ(f_j)} ∪ {w} is a compact subset of W, so the f_j lie in the compact set V ∩ ψ⁻¹(K); a subsequence converges to some v ∈ V; then v ∈ F and ψ(v) = w by continuity. So ψ maps relatively closed subsets of V to relatively closed subsets of W; with F = V, W ∩ M is relatively closed in W, and a continuous closed bijection V → W ∩ M is a homeomorphism. If x' ∈ closure(M) ∩ W, points of M converging to x' eventually lie in the open set W, so x' ∈ closure(W ∩ M) ∩ W = W ∩ M.
 (F2) H^n(ψ(B)) > 0 for every nonempty open B ⊆ V. Proof: fix v ∈ B, let L := Dψ(v) (injective), p the orthogonal projection onto L(ℝ^n), and Π := L⁻¹ ∘ p : ℝ^P → ℝ^n (linear, Lipschitz with constant ‖Π‖). Π ∘ ψ is C¹ near v with D(Π ∘ ψ)(v) = Id, so by the inverse function theorem it maps some open B' ⊆ B containing v onto a nonempty open set O ⊆ ℝ^n. Then 0 < L^n(O) = H^n(O) = H^n(Π(ψ(B'))) ≤ ‖Π‖^n H^n(ψ(B')) ≤ ‖Π‖^n H^n(ψ(B)). (μHE[n] = c_n·μH[n] with a constant c_n ∈ (0, ∞) depending only on n, so the Lipschitz image bound μH[n](Π(A)) ≤ Lip(Π)^n μH[n](A) (Mathlib LipschitzWith.hausdorffMeasure_image_le) carries over to H^n = μHE[n]; on ℝ^n, μHE[n] is Lebesgue measure, which is positive on nonempty open sets.)
 (F3) M is Borel: each x ∈ M has a chart set W_x with W_x ∩ M relatively closed in W_x (F1); countably many W_{x_i} cover M (Lindelöf), and M = ⋃_i (W_{x_i} ∩ closure(W_{x_i} ∩ M)).

2. (Local sheets.) For every z ∈ reg there is an open O_z with z ∈ O_z ⊆ ball(z, ρ_z) such that (a) S ∩ O_z = M_z ∩ O_z, (b) M_z ∩ O_z is connected, (c) S ∩ O_z ⊆ reg. Write ρ, m, M, ξ' for ρ_z, m_z, M_z, ξ_z.
 2.1 (S ∩ ball(z, ρ) ⊆ closure(M).) If x ∈ ball(z, ρ) ∖ closure(M), pick s > 0 with closedBall(x, s) ⊆ ball(z, ρ) ∖ closure(M). For tsupport ω ⊆ ball(x, s), T(ω) = m ∫_M ξ'(ω) dH^n = 0 since ω vanishes on M. So ball(x, s) (open, with compact closure in U) is a region where T vanishes: x ∈ Z(T), x ∉ S.
 2.2 (M ∩ ball(z, ρ) ⊆ S.) Let x ∈ M ∩ ball(z, ρ) and suppose x ∉ S; as x ∈ U, x ∈ Z(T), so T vanishes on some open W' ∋ x. Write ξ'(x) = ε ev_{τ'} and β := ε β_{τ'}, so ξ'(x)(β) = 1; by continuity of ξ' on M there is s > 0 with ξ'(x')(β) > 1/2 for all x' ∈ M ∩ ball(x, s). Take a chart (V_x, W_x, ψ_x) of M at x and O := ball(x, s) ∩ W' ∩ ball(z, ρ) ∩ W_x (open, x ∈ O). Let g ∈ C_c^∞(ℝ^P) with tsupport g ⊆ O, g ≥ 0, g(x) > 0, and ω := g β ∈ 𝒟^n(U). Then T(ω) = 0 because tsupport ω ⊆ W'. On the other hand V_x ∩ ψ_x⁻¹(O ∩ {g > 0}) is an open neighbourhood of ψ_x⁻¹(x) in ℝ^n (ψ_x is continuous on the open set V_x), so it contains a nonempty open ball B, and ψ_x(B) ⊆ M ∩ O ∩ {g > 0} has H^n(ψ_x(B)) > 0 by (F2). The integrand g ξ'(β) is ≥ 0 on M (g = 0 off ball(x, s)), > 0 on ψ_x(B), and integrable for H^n⌞M (bounded, vanishing off tsupport g, and H^n(M ∩ tsupport g) < ∞); M is Borel (F3), so the integral of a nonnegative integrable function that is positive on a set of positive measure is positive (Mathlib integral_pos_iff_support_of_nonneg_ae). Hence T(ω) = m ∫_M g ξ'(β) dH^n ≠ 0, a contradiction.
 2.3 (Construction of O_z.) Let (V, W, ψ) be a chart of M at z and v₀ := ψ⁻¹(z). Choose t > 0 with ball(v₀, t) ⊆ V and ψ(ball(v₀, t)) ⊆ ball(z, ρ). By (F1), ψ(ball(v₀, t)) is relatively open in W ∩ M, i.e. ψ(ball(v₀, t)) = O'' ∩ W ∩ M for some open O''. Put O_z := O'' ∩ W ∩ ball(z, ρ), an open set containing z. Then M ∩ O_z = ψ(ball(v₀, t)), the continuous image of a ball, hence connected: (b). By 2.1 and (F1), S ∩ O_z ⊆ closure(M) ∩ W ∩ O_z = M ∩ O_z, and M ∩ O_z ⊆ S by 2.2: (a).
 2.4 ((c).) Let x ∈ S ∩ O_z = M ∩ O_z and ρ' := ρ − |x − z| > 0. Then ball(x, ρ') ⊆ ball(z, ρ) ⊆ U, x ∈ M, and the same m, M, ξ' satisfy the local finiteness and representation requirements on ball(x, ρ') (compact subsets of ball(x, ρ') lie in ball(z, ρ), and forms supported in ball(x, ρ') are supported in ball(z, ρ)). Together with x ∈ S this gives x ∈ reg.

3. (Topology of M₁; (i), (iii), (iv).)
 3.1 If z ∈ M₁, then reg ∩ O_z = S ∩ O_z = M_z ∩ O_z (by 2(c), reg ⊆ S and 2(a)) is connected and contains z, so it is contained in the connected component of reg through z, which is M₁. Hence M₁ ∩ O_z = S ∩ O_z = M_z ∩ O_z.
 3.2 (i) With O := ⋃_{z ∈ M₁} O_z (open), M₁ = S ∩ O: '⊆' because z ∈ O_z and M₁ ⊆ S, '⊇' by 3.1. As S is Borel, M₁ is Borel.
 3.3 (iv) With O' := ⋃_{z ∈ reg} O_z, reg = S ∩ O' by 2(c); so sing T = S ∖ O' = U ∖ (Z(T) ∪ O'). For compact K ⊆ U, sing T ∩ K = K ∖ (Z(T) ∪ O') is a closed subset of K, hence compact.
 3.4 (iii) Let x ∈ closure(M₁) ∩ U. Then x ∈ closure(S) ∩ U ⊆ S. If x ∈ reg, the open set O_x meets M₁; reg ∩ O_x is connected (2(a), 2(b), 2(c)), contains x and meets M₁, so M₁ ∪ (reg ∩ O_x) is a connected subset of reg containing y; hence it is contained in M₁ and x ∈ M₁. Otherwise x ∈ S ∖ reg = sing T.

4. (Identification of R on a sheet.) Fix z ∈ M₁, write m, M, ξ', ρ for its data and G := O_z ⊆ ball(z, ρ). Claim: (B) H^n((M ∖ C) ∩ G) = 0; (C) for H^n-a.e. x ∈ C ∩ M ∩ G, θ(x) = |m| and ξ(x) = sign(m) ξ'(x). (The symmetric statement H^n((C ∖ M) ∩ G) = 0 also follows from F = 0 below, but is not needed.)
 Let ν := H^n⌞((C ∪ M) ∩ G) and F(x) := θ(x) 1_C(x) ξ(x) − m 1_M(x) ξ'(x) ∈ Λ_n = (Λ^n)*. M is Borel (F3), ξ' is continuous on M and ξ is a.e. strongly measurable on C, so for each α ∈ Λ^n the function x ↦ F(x)(α) is ν-a.e. strongly measurable; moreover |F(x)(α)| ≤ (θ(x) 1_C(x) + |m| 1_M(x)) ‖α‖ ν-a.e., which is ν-integrable on every compact K ⊆ G (∫_{C∩K} θ dH^n < ∞, and H^n(M ∩ K) < ∞ since K ⊆ ball(z, ρ)). For g ∈ C_c^∞(ℝ^P) with tsupport g ⊆ G and α ∈ Λ^n, ω := g α ∈ 𝒟^n(U) has tsupport ω ⊆ G ⊆ ball(z, ρ), hence ∫ g(x) F(x)(α) dν(x) = ∫_C θ ξ(ω) dH^n − m ∫_M ξ'(ω) dH^n = T(ω) − T(ω) = 0. By the fundamental lemma of the calculus of variations on the open set G (Mathlib IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero), F(x)(α) = 0 for ν-a.e. x ∈ G; letting α run through a finite basis of Λ^n, F(x) = 0 for ν-a.e. x ∈ G.
 (B) For H^n-a.e. x ∈ (M ∖ C) ∩ G, m ξ'(x) = 0, impossible since m ≠ 0 and ξ'(x) ≠ 0 for every x ∈ M. Hence H^n((M ∖ C) ∩ G) = 0. (C) For H^n-a.e. x ∈ C ∩ M ∩ G, θ(x) ξ(x) = m ξ'(x), where ξ(x) = ε₁ ev_τ and ξ'(x) = ε₂ ev_{τ'} for orthonormal n-frames τ, τ' and ε₁, ε₂ ∈ {1, −1}. With B_{ij} := ⟨τ_i, τ'_j⟩, β_τ(τ') = det B and β_{τ'}(τ) = det Bᵀ = det B. Evaluating at β_τ and at β_{τ'} gives θ ε₁ = m ε₂ det B and θ ε₁ det B = m ε₂. Hence θ = |m| |det B| and |m| = θ |det B|, so θ = θ (det B)²; as θ ≥ 1, (det B)² = 1 and θ = |m|. Then ξ(x) = (m/θ) ξ'(x) = sign(m) ξ'(x).

5. ((v) and (ii).) (v): for z ∈ M₁ take G := O_z and c := 1/|m_z|. If tsupport ω ⊆ G then, by 3.1 (M₁ ∩ G = M_z ∩ G), (B), (C) and the local representation of T on ball(z, ρ_z) ⊇ G: T₁(ω) = ∫_{M₁∩G} ξ(ω) dH^n = ∫_{M_z∩G} ξ(ω) dH^n = sign(m_z) ∫_{M_z} ξ_z(ω) dH^n = (sign(m_z)/m_z) T(ω) = c·T(ω). Here the integrand of T₁(ω) vanishes off G (ω = 0 there) and, by (B) and (C), coincides H^n-a.e. on M₁ ∩ G = M_z ∩ G with sign(m_z) ξ_z(ω), which is continuous on M_z, bounded, and vanishes off tsupport ω (a compact subset of ball(z, ρ_z), meeting M_z in a set of finite H^n-measure); so all integrals are absolutely convergent and the equalities hold. (ii): M₁ ⊆ ⋃_{z ∈ M₁} O_z, and by the Lindelöf property of ℝ^P there are z_1, z_2, … ∈ M₁ with M₁ ⊆ ⋃_i O_{z_i}. Then M₁ ∖ C ⊆ ⋃_i ((M₁ ∩ O_{z_i}) ∖ C) = ⋃_i ((M_{z_i} ∩ O_{z_i}) ∖ C), and each of these sets is H^n-null by (B); hence H^n(M₁ ∖ C) = 0.

## Key steps

1. Charts of embedded C¹ submanifolds are homeomorphisms onto relatively closed pieces, and nonempty open pieces have positive H^n-measure.
2. Every z ∈ reg T has an open O_z with spt T ∩ O_z = M_z ∩ O_z connected and contained in reg T; hence M₁ is relatively open in spt T and Borel, its frontier in U lies in sing T, and sing T is relatively closed in U.
3. Uniqueness of the representation on O_z (fundamental lemma for H^n⌞((C ∪ M_z) ∩ O_z), normalised by determinant covectors) gives M_z ⊆ C a.e., θ = |m_z| and ξ = sign(m_z)ξ_z a.e. there.
4. Hence T₁ = |m_z|⁻¹·T on O_z, and H^n(M₁ ∖ C) = 0 by a countable subcover.

## Reference use

### local-project

Queries:
- `cmp .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `python3 summary of lean_name fields in dag.json; grep -rl regcomp_ in the run directory (no match)`
- `grep -n 'def GeometricCurrentOn.massOn|massAdmissibleOn|covectorEuclideanNorm' simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `grep -n 'GeometricCurrentOn.support|zeroRegion|restrictDomain' simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `grep -n '^theorem|^def' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (CountablyRectifiable, HasApproximateTangentSpaceAt, HasApproximateTangentSpaceAt.unique, CountablyRectifiable.mono, countablyRectifiable_iUnion, aemeasurable_starProjection_of_approximateTangentField)`
- `grep -rn 'simon_theorem_3_6|simon_remark_3_7' simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `grep -n 'wedgeCovectors_apply_det' simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `grep -n '^theorem|^def' simongmt/Poincare/SimonGMT/Chapter04/MeanCurvature.lean (exp_normalizedBallMass_monotoneOn and the sign-convention remark)`
- `read simongmt/Poincare/SimonGMT/Chapter07/Basic.lean (minimizing_summands, minimizing_summands_source)`
- `grep -rln 'Cauchy-Binet|CauchyBinet|cauchyBinet|cauchy_binet' Mathlib (no match)`
- `grep -rn 'IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero|nullSingletonClass_hausdorff|hausdorffMeasure_zero_singleton|Set.Finite.measure_zero|exists_isSubordinate|hausdorffMeasure_image_le|integral_pos_iff_support_of_nonneg_ae|norm_integral_le_lintegral_norm|norm_alternatizeUncurryFin_le|withDensity_apply|setLIntegral_mono|ae_tendsto_measure_inter_div' Mathlib`
- `grep -n 'μHE\[|euclideanHausdorffMeasure' Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `lake build GMT.Ch07.Submission in scratch copy /tmp/regcomp-proj; lake env lean /tmp/regcomp-proj/Check.lean (nine child types + conditional parent assembly + #print axioms)`
- `lake env lean /tmp/regcomp-proj/Axioms.lean (#print axioms of reused SimonGMT lemmas)`
- `lake env lean /tmp/regcomp-proj/Inst.lean (#synth Norm (Covector (Euclid 3) 2); #synth Sub (GeometricCurrentOn univ 2))`
- `grep -n for book line ranges: chapter-07.txt (1.4, 4.1, 5.1–5.2, 5.11), chapter-06.txt (3.1, 3.2), chapter-04.txt (3.1–3.17), chapter-03.txt (1.5, 1.6), chapter-01.txt (3.6, 3.7)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/MeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter07/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/NullSingletonClass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-07-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/tmp/regcomp-proj/Check.lean`
- `/tmp/regcomp-proj/Axioms.lean`
- `/tmp/regcomp-proj/Inst.lean`

The snapshot contract (project b4d606d, mathlib 25730c7c) is byte-identical to the workspace Submission.lean, and the DAG reserves no regcomp_ names. The children cite these library facts, all using only propext, Classical.choice and Quot.sound: SimonGMT Chapter01.simon_theorem_3_6 and simon_remark_3_7_of_openSigmaFinite (Upper Density Theorem, for approx_tangent_locality); Chapter06.wedgeCovectors_apply_det (determinant covectors, used for the normalisations); Chapter03.HasApproximateTangentSpaceAt.unique, CountablyRectifiable.mono and countablyRectifiable_iUnion; and Chapter07.minimizing_summands_source (the 1.4 chain over abstract groups). That chain cannot be instantiated directly, because the contract gives GeometricCurrentOn no AddCommGroup instance, so minimizing_summand restates it. SimonGMT's monotonicity (Chapter04 RectifiableVarifold.HasGeneralizedMeanCurvatureIn.exp_normalizedBallMass_monotoneOn) is stated for its own varifold structure, which assumes a measurable tangent projection. monotonicity_mass_bound therefore proves the bound for IMRep directly, including measurability of the tangential divergence. From Mathlib the children use: IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (needs only LocallyIntegrableOn), SmoothPartitionOfUnity.exists_isSubordinate, nullSingletonClass_hausdorff, hausdorffMeasure_zero_singleton, μHE[0] = μH[0], LipschitzWith.hausdorffMeasure_image_le and norm_alternatizeUncurryFin_le. The search found no Cauchy–Binet theorem in Mathlib, so the multilinear arguments use slotwise Parseval and determinant covectors instead. All nine child types elaborate after import GMT.Ch07.Submission. The conditional assembly of RegularComponentsAreMinimizing from them, MinimizingImpliesStationary and CodimensionOneRegularity compiles, using the standard axioms plus sorryAx from the child stubs only.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
