<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.cone_splitting-a1.translation_invariance-a1.translate_derivative-a1 -->

## Theorem `Submission.dimred_cs_ti_translate_action_hasDerivAt`

Let P, n ∈ ℕ, R = (M, θ, ξ) ∈ IMRep(ℝ^P, n) (M = R.carrier, θ = R.mult, ξ = R.orient), ω ∈ 𝒟ⁿ(ℝ^P) (TestFormOn univ n), v ∈ ℝ^P and t ∈ ℝ. For s ∈ ℝ put G(s) := R.action(y ↦ ω(s·v + y)) = ∫_M θ(y)·ξ(y)(ω(sv + y)) dHⁿ(y). Then G has derivative R.action(y ↦ Dω(t·v + y)[v]) at t (HasDerivAt), where Dω(z)[u] = fderiv ℝ ω z u.

Node: `root.dimension_reduction_results-a1.cone_splitting-a1.translation_invariance-a1.translate_derivative-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4233

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1062

Decomposition children: None

## Lean problem

Declaration: `Submission.dimred_cs_ti_translate_action_hasDerivAt`

```lean
∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n) (ω : TestFormOn (univ : Set (Euclid P)) n) (v : Euclid P) (t : ℝ), HasDerivAt (fun s : ℝ => R.action (fun y => (ω : DifferentialForm (Euclid P) n) (s • v + y))) (R.action (fun y => fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • v + y) v)) t
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

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.translation_invariance-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.translation_invariance-a1.translate_derivative-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 3 of the parent proof (Derivative along the translation: 'for s in a bounded interval the integrand and its s-derivative θξ(y)(Dω(sv + y)[v]) vanish outside a fixed compact set and are bounded by Cθ (‖ξ(y)‖ ≤ 1 for Hⁿ-a.e. y ∈ M by … unit_orientation_norm_le_one), which is integrable there; so G is differentiable with G'(s) = S(Dβ_s(·)[v])'), written for the representing triple; Dβ_t(y)[v] = Dω(tv + y)[v]. It is the translation counterpart of the accepted Submission.dtc_cwv_scaled_action_hasDerivAt. Notation: ν := Hⁿ⌞M = μHE[n].restrict M, so R.action φ = ∫ θ(y)·ξ(y)(φ(y)) dν(y) for every form φ; norms on covectors and multivectors are operator norms.

1. (Orientation bound.) By R.orients, for ν-a.e. y there is a subspace Q with IsUnitOrientationOf (ξ(y)) Q; by the sibling orientation_norm, ‖ξ(y)‖ ≤ 1. Hence for ν-a.e. y and every n-covector α, |ξ(y)(α)| ≤ ‖ξ(y)‖·‖α‖ ≤ ‖α‖.
2. (Data from ω.) ω is C^∞ with compact support, so ω and Dω are continuous, and ω(z) = 0, Dω(z) = 0 whenever z ∉ tsupport ω (tsupport Dω ⊆ tsupport ω, Mathlib tsupport_fderiv_subset). Choose r ∈ ℝ with tsupport ω ⊆ B̄_r(0) (a compact set is bounded) and K₀ with ‖ω(z)‖ ≤ K₀ for every z (continuous with compact support); then K₀ ≥ ‖ω(0)‖ ≥ 0.
3. (Integrands.) For s ∈ ℝ and y ∈ ℝ^P put Ψ(s, y) := Dω(sv + y)[v], F(s, y) := θ(y)·ξ(y)(ω(sv + y)) and F'(s, y) := θ(y)·ξ(y)(Ψ(s, y)). Then G(s) = ∫ F(s, ·) dν, and the claimed derivative is ∫ F'(t, ·) dν = R.action(y ↦ Ψ(t, y)).
4. (Pointwise derivative.) Fix y. The map s ↦ sv + y has derivative v; ω is differentiable, so by the chain rule s ↦ ω(sv + y) has derivative Dω(sv + y)[v] = Ψ(s, y). Composing with the continuous linear functional ξ(y) and multiplying by the constant θ(y), s ↦ F(s, y) has derivative F'(s, y) at every s, for every y.
5. (Measurability.) θ is measurable (R.measurable_mult composed with ℕ → ℝ) and ξ is AEStronglyMeasurable for ν (R.aestronglyMeasurable_orient). The map (s, y) ↦ Ψ(s, y) is jointly continuous (Dω is continuous, (s, y) ↦ sv + y is continuous, and evaluation at the constant v is continuous), and y ↦ ω(sv + y) is continuous for each s. The evaluation (ζ, α) ↦ ζ(α) is continuous on MultiVector P n × Covector (Euclid P) n, so y ↦ ξ(y)(φ(y)) is AEStronglyMeasurable for ν for every continuous φ; multiplying by θ, F(s, ·) (each s) and F'(t, ·) are AEStronglyMeasurable for ν.
6. (Localization.) Let I := (t − 1, t + 1), an open neighbourhood of t, ρ := r + (|t| + 1)‖v‖ and B := B̄_ρ(0) (compact and measurable). For s ∈ [t − 1, t + 1], |s| ≤ |t| + 1. If |s| ≤ |t| + 1 and sv + y ∈ tsupport ω, then ‖sv + y‖ ≤ r and ‖y‖ ≤ ‖sv + y‖ + ‖sv‖ ≤ r + |s|·‖v‖ ≤ ρ, i.e. y ∈ B. If sv + y ∉ tsupport ω, then ω(sv + y) = 0 and Dω(sv + y) = 0 by step 2, so F(s, y) = F'(s, y) = 0.
7. (Uniform bound.) Ψ is continuous on the compact set [t − 1, t + 1] × B, so there is K with ‖Ψ(s, y)‖ ≤ K for (s, y) ∈ [t − 1, t + 1] × B. Let g(y) := K·θ(y)·1_B(y). For ν-a.e. y (those of step 1) and every s ∈ I: if sv + y ∈ tsupport ω, then y ∈ B by step 6 and |F'(s, y)| ≤ θ(y)·‖ξ(y)‖·‖Ψ(s, y)‖ ≤ θ(y)·1·K = g(y); otherwise F'(s, y) = 0 ≤ g(y), since g(y) = 0 if y ∉ B, and if y ∈ B then K ≥ ‖Ψ(t, y)‖ ≥ 0.
8. (Integrability.) B is compact and B ⊆ univ, so R.locallyIntegrable_mult gives ∫_{M∩B} θ dHⁿ < ∞; as θ is measurable, θ·1_B is ν-integrable, hence so is g. Moreover |F(t, y)| ≤ K₀·θ(y)·1_B(y) for ν-a.e. y: if tv + y ∈ tsupport ω then y ∈ B (step 6 with s = t) and |F(t, y)| ≤ θ(y)·1·K₀; otherwise F(t, y) = 0 ≤ K₀θ(y)1_B(y). So F(t, ·) is ν-integrable.
9. (Conclusion.) The dominated differentiation theorem (Mathlib hasDerivAt_integral_of_dominated_loc_of_deriv_le, with the neighbourhood I of t) applies: F(s, ·) is AEStronglyMeasurable for s near t (step 5); F(t, ·) is integrable (step 8); F'(t, ·) is AEStronglyMeasurable (step 5); |F'(s, y)| ≤ g(y) for ν-a.e. y and all s ∈ I, with g integrable (steps 7–8); and s ↦ F(s, y) has derivative F'(s, y) on I for every y (step 4). Hence G(s) = ∫ F(s, ·) dν has derivative ∫ F'(t, ·) dν = R.action(y ↦ Dω(tv + y)[v]) at t. ∎

Implementation note (not part of the numbered proof).
- The Lean proof below of exactly this frozen type was kernel-checked during this decomposition: Lean v4.35.0-rc3, Mathlib 25730c7c, after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's opens (`open Filter Function Set MeasureTheory Metric`, `open scoped ENNReal Topology`, `open Poincare.SimonGMT.Chapter06`, `open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt)`), like the accepted Submission theorems. #print axioms gives propext, Classical.choice, Quot.sound. It was also checked in isolation with only the listed sibling dependencies present (as stubs), and through the comparator's own NodeSolution wrapper (`exact Submission.X`).
- Do not put `open scoped ContDiff` in front of the declaration (it makes `ω` a reserved token); write the smoothness order as `(⊤ : ℕ∞)`, not `∞` (with `open scoped ENNReal`, `∞` is the ENNReal top).
- Bound the jointly continuous covector-valued Ψ on the compact set as in step 7 (`IsCompact.exists_bound_of_continuousOn`); applying `Continuous.bounded_above_of_compact_support` to the CLM-valued `fderiv ℝ ω` hits a deterministic whnf timeout (recorded by the accepted dilation analogue). `Continuous.bounded_above_of_compact_support` is used only for the covector-valued ω (step 2).
- The sibling orientation_norm is `Submission.unit_orientation_norm_le_one`.
```lean
/-- Differentiation under the integral sign for the translations `y ↦ sv + y`: for every `t`,
`s ↦ τ(M, θ, ξ)(ω(sv + ·))` has derivative `τ(M, θ, ξ)(Dω(tv + ·)[v])` at `t`.  For
`s ∈ (t − 1, t + 1)` the integrands vanish off `B = B̄_ρ(0)`, `ρ = r + (|t| + 1)‖v‖` where
`spt ω ⊆ B̄_r(0)`, and are dominated by `K θ 1_B`, `K` bounding the continuous map
`(s, y) ↦ Dω(sv + y)[v]` on `[t − 1, t + 1] × B` (as `‖ξ‖ ≤ 1` a.e.); `θ 1_B` is integrable since
`θ` is locally `Hⁿ`-integrable. -/
theorem Submission.dimred_cs_ti_translate_action_hasDerivAt : ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n) (ω : TestFormOn (univ : Set (Euclid P)) n) (v : Euclid P) (t : ℝ), HasDerivAt (fun s : ℝ => R.action (fun y => (ω : DifferentialForm (Euclid P) n) (s • v + y))) (R.action (fun y => fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • v + y) v)) t := by
  intro P n R ω v t
  have hws : ContDiff ℝ (⊤ : ℕ∞) (ω : DifferentialForm (Euclid P) n) := ω.property.1.1
  have hwc : HasCompactSupport (ω : DifferentialForm (Euclid P) n) := ω.property.1.2
  set w : DifferentialForm (Euclid P) n := (ω : DifferentialForm (Euclid P) n) with hw_def
  -- Step 1: `‖ξ(x)‖ ≤ 1` for `Hⁿ⌞M`-a.e. `x`
  have hξ : ∀ᵐ x ∂(μHE[n].restrict R.carrier), ‖R.orient x‖ ≤ 1 := by
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact Submission.unit_orientation_norm_le_one P n Q _ hQ
  -- Step 2: a support radius `r` and a bound `K0` for `ω`; `ω` and `Dω` vanish off `spt ω`
  have hwcont : Continuous w := hws.continuous
  have hDw : Continuous (fderiv ℝ w) := hws.continuous_fderiv (by simp)
  obtain ⟨K0, hK0⟩ := hwcont.bounded_above_of_compact_support hwc
  obtain ⟨r, hr⟩ : ∃ r, tsupport w ⊆ closedBall (0 : Euclid P) r :=
    hwc.isCompact.isBounded.subset_closedBall 0
  have hvan : ∀ z, z ∉ tsupport w → w z = 0 ∧ fderiv ℝ w z = 0 := fun z hz =>
    ⟨image_eq_zero_of_notMem_tsupport hz,
      image_eq_zero_of_notMem_tsupport (fun h => hz (tsupport_fderiv_subset ℝ h))⟩
  -- Step 3: measurability of the integrands
  have hθm : Measurable fun x => (R.mult x : ℝ) := measurable_from_nat.comp R.measurable_mult
  have happly : Continuous fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2 :=
    continuous_fst.clm_apply continuous_snd
  have hmeas : ∀ φ : Euclid P → Covector (Euclid P) n, Continuous φ →
      AEStronglyMeasurable (fun y => (R.mult y : ℝ) * R.orient y (φ y))
        (μHE[n].restrict R.carrier) :=
    fun φ hφ => hθm.aestronglyMeasurable.mul
      (happly.comp_aestronglyMeasurable
        (R.aestronglyMeasurable_orient.prodMk hφ.aestronglyMeasurable))
  have hcF : ∀ s : ℝ, Continuous (fun y => w (s • v + y)) := fun s =>
    hwcont.comp (continuous_const.add continuous_id)
  have hΦ : Continuous (fun p : ℝ × Euclid P => fderiv ℝ w (p.1 • v + p.2) v) := by
    have hsy : Continuous (fun p : ℝ × Euclid P => p.1 • v + p.2) :=
      (continuous_fst.smul continuous_const).add continuous_snd
    exact (hDw.comp hsy).clm_apply continuous_const
  have hcF' : ∀ s : ℝ, Continuous (fun y => fderiv ℝ w (s • v + y) v) := fun s =>
    hΦ.comp (continuous_const.prodMk continuous_id)
  -- Step 4: localization in `B = B̄_ρ(0)`, `ρ = r + (|t| + 1)‖v‖`; the bound `K` of `Dω(sv+y)[v]`
  set ρ : ℝ := r + (|t| + 1) * ‖v‖ with hρ
  set B : Set (Euclid P) := closedBall (0 : Euclid P) ρ with hB
  have hBm : MeasurableSet B := measurableSet_closedBall
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := t - 1) (b := t + 1)).prod
    (isCompact_closedBall (0 : Euclid P) ρ) |>.exists_bound_of_continuousOn hΦ.continuousOn
  have hθB : IntegrableOn (fun x => (R.mult x : ℝ)) B (μHE[n].restrict R.carrier) := by
    refine ⟨hθm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, Measure.restrict_restrict hBm, inter_comm]
    simpa only [Real.enorm_natCast] using
      (R.locallyIntegrable_mult B (isCompact_closedBall 0 ρ) (subset_univ _)).lt_top
  -- if `|s| ≤ |t| + 1` and `s v + y ∈ spt ω` then `y ∈ B`
  have hmemB : ∀ s : ℝ, |s| ≤ |t| + 1 → ∀ y : Euclid P, s • v + y ∈ tsupport w → y ∈ B := by
    intro s hs y hy
    have h1 : ‖s • v + y‖ ≤ r := by simpa using hr hy
    have h2 := norm_sub_le (s • v + y) (s • v)
    rw [add_sub_cancel_left] at h2
    have h3 : ‖s • v‖ ≤ (|t| + 1) * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hs (norm_nonneg v)
    simp only [hB, mem_closedBall, dist_zero_right, hρ]
    linarith
  have habs : ∀ s ∈ Icc (t - 1) (t + 1), |s| ≤ |t| + 1 := by
    intro s hs
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2, neg_abs_le t, le_abs_self t]
  -- Step 5: hypotheses of the dominated differentiation theorem
  have hs : Ioo (t - 1) (t + 1) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hF_meas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable
      (fun y => (R.mult y : ℝ) * R.orient y (w (s • v + y))) (μHE[n].restrict R.carrier) :=
    Eventually.of_forall fun s => hmeas _ (hcF s)
  have hF'_meas : AEStronglyMeasurable (fun y => (R.mult y : ℝ) * R.orient y
      (fderiv ℝ w (t • v + y) v)) (μHE[n].restrict R.carrier) := hmeas _ (hcF' t)
  have hF_int : Integrable (fun y => (R.mult y : ℝ) * R.orient y (w (t • v + y)))
      (μHE[n].restrict R.carrier) := by
    refine ((hθB.integrable_indicator hBm).const_mul K0).mono' (hmeas _ (hcF t)) ?_
    filter_upwards [hξ] with y hy
    by_cases hty : t • v + y ∈ tsupport w
    · have hyB := hmemB t (by linarith [abs_nonneg t]) y hty
      rw [indicator_of_mem hyB, norm_mul, Real.norm_natCast]
      calc (R.mult y : ℝ) * ‖R.orient y (w (t • v + y))‖
          ≤ (R.mult y : ℝ) * (‖R.orient y‖ * ‖w (t • v + y)‖) := by
            gcongr; exact (R.orient y).le_opNorm _
        _ ≤ (R.mult y : ℝ) * (1 * K0) := by
            gcongr
            exact hK0 _
        _ = K0 * (R.mult y : ℝ) := by ring
    · rw [(hvan _ hty).1, map_zero, mul_zero, norm_zero]
      have hK0n : 0 ≤ K0 := le_trans (norm_nonneg _) (hK0 0)
      by_cases hyB : y ∈ B
      · rw [indicator_of_mem hyB]; positivity
      · rw [indicator_of_notMem hyB, mul_zero]
  have h_bound : ∀ᵐ y ∂(μHE[n].restrict R.carrier), ∀ s ∈ Ioo (t - 1) (t + 1),
      ‖(R.mult y : ℝ) * R.orient y (fderiv ℝ w (s • v + y) v)‖ ≤
        K * B.indicator (fun x => (R.mult x : ℝ)) y := by
    filter_upwards [hξ] with y hy s hs
    by_cases hsy : s • v + y ∈ tsupport w
    · have hyB := hmemB s (habs s (Ioo_subset_Icc_self hs)) y hsy
      rw [indicator_of_mem hyB, norm_mul, Real.norm_natCast]
      have hnorm := hK (s, y) ⟨Ioo_subset_Icc_self hs, hyB⟩
      calc (R.mult y : ℝ) * ‖R.orient y (fderiv ℝ w (s • v + y) v)‖
          ≤ (R.mult y : ℝ) * (‖R.orient y‖ * ‖fderiv ℝ w (s • v + y) v‖) := by
            gcongr; exact (R.orient y).le_opNorm _
        _ ≤ (R.mult y : ℝ) * (1 * K) := by gcongr
        _ = K * (R.mult y : ℝ) := by ring
    · rw [(hvan _ hsy).2, zero_apply, map_zero, mul_zero, norm_zero]
      by_cases hyB : y ∈ B
      · rw [indicator_of_mem hyB]
        have hKn : 0 ≤ K := le_trans (norm_nonneg _)
          (hK (t, y) ⟨⟨by linarith, by linarith⟩, hyB⟩)
        positivity
      · rw [indicator_of_notMem hyB, mul_zero]
  have h_diff : ∀ᵐ y ∂(μHE[n].restrict R.carrier), ∀ s ∈ Ioo (t - 1) (t + 1),
      HasDerivAt (fun s => (R.mult y : ℝ) * R.orient y (w (s • v + y)))
        ((R.mult y : ℝ) * R.orient y (fderiv ℝ w (s • v + y) v)) s := by
    refine Eventually.of_forall fun y s _ => ?_
    have h1 : HasDerivAt (fun s : ℝ => s • v + y) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).add_const y
    have h2 : HasDerivAt (fun s : ℝ => w (s • v + y)) (fderiv ℝ w (s • v + y) v) s :=
      ((hws.differentiable (by simp)).differentiableAt (x := s • v + y)).hasFDerivAt.comp_hasDerivAt
        s h1
    exact ((R.orient y).hasFDerivAt.comp_hasDerivAt s h2).const_mul (R.mult y : ℝ)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int hF'_meas h_bound
    ((hθB.integrable_indicator hBm).const_mul K) h_diff
  exact key.2
```

## Key steps

1. ‖ξ‖ ≤ 1 Hⁿ⌞M-a.e. (orientation_norm); ω, Dω continuous, vanishing off tsupport ω ⊆ B̄_r(0); ‖ω‖ ≤ K₀.
2. For each y, s ↦ θ(y)ξ(y)(ω(sv + y)) has derivative θ(y)ξ(y)(Dω(sv + y)[v]) (chain rule); the integrands are AEStronglyMeasurable.
3. For s ∈ (t − 1, t + 1) the integrands vanish unless y ∈ B = B̄_{r+(|t|+1)‖v‖}(0), and |F'| ≤ Kθ1_B with θ1_B integrable (locallyIntegrable_mult); F(t, ·) is integrable.
4. hasDerivAt_integral_of_dominated_loc_of_deriv_le gives G'(t) = R.action(y ↦ Dω(tv + y)[v]).

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (project b4d606d, mathlib 25730c7c); git status (clean at b4d606d); stat GMT/Ch07/Submission.lean .lake/build/lib/lean/GMT/Ch07/Submission.olean`
- `python3 inspection of dag.json: selected node (depth 3, depends_on orientation_norm_bound-a1, no children), siblings under cone_splitting-a1, accepted dtc_cwv_* / dtc_cone_* / unit_orientation_norm_le_one / dtc_blowUp_testForm_corr types; scan of all lean_statements for curryLeft|blowUp|translat|fderiv|extDeriv|exteriorDerivative|HasDerivAt`
- `git show {d120e82,9203aee,77ba671,ec0cc8f,dd88db7,81f1c23,da8da23,0325970}:GMT/Ch07/Submission.lean (accepted cone criterion, wedge vanishing, Euler-Cartan, contraction, Lie annihilation, scaled derivative, dilation invariance, orientation norm proofs)`
- `python3 nodes/root-density-and-tangent-cones-a1-cone-a1-cone-lemma-a1/decomposition-v1.json and nodes/root-dimension-reduction-results-a1-cone-splitting-a1/decomposition-v1.json (reuse convention, embedded-proof precedent)`
- `grep -rn 'alternatizeUncurryFin|extDeriv' and grep -rln 'Cartan|interiorProduct|lieDerivForm' in the snapshot mathlib (only Lie-algebra Cartan files; no Cartan formula or interior product for differential forms)`
- `grep -n defs in simongmt Chapter06/Forms.lean, AffineCurrentPushforward.lean, CurrentLocalEquality.lean (restrictDomain_apply); grep -rn 'curryLeft|interior|translat' simongmt (no contraction/translation lemmas)`
- `sed -n 330,400p book/chapter-07.txt (7.3.1 proof, Lemma 7.3.5 left to reader); sed -n 420,500p and 550,600p book/chapter-06.txt (homotopy formula 2.25-2.27, Lemma 2.33)`
- `#check fderiv_comp_add_left, is_const_of_deriv_eq_zero, exteriorDerivative_isTestForm, GeometricCurrentOn.boundary_apply, ContinuousAlternatingMap.curryLeftLI, ContinuousAlternatingMap.alternatizeUncurryFin`
- `verifier/lean_contract.py validate_lean_statement and verifier/gmt-compare.py contract_scope/child_modules applied to the 8 types (NodeChallenge/NodeSolution emulation)`
- `lake env lean /tmp/ti-decomp/{Stubs,Full2,Emu}.lean and /tmp/ti-decomp/final/{Final,Isolate,FromJson}.lean (all children, isolation with dependency stubs, comparator wrapper, re-extraction from JSON; #print axioms)`
- `grep -rl dimred_cs_ti_ across workspaces/ (incl. .swarm-worktrees), lake-packages simongmt, and dag.json (no matches)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-translation-invariance-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-translation-invariance-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-cone-lemma-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-cone-lemma-a1/decomposition-scope-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-measure-unique-a1-orie-c3a822a8f5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ti-decomp/final/FromJson.lean`
- `/tmp/ti-decomp/final/Isolate.lean`
- `/tmp/ti-decomp/Emu.lean`

The pins match: the snapshot is at project b4d606d (= the workspace HEAD, clean) and mathlib 25730c7c. The built Submission.olean is newer than the frozen source.

What the library lacks.
- Mathlib has the exterior derivative (extDeriv = alternatizeUncurryFin ∘ fderiv, with extDeriv_apply and alternatizeUncurryFin_apply). It has no interior product and no Cartan formula for differential forms; the Cartan grep matches only Lie-algebra files.
- SimonGMT Chapter06 provides exteriorDerivative, IsTestForm, exteriorDerivative_isTestForm, boundary_apply, restrictDomain_apply, affinePushforward_apply and affinePullbackForm. It has no contraction, translation or Lie-derivative lemmas.
So the constant-field Cartan identity, the contraction lemma and the translation lemmas are new obligations.

Precedent and reuse.
- The accepted cone-lemma children (commits d120e82, 9203aee, 77ba671, ec0cc8f, dd88db7, 81f1c23, da8da23) prove the Euler-field (dilation) versions. Their types are tied to the point x or to sⁿω(s·), so none applies to a fixed vector v; they served as templates.
- The accepted dtc_blowUp_testForm_corr is not needed, because blowup_translate_eval unfolds blowUp directly.
- The only reuse is unit_orientation_norm_le_one (accepted, candidate 0325970, byte-identical type), which is already this node's resolved dependency.

Mathlib facts used, all present in the snapshot: fderiv_comp_add_left, is_const_of_deriv_eq_zero, HasCompactSupport.comp_homeomorph, HasCompactSupport.fderiv, hasDerivAt_integral_of_dominated_loc_of_deriv_le, Submodule.starProjection_eq_self_iff, ae_withDensity_iff and withDensity_absolutelyContinuous.

Lean check. All seven new children have kernel-checked proofs with standard axioms only, and the 9-line assembly of the frozen parent type compiles from them.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
