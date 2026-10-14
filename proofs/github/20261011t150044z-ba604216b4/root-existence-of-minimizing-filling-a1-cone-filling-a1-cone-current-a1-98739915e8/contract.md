<!-- theorem-id: gmt-ch07/root.existence_of_minimizing_filling-a1.cone_filling-a1.cone_current-a1 -->

## Theorem `Submission.ecf_cone_current`

Let n, P ∈ ℕ and let S ∈ 𝒟_{n+1}(ℝ^P) (a GeometricCurrentOn univ (n + 1) on ℝ^P = Euclid P) have finite mass (S.mass ≠ ∞), compact support spt S (S.support) and ∂S = 0 (S.boundary = 0). Then there is R ∈ 𝒟_{n+2}(ℝ^P) (GeometricCurrentOn univ (n + 2)) such that spt R is compact, ∂R = S (R.boundary = S), and for every test (n+2)-form ω (TestFormOn univ (n + 2)) there is a test (n+1)-form γ (TestFormOn univ (n + 1)) with R(ω) = S(γ) and γ(x)(v_1, …, v_{n+1}) = ∫_0^1 t^{n+1} ω(tx)(x, v_1, …, v_{n+1}) dt for every x ∈ spt S and all v_1, …, v_{n+1} ∈ ℝ^P (here (x, v_1, …, v_{n+1}) is Fin.cons x v and the integral is the interval integral over [0, 1]). (R is Simon's cone 0 ⨯ S = h_#([[(0,1)]] × S), h(t, x) = tx, written as R(ω) = S(ζ·K_{n+2}ω) with the Poincaré homotopy operator K and a smooth cutoff ζ ≡ 1 near spt S.)

Node: `root.existence_of_minimizing_filling-a1.cone_filling-a1.cone_current-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8484

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/810, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7569

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7569, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1809, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8725, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7718, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6960, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2794, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8730, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7056, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4607, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7728, https://github.com/ZhengyangZhang06/gmt-formalize/issues/810, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1174

## Lean problem

Declaration: `Submission.ecf_cone_current`

```lean
∀ (n P : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) (n + 1)), S.mass ≠ ∞ → IsCompact S.support → S.boundary = 0 → ∃ R : GeometricCurrentOn (univ : Set (Euclid P)) (n + 2), IsCompact R.support ∧ R.boundary = S ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) (n + 2), ∃ γ : TestFormOn (univ : Set (Euclid P)) (n + 1), R ω = S γ ∧ ∀ x ∈ S.support, ∀ v : Fin (n + 1) → Euclid P, (γ : DifferentialForm (Euclid P) (n + 1)) x v = ∫ t in (0 : ℝ)..1, t ^ (n + 1) * (ω : DifferentialForm (Euclid P) (n + 2)) (t • x) (Fin.cons x v)
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

- Parent DAG node: `root.existence_of_minimizing_filling-a1.cone_filling-a1`
- Child DAG node: `root.existence_of_minimizing_filling-a1.cone_filling-a1.cone_current-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Part B (B1–B6) of the selected parent's supplied proof, i.e. Simon Ch. 6, 2.25 (homotopy formula for the affine homotopy h(t, x) = tx from f = 0 to g = id), 2.30 (the cone 0 ⨯ S := h_#([[(0,1)]] × S)), 2.31 (∂(0 ⨯ S) = S − 0 ⨯ ∂S) and 2.32 (book/chapter-06.txt lines 441–451 and 528–551). As in the supplied proof, h_#([[(0,1)]] × ·) is written at the level of forms through the Poincaré homotopy operator K. One specialization: the continuity step B4 uses the hypothesis S.mass ≠ ∞ (in the selected parent S is integer multiplicity with compact support, and its finite mass is delivered by the sibling im_parametrization) instead of the general C^m estimate of the supplied B4; only sup-norm bounds are then needed.

Notation and tools.
- k := n + 1 ≥ 1. For p ∈ ℕ, Λ^p := Covector (Euclid P) p (continuous alternating p-linear maps (ℝ^P)^p → ℝ) and 𝒟^p := TestFormOn univ p (C^∞ maps ℝ^P → Λ^p with compact support). For α ∈ Λ^p, ‖α‖ is the operator norm (Mathlib norm of ContinuousAlternatingMap) and |α|_E := covectorEuclideanNorm α is the Euclidean coefficient norm (|α|_E² = Σ_I α(e_{I_1}, …, e_{I_p})² over strictly increasing I).
- d = exteriorDerivative = Mathlib extDeriv. At a point x where β is differentiable, dβ(x)(w_0, …, w_p) = Σ_{i=0}^p (−1)^i Dβ(x)[w_i](w_0, …, ŵ_i, …, w_p) (exteriorDerivative_apply / extDeriv_apply: ∑ i, (−1)^i • fderiv ℝ (fun y => β y (i.removeNth w)) x (w i)). In particular dβ(x) depends only on β on a neighbourhood of x.
- For p ≥ 1, α ∈ Λ^p and x ∈ ℝ^P, ι_xα := α.curryLeft x ∈ Λ^{p−1}, so ι_xα(v) = α(Fin.cons x v) =: α(x, v). The map (α, x) ↦ ι_xα is continuous bilinear and ‖ι_xα‖ ≤ ‖α‖‖x‖.
- spt X = X.support = univ ∖ Z_X, where the zero region Z_X is the union of the open W with compact closure on which X vanishes; Z_X is open (GeometricCurrentOn.isOpen_zeroRegion), so spt X is closed.
- Sibling support_vanishing (Submission.dtc_vanish_off_support): if X ∈ 𝒟_p(U), γ ∈ 𝒟^p(U) and tsupport γ is disjoint from spt X, then X(γ) = 0. Consequence (L), locality: if γ, γ' ∈ 𝒟^p agree on an open set V ⊇ spt X, then X(γ) = X(γ'). Indeed γ − γ' vanishes on V, so its support lies in the closed set ℝ^P ∖ V, hence tsupport(γ − γ') ⊆ ℝ^P ∖ V is disjoint from spt X; by support_vanishing and linearity X(γ) − X(γ') = X(γ − γ') = 0.
- Sibling param_integral (Submission.cmcdt_lpo_slice_param_integral): if V is a complete real normed space and h : ℝ × ℝ^P → V is C^∞, then x ↦ ∫_0^1 h(t, x) dt is C^∞, and its derivative at x is ∫_0^1 D_x h(t, x) dt (the integral of the partial derivatives fderiv ℝ (fun x' => h (t, x')) x).

Step 1 (the homotopy operator; B1). For p ≥ 1 and a C^∞ map β : ℝ^P → Λ^p put h_β(t, x) := t^{p−1} • ι_x(β(t • x)) ∈ Λ^{p−1} and (K_pβ)(x) := ∫_0^1 h_β(t, x) dt (interval integral in the finite-dimensional, hence complete, space Λ^{p−1}).
 (a) h_β is C^∞ on ℝ × ℝ^P: t ↦ t^{p−1} and (t, x) ↦ β(t • x) are C^∞ and (α, x) ↦ ι_xα is continuous bilinear. By param_integral, K_pβ is C^∞ and D(K_pβ)(x) = ∫_0^1 D_x h_β(t, x) dt for every x.
 (b) Evaluation at a fixed v ∈ (ℝ^P)^{p−1} is a continuous linear map Λ^{p−1} → ℝ and commutes with the interval integral, so (K_pβ)(x)(v) = ∫_0^1 t^{p−1} β(tx)(x, v) dt. By (a), the product rule for the bilinear ι and the chain rule D_x[β(tx)][w] = t·Dβ(tx)[w], for every w: D[y ↦ (K_pβ)(y)(v)](x)[w] = ∫_0^1 t^{p−1}[t·Dβ(tx)[w](x, v) + β(tx)(w, v)] dt.
 (c) If β(tx) = 0 for every t ∈ [0, 1], then h_β(t, x) = 0 for t ∈ [0, 1], so (K_pβ)(x) = 0.
 (d) β ↦ K_pβ is linear.

Step 2 (homotopy formula; B2). For p ≥ 1 and every C^∞ p-form β: β = d(K_pβ) + K_{p+1}(dβ). Fix x and v = (v_1, …, v_p).
 - By the formula for d (with w_{i−1} = v_i) and Step 1(b): d(K_pβ)(x)(v) = Σ_{i=1}^p (−1)^{i−1} ∫_0^1 t^{p−1}[t·Dβ(tx)[v_i](x, v_1, …, v̂_i, …, v_p) + β(tx)(v_i, v_1, …, v̂_i, …, v_p)] dt. Moving v_i to the front costs i − 1 transpositions: β(tx)(v_i, v_1, …, v̂_i, …, v_p) = (−1)^{i−1}β(tx)(v). Hence d(K_pβ)(x)(v) = ∫_0^1 [p·t^{p−1}β(tx)(v) + t^p Σ_{i=1}^p (−1)^{i−1}Dβ(tx)[v_i](x, v_1, …, v̂_i, …, v_p)] dt.
 - dβ is C^∞, and by Step 1(b) with p + 1 and the formula for d with w_0 = x, w_i = v_i: K_{p+1}(dβ)(x)(v) = ∫_0^1 t^p dβ(tx)(x, v) dt = ∫_0^1 t^p[Dβ(tx)[x](v) + Σ_{i=1}^p (−1)^i Dβ(tx)[v_i](x, v_1, …, v̂_i, …, v_p)] dt.
 - Adding, the two sums cancel: d(K_pβ)(x)(v) + K_{p+1}(dβ)(x)(v) = ∫_0^1 φ'(t) dt with φ(t) := t^p β(tx)(v), since φ'(t) = p·t^{p−1}β(tx)(v) + t^p Dβ(tx)[x](v) (chain rule; φ is C¹). By the fundamental theorem of calculus this is φ(1) − φ(0) = β(x)(v), because p ≥ 1.

Step 3 (cutoff and definition; B3). If spt S = ∅ put V := ∅ and ζ := 0. Otherwise let O := thickening 2 (spt S) (open, bounded since spt S is compact) and C := cthickening 1 (spt S) (closed, C ⊆ O), and apply Mathlib exists_contDiff_support_eq_eq_one_iff (ℝ^P is finite-dimensional): there is a C^∞ ζ : ℝ^P → [0, 1] with support ζ = O and ζ(x) = 1 ⟺ x ∈ C. Then tsupport ζ ⊆ closure O is compact, and V := thickening 1 (spt S) is open with spt S ⊆ V ⊆ C, so ζ = 1 on V. In both cases: V is open, spt S ⊆ V, ζ = 1 on V, 0 ≤ ζ ≤ 1 and tsupport ζ is compact.
 For ω ∈ 𝒟^{k+1} put Γ(ω) := ζ • K_{k+1}ω. It is C^∞ (Step 1(a)) and vanishes off support ζ, so tsupport Γ(ω) ⊆ tsupport ζ is compact: Γ(ω) ∈ 𝒟^k, and Γ is linear (Step 1(d)). Define R₀(ω) := S(Γ(ω)); R₀ is a linear functional on 𝒟^{k+1}.

Step 4 (R₀ is a current; B4 under finite mass). Let M := (S.mass).toReal; S.mass ≠ ∞ by hypothesis.
 (a) Mass bound. If γ ∈ 𝒟^k, c > 0 and |γ(x)|_E ≤ c for all x, then |S(γ)| ≤ c·M: the forms ±c⁻¹γ are admissible for S.mass = S.massOn univ (tsupport in univ, coefficient norm ≤ 1 everywhere), so ±c⁻¹S(γ) ≤ M (GeometricCurrentOn.le_massOn and S.mass ≠ ∞).
 (b) Coefficient versus operator norm. For α ∈ Λ^k and increasing I, |α(e_{I_1}, …, e_{I_k})| ≤ ‖α‖ (the e_i are unit vectors), so |α|_E ≤ c_0‖α‖ with c_0 := (number of increasing maps Fin k → Fin P)^{1/2}.
 (c) For ω ∈ 𝒟^{k+1} put ‖ω‖_∞ := sup_y ‖ω(y)‖ (finite: ω is continuous with compact support). For every x, ‖(K_{k+1}ω)(x)‖ ≤ ∫_0^1 t^k‖ι_x ω(tx)‖ dt ≤ ‖x‖·‖ω‖_∞. Let ρ_ζ := sup{‖x‖ : x ∈ tsupport ζ} (0 if tsupport ζ = ∅). Since 0 ≤ ζ ≤ 1 and Γ(ω) = 0 off tsupport ζ, |Γ(ω)(x)|_E ≤ c_0ρ_ζ‖ω‖_∞ for all x. By (a) applied with c := c_0ρ_ζ‖ω‖_∞ + ε for every ε > 0, |R₀(ω)| ≤ M·c_0·ρ_ζ·‖ω‖_∞.
 (d) Continuity. Let ω_j → 0 in the sense of TestFormOnConverges (ω_j) 0: there is a compact K₁ containing every tsupport ω_j, and every iterated derivative of ω_j tends to 0 uniformly on K₁; the 0-th one gives ω_j → 0 uniformly on K₁ (‖iteratedFDeriv ℝ 0 f x‖ = ‖f x‖). Off K₁ every ω_j vanishes. Hence ‖ω_j‖_∞ → 0 and R₀(ω_j) → 0 by (c). Therefore R := ⟨R₀, continuity⟩ is a GeometricCurrentOn univ (k + 1) = GeometricCurrentOn univ (n + 2), with R(ω) = S(ζ • K_{k+1}ω) for every ω ∈ 𝒟^{k+1}.

Step 5 (∂R = S; B5). Let ω ∈ 𝒟^k. By definition of the boundary, R.boundary(ω) = R(dω) = S(ζ • K_{k+1}(dω)). By Step 2 with p = k ≥ 1 and β = ω, K_{k+1}(dω) = ω − d(K_kω), so R.boundary(ω) = S(ζ • ω) − S(ζ • d(K_kω)); here ζ • ω and ζ • d(K_kω) are test k-forms (C^∞, tsupport ⊆ tsupport ζ).
 (a) ζ • ω and ω agree on the open set V ⊇ spt S, so S(ζ • ω) = S(ω) by (L).
 (b) ζ • K_kω ∈ 𝒟^{k−1} (C^∞ by Step 1(a), tsupport ⊆ tsupport ζ). For y ∈ V the forms ζ • K_kω and K_kω coincide on the neighbourhood V of y, so d(ζ • K_kω)(y) = d(K_kω)(y) = ζ(y)·d(K_kω)(y) (ζ(y) = 1). Thus the test k-forms ζ • d(K_kω) and d(ζ • K_kω) agree on V, and by (L) and ∂S = 0: S(ζ • d(K_kω)) = S(d(ζ • K_kω)) = S.boundary(ζ • K_kω) = 0, where S.boundary ∈ 𝒟_n is the current γ ↦ S(dγ) of degree k − 1 = n.
 Hence R.boundary(ω) = S(ω) for every ω ∈ 𝒟^k. A GeometricCurrentOn is determined by its underlying linear functional (the continuity field is a proposition), so R.boundary = S.

Step 6 (spt R is compact; B6). C₀ := {t • x : t ∈ [0, 1], x ∈ spt S} is the image of the compact set [0, 1] × spt S under the continuous map (t, x) ↦ t • x, hence compact (and closed).
 (a) Let ω ∈ 𝒟^{k+1} with tsupport ω ∩ C₀ = ∅. W := {x : t • x ∉ tsupport ω for all t ∈ [0, 1]} is open: its complement is the projection to ℝ^P of the closed set {(t, x) ∈ [0, 1] × ℝ^P : t • x ∈ tsupport ω}, and the projection [0, 1] × ℝ^P → ℝ^P is a closed map because [0, 1] is compact. spt S ⊆ W, since t • x ∈ C₀ for x ∈ spt S. By Step 1(c), K_{k+1}ω = 0 on W, so Γ(ω) vanishes on the open set W and tsupport Γ(ω) ⊆ ℝ^P ∖ W, which is disjoint from spt S. By support_vanishing, R(ω) = S(Γ(ω)) = 0.
 (b) Let x ∉ C₀. As C₀ is closed there is r > 0 with closedBall(x, r) ∩ C₀ = ∅. The open ball B := ball(x, r) has compact closure contained in closedBall(x, r) ⊆ univ, and every ω ∈ 𝒟^{k+1} with tsupport ω ⊆ B satisfies tsupport ω ∩ C₀ = ∅, hence R(ω) = 0 by (a). So B is one of the sets forming the zero region of R, and x ∉ spt R.
 (c) Thus spt R ⊆ C₀. spt R is closed, so it is a closed subset of the compact set C₀, hence compact.

Step 7 (the formula). Let ω ∈ 𝒟^{k+1} and γ := Γ(ω) = ζ • K_{k+1}ω ∈ 𝒟^k (Step 3). Then R(ω) = S(γ) by Step 4. For x ∈ spt S ⊆ V we have ζ(x) = 1, so by Step 1(b) with p = k + 1 = n + 2, for every v : Fin (n + 1) → ℝ^P: γ(x)(v) = (K_{k+1}ω)(x)(v) = ∫_0^1 t^{n+1} ω(t • x)(Fin.cons x v) dt.

Steps 4–7 give R ∈ 𝒟_{n+2}(ℝ^P) with IsCompact R.support, R.boundary = S and the stated formula. ∎

## Key steps

1. Homotopy operator (K_pβ)(x) = ∫_0^1 t^{p−1} β(tx)(x, ·) dt: C^∞ with derivatives under the integral by the sibling param_integral; it vanishes at x when β vanishes on the segment [0, x].
2. Homotopy formula β = d(K_pβ) + K_{p+1}(dβ) for p ≥ 1: the two alternating sums cancel and the rest is ∫_0^1 d/dt[t^p β(tx)(v)] dt = β(x)(v).
3. Cutoff ζ ∈ C^∞_c, ζ ≡ 1 on an open V ⊇ spt S (exists_contDiff_support_eq_eq_one_iff); R(ω) := S(ζ·K_{n+2}ω) is linear.
4. Continuity from finite mass: |S(γ)| ≤ M(S)·sup|γ|_E, |γ|_E ≤ c_0‖γ‖ and ‖ζK ω‖ ≤ ρ_ζ sup‖ω‖, and test-form convergence forces sup‖ω_j‖ → 0.
5. ∂R = S: K(dω) = ω − dKω, locality from support_vanishing (S(ζω) = S(ω), S(ζ dKω) = S(d(ζKω))) and ∂S = 0.
6. spt R ⊆ C₀ = {tx : t ∈ [0,1], x ∈ spt S} (compact): forms supported off C₀ give ζKω supported off spt S; closed subset of a compact set.
7. Formula: on spt S, ζ = 1, so γ := ζK_{n+2}ω satisfies γ(x)(v) = ∫_0^1 t^{n+1} ω(tx)(Fin.cons x v) dt and R(ω) = S(γ).

## Reference use

### local-project

Queries:
- `sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n 'theorem exists_contDiff_support_eq_eq_one_iff|lemma measure_compl_support|theorem volume_preserving_piFinSuccAbove|theorem EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp|theorem norm_fderiv_le_of_lipschitz|theorem measurable_to_countable.|theorem enorm_integral_le_lintegral_enorm|theorem setIntegral_congr_set|theorem measurable_fderiv |def curryLeft|theorem extDeriv_apply|theorem hasFDerivAt_integral_of_dominated_of_fderiv_le..' local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean'`
- `grep -rln 'contDiff_parametric|ContDiff.*intervalIntegral|contDiff_integral' mathlib/Mathlib (no match)`
- `python3 -I over dag.json (2375 nodes): keyword search homotop|cone|parametri|Lipschitz|Gram|orientation|approximate tangent|density|area formula|pushforward; status, candidate_commit and child/dependency closure of the reuse targets; byte equality of lean_statement with each handoff; replay of Runtime._existing_lean_name_problem for all 12 names`
- `git show <candidate>:GMT/Ch07/Submission.lean | grep -n 'theorem Submission.<name>|sorry' for the 8 reused candidates; cross-candidate comparison of 77 shared theorem headers`
- `lake env lean /tmp/cone-split-check/Final.lean (12 exact child types; parent assembly; Lean proofs of ecf_im_lipschitz_parametrization and ecf_isIntegerMultiplicity_of_parametrization from the reused types; Fin.cons, enorm and inner meaning checks; #print axioms)`
- `sed -n 441,551p and 850,866p book/chapter-06.txt`
- `grep -n '_existing_lean_name_problem|_accepted_checkpoint|def ensure|_overlay_accepted_children|cited_inherited|_reference_use_problem' /runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/{runtime,store,inherited}.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-existence-of-minimizing-filling-a1-cone-filling-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-vanish-off-support-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-9310c84433/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-1df3e47686/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-im-calculus-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-im-series-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-53b6b2be95/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-covector-gram-bounds-a1/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/inherited.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/cone-split-check/Final.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) Ch07 contract is byte-identical (sha256 e4148e7f…) to the workspace Contract.lean and Submission.lean.

Availability of the cited Mathlib facts:
- The pinned Mathlib contains every Mathlib fact the new children cite: exists_contDiff_support_eq_eq_one_iff, Measure.measure_compl_support, volume_preserving_piFinSuccAbove, EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp, ContinuousAlternatingMap.curryLeft, extDeriv_apply, measurable_to_countable', enorm_integral_le_lintegral_enorm, setIntegral_congr_set, measurable_fderiv, norm_fderiv_le_of_lipschitz and hasFDerivAt_integral_of_dominated_of_fderiv_le''.
- It has no C^∞ parametric-integral lemma (no match). B1 therefore reuses the accepted cmcdt_lpo_slice_param_integral.
- No cone construction, homotopy operator or general integrality-of-parametrization theorem exists in the snapshot project or in SimonGMT.

Reuse of DAG checkpoints:
- The DAG holds comparator-accepted checkpoints that are exactly E2–E4, E1/(MR), G2–G6 for one piece, the G4–G6 summation, (IMC), A2a and (VO). These are dor_lmb_fcd_imp_parametric_rep, dor_imrep_massOn_eq_measure_and_support, dimred_mbl_dt_lpip_lipschitz_piece_current, cmcdt_im_series, cmc_imRep_locality_restrict_sub, covectorEuclideanNorm_gram_bounds and dtc_vanish_off_support.
- Their frozen types match byte for byte. Their candidate commits contain the declared theorems, with the only sorry in main_theorem. Their closures are fully accepted, and the shared theorem headers are identical across candidates.
- The runtime permits identical-type reuse of accepted checkpoints across branches. The four new ecf_ names are unreserved.

Lean checks:
- All 12 child types elaborate.
- The parent assembly compiles.
- Both glue children are proved in Lean from the exact reused types, with 0 errors and only stub sorries.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
