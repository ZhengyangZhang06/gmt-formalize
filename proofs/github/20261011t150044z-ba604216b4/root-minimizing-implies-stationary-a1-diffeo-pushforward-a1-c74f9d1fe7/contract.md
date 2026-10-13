<!-- theorem-id: gmt-ch07/root.minimizing_implies_stationary-a1.diffeo_pushforward-a1 -->

## Theorem `Submission.imrep_c1_diffeo_pushforward_im`

Let U ⊆ ℝ^P be open, R = (M, θ, ξ) an integer multiplicity triple representing T ∈ 𝒟_n(U), K ⊆ U compact, and φ : ℝ^P → ℝ^P a C¹ bijection with Dφ(x) injective for every x and φ(x) = x for x ∉ K. Then there is an integer multiplicity S ∈ 𝒟_n(U) with S(ω) = ∫_M θ(x)·ξ(x)(φ^#ω(x)) dH^n(x) for all ω ∈ 𝒟^n(U), where φ^#ω(x) = ω(φ(x))∘Dφ(x) is the pulled-back covector (so S = φ_#T), and ∂S = 0 whenever ∂T = 0 (BoundaryVanishes; vacuous for n = 0).

Node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/367

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/985

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4116, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4128, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4130, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4137, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4140, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4147, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4151, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4162, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4166, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4175, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4185

## Lean problem

Declaration: `Submission.imrep_c1_diffeo_pushforward_im`

```lean
∀ (P n : ℕ) (U K : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n) (φ : Euclid P → Euclid P), IsOpen U → R.Represents T → IsCompact K → K ⊆ U → ContDiff ℝ 1 φ → Bijective φ → (∀ x, Injective (fderiv ℝ φ x)) → (∀ x, x ∉ K → φ x = x) → ∃ S : GeometricCurrentOn U n, IsIntegerMultiplicity S ∧ (BoundaryVanishes T → BoundaryVanishes S) ∧ ∀ ω : TestFormOn U n, S ω = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) n) (φ x)).compContinuousLinearMap (fderiv ℝ φ x)) ∂μHE[n]
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

- Parent DAG node: `root.minimizing_implies_stationary-a1`
- Child DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon 6.2.23–2.24 (definition of f_#T, ∂f_# = f_#∂, the integral formula 2.24(2)–(3)) and 6.3.3–3.9 (f_#T is integer multiplicity; for injective f, f_#T = τ(f(M), θ∘f^{-1}, induced orientation), with the induced orientation of 3.5/3.7), together with Ch. 3 §1–2 (approximate tangent planes, area formula); this is step 4 of the parent proof. The printed argument (3.6–3.7) uses without proof that dφ_x maps T_xM onto the approximate tangent plane of φ(M) at φ(x) for H^n-a.e. x ∈ M; steps 4–6 supply this. Notation: E := ℝ^P; M, θ, ξ from R; Q(x) := approxTangentPlane n M x and p(x) its orthogonal projection; for a linear L and a plane Q, J(L, Q) := normDet(L restricted to Q) = (det(Lτ_a·Lτ_b))^{1/2} for any orthonormal basis τ of Q (Mathlib LinearMap.normDet, normDet_sq_eq_det_gram); β∘L denotes β.compContinuousLinearMap L. The argument is uniform in n ≥ 0; step 10 records what each step reduces to when n = 0.
1. φ is a bi-Lipschitz C¹ diffeomorphism preserving U. By the inverse function theorem φ^{-1} is C¹ (Dφ(x) is an injective, hence invertible, endomorphism of E). φ is the identity on the open set E ∖ K, so Dφ = I there, φ(E ∖ K) = E ∖ K, hence (φ bijective) φ(K) = K, φ(U) = U and φ^{-1}(U) = U. Dφ − I and D(φ^{-1}) − I are continuous with compact support, so ‖Dφ‖, ‖D(φ^{-1})‖ ≤ Λ on E for some Λ ≥ 1 and, by the mean value inequality, φ and φ^{-1} are Λ-Lipschitz. Hence Λ^{-n}H^n(A) ≤ H^n(φ(A)) ≤ Λ^n H^n(A) for all A ⊆ E (Mathlib LipschitzWith.hausdorffMeasure_image_le for φ and φ^{-1}; μHE[n] is a fixed positive multiple of μH[n]); in particular φ and φ^{-1} map H^n-null sets to H^n-null sets.
2. S is a current with the stated action. For ω ∈ 𝒟^n(U) let g_ω(x) := θ(x)ξ(x)(ω(φx)∘Dφ(x)). For a.e. x ∈ M, ξ(x)(β) = ±β(τ) with |τ_i| = 1, so |ξ(x)(β)| ≤ ‖β‖ (operator norm), and ‖β∘L‖ ≤ ‖β‖‖L‖^n. g_ω vanishes off C_ω := φ^{-1}(tsupport ω), a compact subset of U, so |g_ω| ≤ Λ^n·sup‖ω‖·θ·1_{C_ω} a.e. on M, which is integrable by R.locallyIntegrable_mult; g_ω is a.e. strongly measurable (θ measurable, ξ a.e. strongly measurable, x ↦ ω(φx) and x ↦ Dφ(x) continuous, evaluation continuous). Define S(ω) := ∫_M g_ω dH^n. S is linear in ω, and if ω_j → 0 in 𝒟^n(U) (TestFormOnConverges: supports in one compact C ⊆ U, uniform convergence) then |S(ω_j)| ≤ Λ^n sup‖ω_j‖ ∫_{M∩φ^{-1}C} θ dH^n → 0; so S is a GeometricCurrentOn U n with the required action formula.
3. Boundary. Let n ≥ 1 and T.boundary = 0 (for n = 0, BoundaryVanishes S is True). Fix η ∈ 𝒟^{n−1}(U). Let ρ_k be smooth mollifiers supported in B_{1/k}(0) and φ_k := id + ρ_k∗(φ − id). Then φ_k is C^∞, φ_k = id outside K_k := K + closedBall(0, 1/k), a compact subset of U for k ≥ k_0, and φ_k → φ, Dφ_k → Dφ uniformly on E. The pulled-back form φ_k^#η(x) := η(φ_k x)∘Dφ_k(x) is smooth with tsupport ⊆ tsupport η ∪ K_k (φ_k = id near every point outside K_k), so φ_k^#η ∈ 𝒟^{n−1}(U), and d(φ_k^#η) = φ_k^#(dη) (exterior derivative commutes with pull-back by smooth maps: SimonGMT exteriorDerivativeOn_pullbackFormWithin with domains univ, i.e. Mathlib extDerivWithin_pullback). Therefore 0 = T.boundary(φ_k^#η) = T(φ_k^#dη) = ∫_M θ ξ(dη(φ_k x)∘Dφ_k(x)) dH^n. As k → ∞ these integrands converge pointwise to θ ξ(dη(φx)∘Dφ(x)) and are dominated by C·θ·1_{tsupport η ∪ K_{k_0}}; by dominated convergence S(dη) = 0. So S.boundary = 0.
4. Lipschitz pieces of M. By R.rectifiable (SimonGMT CountablyRectifiable n M) there are M_0 ⊆ E with H^n(M_0) = 0 and Lipschitz maps F_j : ℝ^n → E (j ∈ ℕ) with M ⊆ M_0 ∪ ⋃_j F_j(ℝ^n). Let G_j := {a ∈ ℝ^n : F_j is differentiable at a and DF_j(a) is injective} (SimonGMT areaRegularSet F_j); G_j is Borel (SimonGMT measurableSet_areaRegularSet) and H^n(F_j(ℝ^n ∖ G_j)) = 0 (SimonGMT area_image_compl_regularSet_eq_zero).
 (a) Coercivity constant. For an injective linear map A : ℝ^n → E define m(A) > 0 as follows. If n ≥ 1, m(A) := min{|Ah| : h ∈ ℝ^n, |h| = 1}; the minimum exists and is positive because the unit sphere of ℝ^n is compact and nonempty and h ↦ |Ah| is continuous and nowhere zero on it. If n = 0, m(A) := 1; the unit sphere of ℝ^0 = {0} is empty, so no minimum is taken. In both cases (†) |Ah| ≥ m(A)|h| for every h ∈ ℝ^n: for n ≥ 1 and h ≠ 0 apply the definition to h/|h| and multiply by |h|; for h = 0, which is the only vector when n = 0, both sides vanish. (Alternatively, one may take m(A) := 1/K for any K > 0 with AntilipschitzWith K A, which Mathlib's LinearMap.exists_antilipschitzWith supplies for every injective A in every dimension, including n = 0; only m(A) > 0 and (†) are used below.)
 (b) Positive radius. Define r : (ℝ^n →L[ℝ] E) → ℝ≥0 by r(A) := m(A)/2 if A is injective and r(A) := 1 otherwise. Then r(A) > 0, hence r(A) ≠ 0, for every A, including every A when n = 0 (then every A is injective and r(A) = 1/2). This is exactly the hypothesis rpos : ∀ A, r A ≠ 0 of Mathlib's exists_partition_approximatesLinearOn_of_hasFDerivWithinAt.
 (c) Partition. Apply that theorem with f := F_j, s := G_j, f' := fderiv ℝ F_j (for a ∈ G_j, F_j is differentiable at a, so HasFDerivWithinAt F_j (DF_j(a)) G_j a) and r from (b). It gives pairwise disjoint measurable sets t_{j,k} ⊆ ℝ^n (k ∈ ℕ) with G_j ⊆ ⋃_k t_{j,k} and continuous linear maps A_{j,k} such that ApproximatesLinearOn F_j A_{j,k} (G_j ∩ t_{j,k}) (r(A_{j,k})), i.e. |F_j(a) − F_j(a') − A_{j,k}(a − a')| ≤ r(A_{j,k})|a − a'| for a, a' ∈ G_j ∩ t_{j,k}, and, when G_j ≠ ∅, A_{j,k} = DF_j(y) for some y ∈ G_j; in particular A_{j,k} is injective and r(A_{j,k}) = m(A_{j,k})/2. (When G_j = ∅ all sets G_j ∩ t_{j,k} are empty and are discarded.) By (†), for a, a' ∈ G_j ∩ t_{j,k}: |F_j(a) − F_j(a')| ≥ |A_{j,k}(a − a')| − (m(A_{j,k})/2)|a − a'| ≥ (m(A_{j,k})/2)|a − a'|. So F_j is bi-Lipschitz on the Borel set G_j ∩ t_{j,k}, with lower constant m(A_{j,k})/2 > 0.
 (d) Disjoint pieces of M. Enumerate the nonempty sets G_j ∩ t_{j,k} as D_i, i ∈ I, where I = {1, 2, …} or I = {1, …, N} is a countable (possibly finite or empty, e.g. always empty when n > P) initial segment of the positive integers, with F_i the corresponding F_j and m_i := m(A_{j,k})/2 > 0: D_i is Borel, F_i is Lipschitz, |F_i(a) − F_i(a')| ≥ m_i|a − a'| for a, a' ∈ D_i, and F_i is differentiable with injective derivative at each point of D_i. Recursively let B_i := (D_i ∩ F_i^{-1}(M)) ∖ F_i^{-1}(⋃_{i'<i} F_{i'}(B_{i'})). Images of Borel sets under continuous maps injective on them are Borel (Lusin–Souslin, Mathlib MeasurableSet.image_of_continuousOn_injOn), so by induction on i ∈ I every B_i is Borel and P_i := F_i(B_i) is a Borel subset of M; the P_i are pairwise disjoint by construction. Finally Z := M ∖ ⋃_i P_i ⊆ M_0 ∪ ⋃_j F_j(ℝ^n ∖ G_j) is H^n-null: if x ∈ M ∖ M_0 then x = F_j(a) for some j and a; if a ∉ G_j then x ∈ F_j(ℝ^n ∖ G_j); if a ∈ G_j then a ∈ D_i for some i with F_i = F_j and a ∈ F_i^{-1}(M), so either a ∈ B_i and x ∈ P_i, or x ∈ F_{i'}(B_{i'}) = P_{i'} for some i' < i.
5. Density lemma. Let Y ⊆ U be Borel with H^n(Y ∩ C) < ∞ for every compact C ⊆ U, F : ℝ^n → E Lipschitz, B ⊆ ℝ^n Borel, and m > 0 with |F(a) − F(a')| ≥ m|a − a'| for a, a' ∈ B, F(B) ⊆ Y, and F differentiable with injective derivative at each point of B. Then for H^n-a.e. y ∈ F(B), writing y = F(b) (b ∈ B is unique), HasApproximateTangentSpaceAt n Y y (range DF(b)). Proof. (i) For H^n-a.e. y ∈ F(B): H^n((Y ∖ F(B)) ∩ B_r(y)) = o(r^n) as r ↓ 0. Indeed, on a compact C ⊆ U with y in its interior, ν := H^n⌞(Y ∩ C) is a finite Borel measure; by the Besicovitch density theorem (Mathlib Besicovitch.ae_tendsto_measure_inter_div) ν(F(B) ∩ B̄_r(y))/ν(B̄_r(y)) → 1 for ν-a.e. y ∈ F(B), so ν((Y ∖ F(B)) ∩ B̄_r(y)) = o(ν(B̄_r(y))); and ν(B̄_r(y)) ≤ C_n r^n for small r at H^n-a.e. y ∈ Y ∩ C by the upper density theorem applied to the H^n-measurable set A := Y ∩ C of finite measure (Simon Ch. 1 (3.26)(1), SimonGMT ae_hausdorff_dimensionalUpperDensity_le_one with real exponent n ≥ 0, stated for Simon's Hausdorff measure simonHausdorffMeasureReal n; by SimonGMT simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure it is a fixed positive multiple of μHE[n], so the bound holds for μHE[n] with another constant and the exceptional sets have the same null sets). Covering U by countably many such C gives the claim for H^n-a.e. y ∈ F(B). (ii) For f ∈ C_c(E) with support in B_R(0): by scaling of H^n and the injective Lipschitz area formula (SimonGMT weighted_area_formula_lipschitz_injOn, Jacobian J_F = areaJacobianAt F = normDet DF), ∫_{η_{y,r}(F(B))} f dH^n = r^{-n}∫_B f((F(a) − F(b))/r) J_F(a) da = ∫_{(B−b)/r} f((F(b + rc) − F(b))/r) J_F(b + rc) dc. Only |c| ≤ R/m contributes, before the limit because |F(b + rc) − F(b)| ≥ mr|c| when b + rc ∈ B, and in the limit because |DF(b)c| ≥ m|c| for every c ∈ ℝ^n. For the latter, let b be a Lebesgue density point of B and c ∈ ℝ^n, c ≠ 0: there are r_l ↓ 0 and c_l → c with b + r_l c_l ∈ B (otherwise, for some ε > 0 and all small r, B misses b + r·B_ε(c) ⊆ B_{r(|c|+ε)}(b), a set of measure r^n|B_ε(0)|, a fixed positive fraction of |B_{r(|c|+ε)}(b)|, contradicting density 1); then m r_l|c_l| ≤ |F(b + r_l c_l) − F(b)| = r_l|DF(b)c_l| + o(r_l), and dividing by r_l and letting l → ∞ gives m|c| ≤ |DF(b)c|. Choose b a Lebesgue density point of B and a Lebesgue point of J_F (a.e. b ∈ B; F maps L^n-null sets to H^n-null sets, so the corresponding y form a full-measure subset of F(B)). Then 1_{(B−b)/r} → 1 and J_F(b + r·) → J_F(b) in L¹(B_{R/m}), and (F(b + rc) − F(b))/r → DF(b)c uniformly for |c| ≤ R/m; f is bounded and uniformly continuous, so the integral tends to ∫_{ℝ^n} f(DF(b)c) J_F(b) dc = ∫_{range DF(b)} f dH^n (linear area formula, Mathlib LinearMap.euclideanHausdorffMeasure_image). (iii) |∫_{η_{y,r}Y} f dH^n − ∫_{η_{y,r}F(B)} f dH^n| ≤ ‖f‖_∞ r^{-n} H^n((Y ∖ F(B)) ∩ B_{rR}(y)) → 0 by (i). As finrank range DF(b) = n (DF(b) is injective), the definition of HasApproximateTangentSpaceAt is met.
6. Tangent planes of M and of φ(M). Step 5 with Y := M (Borel, ⊆ U, and H^n(M ∩ C) ≤ ∫_{M∩C} θ dH^n < ∞ for compact C ⊆ U because θ ≥ 1 on M) and the pieces (F_i, B_i, m_i), plus uniqueness of approximate tangent planes (SimonGMT HasApproximateTangentSpaceAt.unique), gives Q(F_i b) = range DF_i(b) for L^n-a.e. b ∈ B_i (H^n-null subsets of P_i pull back to L^n-null subsets of B_i because F_i^{-1} is (1/m_i)-Lipschitz on P_i). φ(M) is Borel, ⊆ U, with H^n(φ(M) ∩ C) ≤ Λ^n H^n(M ∩ φ^{-1}C) < ∞ for compact C ⊆ U; φ(M) is the disjoint union of φ(Z) and the (φ∘F_i)(B_i), with H^n(φ(Z)) = 0, and φ∘F_i is Lipschitz, satisfies |φF_i(a) − φF_i(a')| ≥ (m_i/Λ)|a − a'| for a, a' ∈ B_i, and is differentiable at each b ∈ B_i with injective derivative Dφ(F_i b)∘DF_i(b). Step 5 with Y := φ(M) gives HasApproximateTangentSpaceAt n φ(M) (φ x) (Dφ(x)(range DF_i(b))) for H^n-a.e. x = F_i(b) ∈ P_i. Since null sets correspond under φ, F_i and their inverses, for H^n-a.e. x ∈ M: (★) HasApproximateTangentSpaceAt n φ(M) φ(x) (Dφ(x)Q(x)).
7. Area formula on M. For every function g : E → [0, ∞] (no measurability of g is needed): ∫_{φ(M)} g dH^n = ∫_M g(φx)J(x) dH^n(x) (lower Lebesgue integrals), J(x) := J(Dφ(x), Q(x)). Both sides split over the disjoint Borel pieces, since Z and φ(Z) are null (Mathlib lintegral_iUnion needs measurable pieces but no measurability of the integrand). On a piece, by the weighted injective Lipschitz area formula for φ∘F_i and then for F_i: ∫_{φ(P_i)} g dH^n = ∫_{B_i} g(φF_ib)·normDet(Dφ(F_ib)∘DF_i(b)) db = ∫_{B_i} g(φF_ib)·normDet(Dφ(F_ib) restricted to range DF_i(b))·normDet(DF_i(b)) db (Mathlib LinearMap.normDet_comp) = ∫_{B_i} (g∘φ·J)(F_ib)·normDet(DF_i(b)) db (step 6, an a.e. equality in b, so lintegral_congr_ae applies) = ∫_{P_i} (g∘φ)·J dH^n; the SimonGMT weighted area formula weighted_area_formula_lipschitz_injOn takes an arbitrary weight g : F → [0, ∞]. J is H^n⌞M-a.e. strongly measurable: J(x)² = det(p(x)Dφ(x)*Dφ(x)p(x) + I − p(x)) (the operator equals (Dφ(x)*Dφ(x)) compressed to Q(x) on Q(x) and the identity on Q(x)^⊥), a continuous function of (p(x), Dφ(x)), and p is a.e. strongly measurable by the sibling imrep_approxTangent_starProjection_aesm. J > 0 a.e. because Dφ(x) is injective, and J ≤ ‖Dφ(x)‖^n ≤ Λ^n.
8. Induced orientation. For a.e. x ∈ M, ξ(x)(β) = s·β(τ) for all n-covectors β, with τ an orthonormal basis of Q(x) and s = ±1. Let L := Dφ(x), v_a := Lτ_a and Q' := LQ(x). Gram–Schmidt gives v = σA (v_b = Σ_a A_{ab}σ_a) with σ an orthonormal basis of Q' and A an invertible upper-triangular n×n matrix; multilinearity and alternation give β(v) = det(A)·β(σ) for all n-covectors β, and det(v_a·v_b) = det(AᵀA) = det(A)², so J(x) = |det A|. Define ζ(x) by ζ(x)(β) := ξ(x)(β∘Dφ(x)) = s·β(v) and ξ'(φ x) := ζ(x)/J(x). Then ξ'(φx)(β) = s·sign(det A)·β(σ) for all β, i.e. IsUnitOrientationOf (ξ'(φx)) (Dφ(x)Q(x)).
9. The representation. With ψ := φ^{-1}, define R' := (M', θ', ξ') by M' := φ(M), θ'(y) := θ(ψy), ξ'(y) := ζ(ψy)/J(ψy) (and 0 where J(ψy) = 0). Fields: M' is Borel (= ψ^{-1}(M), ψ continuous) and M' ⊆ φ(U) = U; M' is countably n-rectifiable (M' ⊆ φ(M_0) ∪ ⋃_j (φ∘F_j)(ℝ^n) with H^n(φ(M_0)) ≤ Λ^n·0 and φ∘F_j Lipschitz); θ' is measurable and ≥ 1 on M'; for compact C ⊆ U, ∫_{M'∩C} θ' dH^n = ∫_{M∩ψ(C)} θJ dH^n ≤ Λ^n ∫_{M∩ψ(C)} θ dH^n < ∞ (step 7 with g := θ'·1_C, ψ(C) compact ⊆ U); ξ' is H^n⌞M'-a.e. strongly measurable (composition of a.e. strongly measurable maps with ψ; null sets correspond); and by (★) and step 8, for H^n-a.e. y ∈ M' the vector ξ'(y) orients an approximate tangent plane of M' at y. So R' is an IMRep U n. Finally, fix ω ∈ 𝒟^n(U). The function h(y) := θ'(y)ξ'(y)(ω(y)) is H^n⌞M'-integrable: it is a.e. strongly measurable (θ' measurable, ξ' a.e. strongly measurable, ω continuous), and |ξ'(y)(β)| ≤ ‖β‖ for a.e. y ∈ M' (step 8: ξ'(y)(β) = ±β(σ) with σ orthonormal), so |h| ≤ sup‖ω‖·θ'·1_{tsupport ω}, which is integrable by the local integrability of θ' just shown. Likewise x ↦ θ(x)ξ'(φx)(ω(φx))J(x), which equals g_ω(x) a.e. on M, is H^n⌞M-integrable (step 2). Applying step 7 to g := max(h, 0) and g := max(−h, 0) (and subtracting): R'.action ω = ∫_{M'} θ'ξ'(ω) dH^n = ∫_M θ(x) ξ'(φx)(ω(φx)) J(x) dH^n(x) = ∫_M θ(x) ζ(x)(ω(φx)) dH^n(x) = ∫_M θ(x) ξ(x)(ω(φx)∘Dφ(x)) dH^n(x) = S(ω). Hence R' represents S, S is integer multiplicity, and steps 2–3 give the remaining conclusions.
10. Dimension zero. Every step above is valid for n = 0, where ℝ^0 = {0}, Lebesgue measure on ℝ^0 is the unit point mass and μHE[0] = μH[0] gives measure 1 to every singleton (Mathlib Measure.euclideanHausdorffMeasure_zero and Measure.hausdorffMeasure_zero_singleton). Step 3 is vacuous (BoundaryVanishes S is True in degree 0). In step 4, every map ℝ^0 → E is differentiable with injective derivative, so G_j = ℝ^0, m(A) = 1 and r(A) = 1/2 ≠ 0 for every A, each piece D_i is a single point, and the bi-Lipschitz inequality holds because a = a' for a, a' ∈ ℝ^0. In step 5, the only vector of ℝ^0 is c = 0, so the bounds involving m are trivial, (B − b)/r = {0} for B = {b}, the integrals over ℝ^0 are evaluations at 0, J_F = normDet of a map out of ℝ^0 equals 1 (Mathlib LinearMap.normDet_of_subsingleton), and range DF(b) = {0} has finrank 0 = n. In steps 7–8, Q(x) = {0}, J(x) = 1, the frames τ, σ and the matrix A are empty with det A = 1 (Mathlib Matrix.det_isEmpty), and β∘Dφ(x) = β for every 0-covector β (it takes no arguments), so ζ(x) = ξ(x) and ξ'(φx) = ξ(x), which orients {0} = Dφ(x)Q(x) because ξ(x) does. Hence R' of step 9 is an IMRep U 0 representing S, and the statement holds for every n, including n = 0.

## Key steps

1. φ is a bi-Lipschitz C¹ diffeomorphism with φ(U) = U; the integral formula defines a current S = φ_#T.
2. ∂S = 0 by approximating φ in C¹ by smooth maps φ_k, for which d commutes with pull-back, and dominated convergence.
3. A coercivity constant m(A) > 0 (unit-sphere minimum for n ≥ 1, m(A) = 1 for n = 0) gives the radius r(A) = m(A)/2 (1 for non-injective A), nonzero for every A as Mathlib's partition theorem requires; this splits M, up to a null set, into disjoint Borel pieces parametrized bi-Lipschitzly.
4. A density/blow-up argument identifies approximate tangent planes of M and of φ(M), giving T_{φx}φ(M) = Dφ(x)T_xM a.e.
5. The area formula on the pieces and the normalized push-forward orientation give an integer multiplicity representation of S; every step is checked in dimension 0.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (project b4d606d, mathlib 25730c7c)`
- `python3 -I: read nodes/root-minimizing-implies-stationary-a1/{parent-child-handoff.json,decomposition-v1.json,decomposition-audit-v1.json,decomposition-review-receipt-v1.json}`
- `python3 -I: list dag.json node ids and lean_name (56 nodes; no collision with the twelve child names)`
- `grep -n 'exists_partition_approximatesLinearOn_of_hasFDerivWithinAt' -A 25 mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `grep -rn 'theorem LinearMap.exists_antilipschitzWith' mathlib/Mathlib`
- `grep -n 'def normDet\|normDet_of_subsingleton\|normDet_comp\|normDet_sq_eq_det_gram\|euclideanHausdorffMeasure_image' mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `sed -n 1,100p mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean; grep -n hausdorffMeasure_zero_singleton mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `grep -rn 'MeasurableSet.image_of_continuousOn_injOn\|ae_tendsto_measure_inter_div\|hausdorffMeasure_image_le\|measurable_fderiv\|measurableSet_of_differentiableAt\|extDerivWithin_pullback\|det_isEmpty\|lintegral_iUnion\|to_localInverse\|toHomeomorph\|exists_isSubordinate' mathlib/Mathlib`
- `sed -n 1,420p simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `sed -n 1,140p simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean; grep -n areaJacobianAt simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `sed -n 60,110p simongmt/Poincare/SimonGMT/Chapter01/HausdorffDensityBounds.lean; sed -n 30,70p simongmt/Poincare/SimonGMT/Chapter02/AreaNormalization.lean`
- `sed -n 1,140p simongmt/Poincare/SimonGMT/Chapter06/Mass.lean; sed -n 95,140p simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean; sed -n 110,360p simongmt/Poincare/SimonGMT/Chapter06/Currents.lean; sed -n 25,125p simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `sed -n 1,75p book/chapter-07.txt; sed -n 400,440p book/chapter-06.txt; sed -n 760,880p book/chapter-06.txt`
- `lake env lean /tmp/mis-decomp-v2/Check.lean (import GMT.Ch07.Submission; 12 child types in namespace GMT.Ch07.Submission, minimizing_implies_stationary and a conditional assembly_check; #print axioms)`
- `lake env lean /tmp/mis-decomp-v2/Standalone.lean (same with the frozen contract inlined)`
- `lake env lean /tmp/mis-decomp-v2/Radius.lean (radius_check, pieces_check; #print axioms)`
- `lake env lean /tmp/mis-decomp-v2/Instances.lean (Gram Matrix.of, HasOrthogonalProjection instances, operator norm, μHE[0] singleton, normDet out of ℝ^0)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ApproximatesLinearOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaNormalization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/HausdorffDensityBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/mis-decomp-v2/Check.lean`
- `/tmp/mis-decomp-v2/Standalone.lean`
- `/tmp/mis-decomp-v2/Radius.lean`
- `/tmp/mis-decomp-v2/Instances.lean`

The local snapshot (project b4d606d, Mathlib 25730c7c) has no counterpart for the contract's IMRep push-forward, first variation or mean curvature, so the twelve children are new. The library facts they reuse are the ones cited in the child proofs. The only blocking defect from v1 is confirmed and repaired. Mathlib's exists_partition_approximatesLinearOn_of_hasFDerivWithinAt takes r : (E →L[ℝ] F) → ℝ≥0 with rpos : ∀ A, r A ≠ 0, and the unit-sphere minimum used in v1 does not exist for n = 0. The fix sets m(A) = 1 for n = 0 (alternatively 1/K from LinearMap.exists_antilipschitzWith, which also covers subsingleton domains) and r = 1 on non-injective maps; rpos then holds for every A. pieces_check compiles the resulting bi-Lipschitz partition for all n and P using only propext, Classical.choice and Quot.sound. The n = 0 facts used in the new step 10 exist: Measure.euclideanHausdorffMeasure_zero, Measure.hausdorffMeasure_zero_singleton, LinearMap.normDet_of_subsingleton and Matrix.det_isEmpty. The upper-density lemma needs only real n ≥ 0, and the SimonGMT area lemmas have no rank hypothesis and accept arbitrary weights. All twelve child types (eleven identical to v1) elaborate after import GMT.Ch07.Submission and also with the contract inlined. minimizing_implies_stationary compiles from them, and the conditional assembly uses only standard axioms. Inferred instances were verified: Matrix.of Gram matrix, Submodule.HasOrthogonalProjection.ofCompleteSpace and ContinuousLinearMap.hasOpNorm. No child name collides with any of the 56 DAG nodes.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
