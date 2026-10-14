<!-- theorem-id: gmt-ch07/root.compactness_of_minimizing_currents-a1.mass_representation-a1 -->

## Theorem `Submission.cmc_exists_massRepresentation`

Let P, n ∈ ℕ, U ⊆ ℝ^P open and T ∈ 𝒟_n(U) a current (SimonGMT GeometricCurrentOn U n) with M_W(T) < ∞ for every open W with closure(W) compact and contained in U. Then there are a Borel measure μ on ℝ^P and a map ξ from ℝ^P to n-vectors (continuous linear functionals on n-covectors) such that: μ(ℝ^P ∖ U) = 0; μ(K) < ∞ for every compact K ⊆ U; M_W(T) = μ(W) for every open W ⊆ ℝ^P; ξ is μ-a.e. strongly measurable; |ξ(x)(α)| ≤ |α| for every x and every n-covector α, where |α| is the Euclidean coefficient norm (covectorEuclideanNorm); T(ω) = ∫ ξ(x)(ω(x)) dμ(x) for every ω ∈ 𝒟ⁿ(U); and, if in addition M_W(∂T) < ∞ for every such W (boundaryMassOn, read as 0 when n = 0), then μ(E) = 0 for every set E ⊆ ℝ^P with Hⁿ(E) = 0 (Hⁿ = μHE[n]).

Node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/370

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/986, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2392, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1319, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4607, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4614, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4626, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4631, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4637, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4647, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4654, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4666, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4679

## Lean problem

Declaration: `Submission.cmc_exists_massRepresentation`

```lean
∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)
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

- Parent DAG node: `root.compactness_of_minimizing_currents-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, 2.7–2.8 (Riesz representation of currents of locally finite mass, chapter-06.txt lines 265–283), 2.35–2.37 (absolute continuity of normal currents, lines 606–660; printed pages 143–145). Simon proves 2.36 through the BV structure theorem 2.35 (which rests on BV compactness, Ch. 2, 2.6); here 2.35 is replaced by the elementary estimate of step 8 (mollification plus the Gagliardo–Nirenberg–Sobolev inequality, which is in Mathlib), and the rest of 2.36 is Simon's projection argument.

Notation. 𝒟ⁿ(U) is the space of test forms in U (TestFormOn U n). For an n-covector α on ℝ^P, |α| := covectorEuclideanNorm α = (Σ_I α(e_I)²)^{1/2}, the sum over strictly increasing I = (i_1 < ⋯ < i_n) in {1, …, P}, e_I := (e_{i_1}, …, e_{i_n}). Let 𝕀 be the finite set of these I and H := EuclideanSpace ℝ 𝕀; the map c(α) := (α(e_I))_{I∈𝕀} is a linear isomorphism onto H — injective because an alternating form is determined by its values on increasing tuples of basis vectors, surjective because the coordinate covectors dx^I(v_1, …, v_n) := det((v_j)^{i_k})_{k,j} (built from Mathlib's determinant of the matrix of coordinates, an alternating multilinear map) satisfy dx^I(e_J) = δ_{IJ} — and |α| = ‖c(α)‖_H; every n-covector is α = Σ_I α(e_I) dx^I. If n > P then 𝕀 = ∅ and every n-covector is 0 (any n > P vectors are linearly dependent, and alternating maps vanish on linearly dependent families, Mathlib AlternatingMap.map_linearDependent). For a form ω put |ω|_∞ := sup_x |ω(x)|. An n-vector (MultiVector P n) is a continuous linear functional on n-covectors; ⟨α, ζ⟩ := ζ(α).

Elementary facts used below.
(E1) If ω ∈ 𝒟ⁿ(U), tsupport ω ⊆ W with W open and W ⊂⊂ U, then |T(ω)| ≤ |ω|_∞·M_W(T). Proof: if |ω|_∞ = 0 then ω = 0. Otherwise ±ω/|ω|_∞ are admissible for M_W(T) (massAdmissibleOn), so ±T(ω)/|ω|_∞ ≤ M_W(T).
(E2) For a 1-covector β and a k-covector γ, |β ∧ γ| ≤ |β||γ|; for an orthogonal projection (or any linear map with orthonormal coordinate structure) p_α : ℝ^P → ℝⁿ, x ↦ (x^{i_1}, …, x^{i_n}), and a k-covector γ on ℝⁿ, |p_α^#γ| = |γ|. Proof: k!|γ|² = Σ_{i_1,…,i_k} γ(e_{i_1}, …, e_{i_k})² (each increasing tuple occurs k! times up to sign; tuples with repetitions vanish), and the right side is the Hilbert–Schmidt norm of the multilinear form γ, which does not depend on the orthonormal basis; so |·| is invariant under orthogonal changes of coordinates; rotate so that β = |β|e^1; then β∧γ = |β| Σ_{I∌1} γ_I e^1∧e^I and its norm is |β|(Σ_{I∌1}γ_I²)^{1/2} ≤ |β||γ|. For p_α, p_α^# maps the coordinate covector e^J of ℝⁿ (J ⊆ {1..n}) to the coordinate covector e^{α(J)} of ℝ^P, an isometric embedding of the orthonormal bases.
(E3) If ζ is a unit simple n-vector or more generally |⟨α, ζ⟩| ≤ |α| for all α, then for every form ω, |⟨ω(x), ζ⟩| ≤ |ω(x)|.

Proof.

Part I: representation, properties (1)–(6) of the statement (μ Uᶜ = 0, finiteness on compacts, M_W(T) = μ(W), measurability, |ξ| ≤ 1, T(ω) = ∫⟨ω, ξ⟩ dμ).

1. (Trivial case n > P.) Then every n-covector vanishes (Notation), every test form is 0, T = 0, M_W(T) = 0 for all W; μ := 0 and ξ := 0 satisfy all assertions, including the last one. Assume n ≤ P.

2. (Extension to continuous forms.) Let X := U with the subspace topology (open in ℝ^P, hence locally compact, Hausdorff and second countable). For g ∈ C_c(X, H) let g̃ : ℝ^P → (n-covectors) be g̃(x) := c^{-1}(g(x)) for x ∈ U and g̃(x) := 0 otherwise; g̃ is continuous with compact support spt g ⊆ U. Fix a compact set C ⊆ U containing spt g and an open W with C ⊆ W ⊂⊂ U (e.g. W := thickening δ C = {x : ∃ y ∈ C, |x − y| < δ} with 2δ < infDist(C, ℝ^P ∖ U), δ := 1 if U = ℝ^P; W = ∅ if C = ∅, in which case g = 0 and L(g) := 0). Let (φ_σ)_{σ>0} be a standard mollifier on ℝ^P (C^∞, ≥ 0, ∫φ_σ = 1, support in the closed σ-ball; Mathlib ContDiffBump.normed). For 0 < σ < dist(C, ℝ^P ∖ W), g_σ := g̃ ∗ φ_σ (componentwise in the coordinates α(e_I)) is C^∞ with tsupport g_σ ⊆ C + B̄_σ ⊆ W, so g_σ ∈ 𝒟ⁿ(U); g_σ → g̃ uniformly as σ ↓ 0 (uniform continuity of g̃); and |g_σ(x)| ≤ ∫|g̃(x − y)|φ_σ(y) dy ≤ |g̃|_∞ (convexity of the norm). By (E1), |T(g_σ) − T(g_τ)| ≤ |g_σ − g_τ|_∞ M_W(T) → 0, so L(g) := lim_{σ↓0} T(g_σ) exists. More generally, if (h_k), (h'_k) are sequences in 𝒟ⁿ(U) with supports in a fixed open W' ⊂⊂ U and h_k, h'_k → g̃ uniformly, then |T(h_k) − T(h'_k)| ≤ |h_k − h'_k|_∞ M_{W'}(T) → 0 (E1); since the union of two open sets compactly contained in U is again compactly contained in U, L(g) does not depend on the mollifier or on C, W. Consequently: (a) L : C_c(X, H) → ℝ is linear; (b) L(ω|_U) = T(ω) for every ω ∈ 𝒟ⁿ(U) (constant sequence); (c) |L(g)| ≤ |g̃|_∞ M_W(T) = sup‖g‖_H · M_W(T) whenever spt g ⊆ W ⊂⊂ U, W open. In particular L is locally bounded in the sense of SimonGMT IsLocallyBoundedCcFunctional: for compact C ⊆ X choose W ⊂⊂ U open with C ⊆ W; then L(g) ≤ M_W(T) < ∞ whenever ‖g‖ ≤ 1 and spt g ⊆ C.

3. (Riesz representation.) By SimonGMT Chapter01 simon_theorem_4_14_caratheodory (X locally compact Hausdorff, H a finite-dimensional, hence separable, real inner product space, L locally bounded) there are the Radon measure μ₀ := vectorFunctionalEnvelopeMeasure L on X (regular, finite on compact sets: vectorFunctionalEnvelopeMeasure_isRadon) and ν : X → H, measurable for the Carathéodory σ-algebra of μ₀, with ‖ν‖ = 1 μ₀-a.e. and L(g) = ∫⟨g(x), ν(x)⟩_H dμ₀(x) for all g ∈ C_c(X, H) (the Carathéodory extension agrees with μ₀ on Borel sets). Moreover (simon_theorem_4_14_positive_envelope) for every f ∈ C_c(X, ℝ_{≥0}),
 (3a) sup{L(g) : g ∈ C_c(X, H), ‖g(x)‖ ≤ f(x) ∀x} = ∫ f dμ₀.
Passage to a Borel version: μ₀ is σ-finite (X is σ-compact and μ₀ is finite on compact sets), so every set measurable for the Carathéodory σ-algebra of the outer measure of μ₀ is μ₀-null-measurable, and the Carathéodory measure radonCaratheodoryMeasure μ₀ has the same null sets as μ₀ and agrees with it on Borel sets (SimonGMT Chapter01 radonCaratheodoryMeasure_apply and integral_radonCaratheodoryMeasure). Hence ν agrees μ₀-a.e. with a Borel map ν_B, and L(g) = ∫⟨g, ν_B⟩ dμ₀ for g ∈ C_c(X, H) (the integrand is Borel); redefine ν_B := 0 on the Borel μ₀-null set where ‖ν_B‖ ≠ 1, so ‖ν_B(x)‖ ≤ 1 for all x and the representation of L is unchanged.

4. (Definition of μ and ξ.) Let μ be the push-forward of μ₀ under the inclusion U ↪ ℝ^P, a Borel measure on ℝ^P with μ(ℝ^P ∖ U) = 0 and μ(C) = μ₀(C) < ∞ for every compact C ⊆ U. For x ∈ U let ξ(x) be the n-vector α ↦ ⟨c(α), ν_B(x)⟩_H, and ξ(x) := 0 for x ∉ U. Then ξ is Borel (finite-dimensional target), hence a.e. strongly measurable for μ, and |ξ(x)(α)| ≤ ‖c(α)‖‖ν_B(x)‖ ≤ |α| for all x, α (Cauchy–Schwarz). For ω ∈ 𝒟ⁿ(U), step 2(b) and step 3 give T(ω) = L(ω|_U) = ∫_U ⟨c(ω(x)), ν_B(x)⟩ dμ₀ = ∫ ξ(x)(ω(x)) dμ(x), the integrand being bounded by |ω|_∞ 1_{tsupport ω}, which is μ-integrable.

5. (M_W(T) = μ(W) for open W.) Upper bound: if ω is admissible for M_W(T) (tsupport ω ⊆ W, |ω| ≤ 1) then T(ω) = ∫ξ(ω) dμ ≤ μ(tsupport ω) (a finite real number, since ξ(x)(ω(x)) ≤ |ω(x)| ≤ 1_{tsupport ω}(x)), so ofReal(T(ω)) ≤ μ(tsupport ω) ≤ μ(W) in [0, ∞]. Hence M_W(T) = sup ofReal(T(ω)) ≤ μ(W). Lower bound: μ(W) = μ₀(W ∩ U) = sup{μ₀(C) : C ⊆ W ∩ U compact} (inner regularity of the Radon measure μ₀ on the open set W ∩ U). Fix such C and ε > 0. Choose f ∈ C_c(X, [0, 1]) with f = 1 on C and spt f ⊆ W ∩ U (Urysohn). By (3a) there is g ∈ C_c(X, H) with ‖g‖ ≤ f and L(g) ≥ ∫ f dμ₀ − ε ≥ μ₀(C) − ε. Mollify as in step 2 with σ < dist(spt f, ℝ^P ∖ (W ∩ U)): g_σ ∈ 𝒟ⁿ(U), tsupport g_σ ⊆ W ∩ U, |g_σ| ≤ 1, and T(g_σ) → L(g). So for small σ, g_σ is admissible for M_W(T) and T(g_σ) ≥ μ₀(C) − 2ε. Hence M_W(T) ≥ μ₀(C) − 2ε, and M_W(T) ≥ μ(W). (Both sides may be ∞.)

6. Steps 4 and 5 give all assertions except the last. In particular, for every open G and every ω ∈ 𝒟ⁿ(U) with tsupport ω ⊆ G and |ω| ≤ 1, T(ω) ≤ μ(G), and the following uniqueness fact holds: (U1) if two finite signed Borel measures κ, κ' on an open set G satisfy ∫ b dκ = ∫ b dκ' for all b ∈ C_c^∞(G), then κ = κ' on Borel subsets of G (for compact C ⊆ G, smooth 0 ≤ b_k ≤ 1 with b_k ↓ 1_C pointwise and supports in a fixed compact subset of G exist; dominated convergence gives κ(C) = κ'(C); compact sets form a π-system generating the Borel σ-algebra of G and both are finite).

Part II: absolute continuity (the last assertion). Assume M_W(∂T) < ∞ (boundaryMassOn) for every open W ⊂⊂ U. If n = 0, μHE[0] = μH[0] is the counting measure (Mathlib euclideanHausdorffMeasure_zero, hausdorffMeasure_zero_singleton), so μHE[0](E) = 0 forces E = ∅ and μ(E) = 0. If n > P, μ = 0 (step 1). Assume 1 ≤ n ≤ P.

7. (Reduction.) Let E ⊆ ℝ^P with Hⁿ(E) = 0 (Hⁿ := μHE[n]). Hⁿ is Borel regular, so there is a Borel E' ⊇ E with Hⁿ(E') = 0; replacing E by E' ∩ U (μ(ℝ^P ∖ U) = 0) we may assume E is Borel and E ⊆ U. μ is a Borel measure on ℝ^P which is finite on compact subsets of the open set U and vanishes outside U, hence inner regular on Borel sets (it is locally finite on the σ-compact Polish space U); so it suffices to show μ(C) = 0 for every compact C ⊆ U with Hⁿ(C) = 0. Fix such C and an open W with C ⊆ W ⊂⊂ U (as in step 2). Then μ(W) = M_W(T) < ∞ and M_W(∂T) < ∞.

8. (Lemma TD: top-dimensional normal measures are absolutely continuous.) Let 1 ≤ n, let m be a finite signed Borel measure on ℝⁿ with compact support, and suppose
 Λ := sup{|∫ div g dm| : g ∈ C_c^∞(ℝⁿ; ℝⁿ), |g(y)| ≤ 1 ∀y} < ∞.
Then |m|(N) = 0 for every Lⁿ-null set N ⊆ ℝⁿ.
Proof. Let u_σ := φ_σ ∗ m, i.e. u_σ(y) := ∫ φ_σ(y − z) dm(z), with φ_σ a mollifier on ℝⁿ; u_σ is C^∞ with compact support (in spt m + B̄_σ) and ∂_j u_σ(y) = ∫ ∂_jφ_σ(y − z) dm(z) (differentiation under the integral, m finite). For g ∈ C_c^∞(ℝⁿ; ℝⁿ), Fubini gives ∫ ∇u_σ · g dy = ∫∫ ∇φ_σ(y − z)·g(y) dy dm(z) = −∫ div(φ̌_σ ∗ g) dm with (φ̌_σ ∗ g)(z) := ∫ φ_σ(y − z) g(y) dy, a smooth compactly supported field with |φ̌_σ ∗ g| ≤ 1 when |g| ≤ 1. Hence |∫∇u_σ·g| ≤ Λ for all such g, and since ∇u_σ is continuous with compact support, ∫|∇u_σ| dy ≤ Λ (take g_k := χ_k ∇u_σ/(|∇u_σ|² + 1/k)^{1/2} with smooth cut-offs χ_k ↑ 1, |g_k| ≤ 1, and use monotone convergence). If n ≥ 2, the Gagliardo–Nirenberg–Sobolev inequality (Mathlib MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one, applied on ℝⁿ with p = n/(n−1), the Hölder conjugate of n = finrank ℝⁿ, and ‖fderiv u_σ‖ = |∇u_σ|) gives ‖u_σ‖_{L^{n/(n−1)}} ≤ C_n Λ. If n = 1, u_σ(y) = ∫_{−∞}^y u_σ' so sup|u_σ| ≤ Λ. For a ∈ C_c^∞(ℝⁿ), Fubini gives ∫ u_σ a dy = ∫ (φ̌_σ ∗ a) dm → ∫ a dm as σ ↓ 0 (φ̌_σ ∗ a → a uniformly and |m| is finite). By Hölder, |∫ a dm| ≤ C_n Λ ‖a‖_{L^n} (n ≥ 2), resp. ≤ Λ‖a‖_{L^1} (n = 1). For an open set G, |m|(G) = sup{∫ a dm : a ∈ C_c^∞(G), |a| ≤ 1} (Hahn decomposition and inner regularity of the finite Borel measure |m| on G, approximating 1_{P∩C} − 1_{N∩C} for compact C by smooth functions and dominated convergence), hence |m|(G) ≤ C_nΛ Lⁿ(G)^{1/n}, resp. ≤ Λ L¹(G). If Lⁿ(N) = 0, outer regularity of Lⁿ gives open G ⊇ N with Lⁿ(G) arbitrarily small, so |m|(N) = 0. ∎

9. (Projection argument; Simon 2.36.) For a multi-index α = (i_1 < ⋯ < i_n) ∈ 𝕀 let p_α : ℝ^P → ℝⁿ, x ↦ (x^{i_1}, …, x^{i_n}), and dx^α := dx^{i_1} ∧ ⋯ ∧ dx^{i_n}. p_α is 1-Lipschitz, so Hⁿ(p_α(C)) ≤ Hⁿ(C) = 0 (Mathlib LipschitzOnWith.hausdorffMeasure_image_le), and Hⁿ = Lⁿ on ℝⁿ (μHE[n] on EuclideanSpace ℝ (Fin n) is the volume, Mathlib Geometry/Euclidean/Volume); so N_α := p_α(C) is a compact Lⁿ-null set. Let λ_α be the finite signed Borel measure on W given by dλ_α := ⟨dx^α, ξ⟩ dμ⌞W (|⟨dx^α, ξ⟩| ≤ |dx^α| = 1, μ(W) < ∞). For b ∈ C_c^∞(W) let m_{α,b} := (p_α)_*(b λ_α), a finite signed measure on ℝⁿ supported in p_α(spt b) (compact). For g ∈ C_c^∞(ℝⁿ; ℝⁿ) put γ := Σ_j g_j ε_j with ε_j := (−1)^{j−1} dy^1 ∧ ⋯ ∧ dy^{j−1} ∧ dy^{j+1} ∧ ⋯ ∧ dy^n (the factor dy^j omitted), so that dγ = (div g) dy and |γ(y)| = |g(y)|. Then p_α^#((div g)dy) = d(p_α^#γ), and by step 4 (applied to the test form b·p_α^#((div g) dy) ∈ 𝒟ⁿ(U), supported in spt b ⊆ W):
 ∫ div g dm_{α,b} = ∫ b(x)(div g)(p_α x)⟨dx^α, ξ(x)⟩ dμ(x) = T(b·d(p_α^#γ)) = T(d(b p_α^#γ)) − T(db ∧ p_α^#γ) = ∂T(b p_α^#γ) − T(db ∧ p_α^#γ).
By (E1) and (E2) (|p_α^#γ| = |γ| ≤ 1, |db ∧ p_α^#γ| ≤ |db|), the absolute value is ≤ |b|_∞ M_W(∂T) + |db|_∞ M_W(T) < ∞ whenever |g| ≤ 1. By step 8, |m_{α,b}|(N_α) = 0, i.e.
 ∫_{p_α^{-1}(N_α)} b dλ_α = m_{α,b}(N_α) = 0 for every b ∈ C_c^∞(W).
By (U1) applied to the finite signed measures 1_{p_α^{-1}(N_α)}λ_α and 0 on W, λ_α(B ∩ p_α^{-1}(N_α)) = 0 for every Borel B ⊆ W; since C ⊆ p_α^{-1}(N_α), ∫_C h dλ_α = 0 for every bounded Borel h on W.

10. (Conclusion.) Let ω be admissible for M_W(T) and write ω = Σ_{α∈𝕀} ω_α dx^α with ω_α ∈ C_c^∞(W). By step 4 and step 9 (h := ω_α),
 T(ω) = Σ_α ∫ ω_α dλ_α = Σ_α ∫_C ω_α dλ_α + ∫_{W∖C} ξ(ω) dμ = ∫_{W∖C} ξ(ω) dμ ≤ μ(W ∖ C).
Taking the supremum, μ(W) = M_W(T) ≤ μ(W ∖ C); since μ(W) < ∞, μ(C) = 0. By step 7, μ(E) = 0 for every E with Hⁿ(E) = 0. ∎

## Key steps

1. Extend T by mollification to a locally bounded linear functional L on C_c(U; Λⁿ) with |L(g)| ≤ sup|g|·M_W(T).
2. Apply the SimonGMT vector Riesz theorem (simon_theorem_4_14_caratheodory) to get μ₀ and a unit field ν; push μ₀ to ℝ^P and set ξ(x)(α) := ⟨c(α), ν(x)⟩.
3. M_W(T) = μ(W): ≤ from the representation; ≥ from the positive-envelope identity, inner regularity, Urysohn and mollification.
4. Lemma TD: a compactly supported signed measure on ℝⁿ whose distributional gradient has finite mass is absolutely continuous (mollify, Gagliardo–Nirenberg–Sobolev for n ≥ 2, direct bound for n = 1).
5. Simon 2.36: push T⌞b dx^α forward by the coordinate projections p_α; TD shows these measures do not charge p_α(C) for Hⁿ-null compact C, hence M_W(T) ≤ μ(W ∖ C) and μ(C) = 0; inner regularity finishes.

## Reference use

### local-project

Queries:
- `cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; cmp GMT/Ch07/Contract.lean .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `rg -n 'cmc_|dtc_vanish_off_support' local-references/123e8435b4a2469b/project (no match); rg -c sorry local-references/123e8435b4a2469b/project/GMT -g '*.lean'`
- `rg -n -i 'federer.?fleming|deformation theorem|flat norm' local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean' (no match); rg -n 'theorem eLpNorm_le_eLpNorm_fderiv_one|theorem tendsto_measure_thickening_of_isClosed' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n -i 'federer|deformation|flat (norm|metric|convergence)|slice|slicing|closure theorem|boundary rectifiab' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06`
- `python3 scan of dag.json: lean_name, lean_statement, status and children of all 451 nodes; collisions of the twelve proposed names; accepted nodes with matching types (dtc_vanish_off_support, dor_ims_massOn_le_measure, dor_ims_measure_le_massOn, regcomp_approx_tangent_locality, regcomp_covector_eval_orthonormal_le, rsdic_unitOrientation_eq_or_eq_neg, dtc_isIntegerMultiplicity_sub); cross-branch reuse edges`
- `grep compactness_of_minimizing cluster-state/logs/gmt-ch07/*.log; comparison of swarm-configs/3cda86c657b24789a5e2370499838a03.json and e19a0116cbcc4eccb5496520b27c492f.json (max_nodes 200 vs 1000); node-directory timestamps at the v3 and v4 audit times`
- `sed -n 1300,1700p and 1801,2000p /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py; grep -n 'def _existing_lean_name_problem' -A 40 runtime.py; grep -n 'def ensure' -A 35 store.py`
- `grep for declarations simon_theorem_4_14_caratheodory, simon_theorem_4_14_positive_envelope, vectorFunctionalEnvelopeMeasure_isRadon, radonCaratheodoryMeasure_apply, integral_radonCaratheodoryMeasure, IsLocallyBoundedCcFunctional, simon_theorem_4_16_compact_metrizable, simon_theorem_3_6, simon_remark_3_7_hausdorff, simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure, simonHausdorffMeasureReal_toOuterMeasure, simon_theorem_3_3, simon_theorem_3_26_i, exists_isClosed_continuousOn_of_measurable, area_image_criticalSet_eq_zero, injective_area_formula_lipschitzOn, weighted_area_formula_lipschitzOn_fiberSum, exteriorDerivativeOn_pullbackFormWithin, countablyRectifiable_of_measure_zero, HasApproximateTangentSpaceAt.unique, WeaklyConvergesOn.boundary, WeaklyConvergesOn.massOn_le_liminf, affinePushforward in lake-packages-25730c7c/simongmt/Poincare`
- `grep for declarations Monotone.ae_differentiableAt, measurable_deriv, MonotoneOn.intervalIntegrable_deriv, MonotoneOn.intervalIntegral_deriv_mem_uIcc, LipschitzWith.ae_differentiableAt, LipschitzOnWith.hausdorffMeasure_image_le, exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, LinearMap.exists_antilipschitzWith, MeasurableSet.image_of_continuousOn_injOn, LipschitzOnWith.extend_real, LipschitzOnWith.extend_pi, Besicovitch.exists_disjoint_closedBall_covering_ae, VitaliFamily.ae_tendsto_average_norm_sub, isMulLeftInvariant_eq_smul, tendstoUniformlyOn_of_ae_tendsto, LipschitzWith.integral_lineDeriv_mul_eq, eLpNorm_le_eLpNorm_fderiv_one, euclideanHausdorffMeasure_zero, hausdorffMeasure_smul₀, tendsto_measure_thickening_of_isClosed, countable_meas_level_set_pos, Integrable.integral_eq_integral_meas_lt, SmoothPartitionOfUnity.exists_isSubordinate, exists_contDiff_tsupport_subset, ContDiffBump.normed, AlternatingMap.map_linearDependent, Vitali.exists_disjoint_subfamily_covering_enlargement, RealRMK.rieszMeasure, ext_of_generate_finite, ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable, hausdorffMeasure_zero_singleton, Besicovitch.tendsto_filterAt in lake-packages-25730c7c/mathlib/Mathlib`
- `lake env lean /tmp/cmc-a5/lean/TypesFinal.lean; lake env lean /tmp/cmc-a5/lean/AssemblyFinal.lean; lake env lean /tmp/cmc-a5/lean/Inst.lean; lake env lean /tmp/cmc-a5/lean/Names.lean; lake env lean /tmp/cmc-a5/lean/Names2.lean`
- `git -C lake-packages-25730c7c/simongmt rev-parse HEAD; git -C lake-packages-25730c7c/mathlib rev-parse HEAD`
- `sed -n 176,260p book/chapter-07.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1/decomposition-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1/decomposition-audit-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1/decomposition-audit-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1/decomposition-review-receipt-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/3cda86c657b24789a5e2370499838a03.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/e19a0116cbcc4eccb5496520b27c492f.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/cluster-state/logs/gmt-ch07/3cda86c657b24789a5e2370499838a03.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/cluster-state/logs/gmt-ch07/e19a0116cbcc4eccb5496520b27c492f.log`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/GeometricPointProduct.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonPolarRepresentation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/VectorFunctionalEnvelope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonCaratheodoryIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/CompactMetrizableCompactness.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/HausdorffDensityBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Measure/Haar/Unique.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/cmc-a5/final.json`
- `/tmp/cmc-a5/scripts/build_final.py`
- `/tmp/cmc-a5/scripts/gen_types_final.py`
- `/tmp/cmc-a5/scripts/gen_assembly.py`
- `/tmp/cmc-a5/scripts/body.lean`
- `/tmp/cmc-a5/lean/TypesFinal.lean`
- `/tmp/cmc-a5/lean/AssemblyFinal.lean`
- `/tmp/cmc-a5/lean/Inst.lean`
- `/tmp/cmc-a5/lean/Names.lean`
- `/tmp/cmc-a5/lean/Names2.lean`

The snapshot contract (manifest: project b4d606db, mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean, and each snapshot chapter contract has only its frozen final sorry; the pinned packages are SimonGMT 2b366308 and Mathlib 25730c7c. SimonGMT Chapter06 says Federer–Fleming compactness remains a separate obligation and contains only point slices of products. Neither SimonGMT nor the snapshot Mathlib has a closure, deformation, Lipschitz-slicing or flat-convergence theorem (rg: no match). These results, Riesz representation and absolute continuity of normal currents, and IM calculus therefore remain children with complete parent-written proofs. Reusable library facts: WeaklyConvergesOn.massOn_le_liminf and WeaklyConvergesOn.boundary, the Chapter01 Riesz, compactness, density and Lusin theorems, the Chapter02 area formulas and the Chapter03 rectifiability API. Every SimonGMT and Mathlib declaration cited by name in the child proofs exists in the pinned sources. The 451-node DAG contains no cmc_ name, and the snapshot project has no cmc_ or dtc_ name. dtc_vanish_off_support is a comparator-accepted node whose frozen type equals the vanish_off_support child type, so it is reused verbatim; accepted declarations covering parts of mass_equals_rep_measure and im_calculus are named in remarks. In the workspace build, all 12 exact child types elaborate after import GMT.Ch07.Submission. The conditional assembly of CompactnessOfMinimizingCurrents from the six used child types depends only on propext, Classical.choice and Quot.sound, and current subtraction uses the contract instance. The identical previously accepted split was dropped only by the runtime node bound (max_nodes = 200 with about 200 DAG nodes); the current configuration allows 1000 nodes. Book lines 176–260 confirm the two corrections used in local_comparison.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
