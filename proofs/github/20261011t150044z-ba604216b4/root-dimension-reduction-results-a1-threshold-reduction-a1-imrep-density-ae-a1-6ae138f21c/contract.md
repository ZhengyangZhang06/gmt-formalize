<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.threshold_reduction-a1.imrep_density_ae-a1 -->

## Theorem `Submission.dimred_tr_imrep_density_ae`

Let P, n ∈ ℕ, let V ⊆ ℝ^P be any set and let R = (M, θ, ξ) be an integer multiplicity triple in V (IMRep V n: M ⊆ V Borel and countably n-rectifiable, θ : ℝ^P → ℕ Borel with θ ≥ 1 on M, ξ orienting the approximate tangent space of M at Hⁿ-a.e. point of M, Hⁿ = μHE[n]), with weight μ_R = θHⁿ⌞M (R.measure). Let W ⊆ ℝ^P be open and assume μ_R(K ∩ W) < ∞ for every compact K ⊆ ℝ^P. Then for Hⁿ-a.e. x ∈ ℝ^P, μ_R(B_ρ(x) ∩ W)/(ω_nρⁿ) → 1_{M∩W}(x)·θ(x) in [0, ∞] as ρ ↓ 0, where B_ρ(x) is the open ball, ω_n = unitBallVolume n and the denominator is written unitBallVolume n · ofReal(ρⁿ) (division in [0, ∞]).

Node: `root.dimension_reduction_results-a1.threshold_reduction-a1.imrep_density_ae-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1030

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5283, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1255, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1257, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8653

## Lean problem

Declaration: `Submission.dimred_tr_imrep_density_ae`

```lean
∀ (P n : ℕ) (V W : Set (Euclid P)) (R : IMRep V n), IsOpen W → (∀ K : Set (Euclid P), IsCompact K → R.measure (K ∩ W) ≠ ∞) → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), Tendsto (fun ρ : ℝ => R.measure (ball x ρ ∩ W) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 (Set.indicator (R.carrier ∩ W) (fun y => (R.mult y : ℝ≥0∞)) x))
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

- Parent DAG node: `root.dimension_reduction_results-a1.threshold_reduction-a1`
- Child DAG node: `root.dimension_reduction_results-a1.threshold_reduction-a1.imrep_density_ae-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 3(iii), "μ_A = ϑ_A·Hⁿ as measures on ℝ^P". That step cites Simon Ch. 3, Remark 1.5(3), Remark 1.8 and Theorem 1.9 (the density equals θ on the carrier) and Ch. 1, Theorem 3.6 with Remark 3.7(2) (the upper density vanishes off the carrier). The printed arguments are reproduced and specialized to integer multiplicities; the level sets of θ replace Lusin's theorem in Remark 1.8(1). The upper density theorem is proved first, as Lemma U in Step 0.


Step 0 (Lemma U; formerly the separate sibling upper_density_zero of attempt 4, merged here because this child is its only user). Within this step the letters below denote the objects of Lemma U only.
Lemma U (Simon Ch. 1, Theorem 3.6 with Remark 3.7(2)). Let P, n ∈ ℕ, let μ be a Borel measure on ℝ^P (Euclid P) with μ(K) < ∞ for every compact K ⊆ ℝ^P, and let A ⊆ ℝ^P be a Borel set with μ(ℝ^P ∖ A) = 0. Then for μHE[n]-almost every x ∈ ℝ^P with x ∉ A, μ(B̄_ρ(x))/ofReal(ρ)ⁿ → 0 in [0, ∞] as ρ ↓ 0, where B̄_ρ(x) is the closed ball.
Proof of Lemma U.
Source: Simon Ch. 1, Theorem 3.6 with Remark 3.7(2), the fact "the upper density vanishes Hⁿ-a.e. off the carrier" cited in parent step 3(iii). The printed proof is reproduced for a locally finite Borel measure: density comparison (Ch. 1, 3.2) via the Vitali covering lemma (Ch. 1, 3.3), inner regularity by closed sets, then localization.

The same argument, written for μ = μHE[n]⌞S with μHE[n](S) < ∞, is the comparator-accepted declaration Submission.regcomp_atl_upper_density_zero of DAG node root.regular_components_are_minimizing-a1.approx_tangent_locality-a1.upper_density_zero-a1 (candidate 031b5125695febe04a82aacb729a15164ef02960). These accepted declarations are reading references only. They are not dependencies of this child and are not in its worktree, and the numbered proof below is self-contained. Their Lean proofs show the same Vitali and comparison steps with μHE[n](S ∩ ·) in place of λ(·); Submission.regcomp_atl_local_density_zero shows the localization by balls. The SimonGMT lemmas simon_theorem_3_6 and simon_remark_3_7_of_openSigmaFinite are not used: they live in Poincare/SimonGMT/Chapter01/DensityComparison.lean, which the frozen header does not import.

Notation. Hⁿ := μHE[n] = c_n·μH[n] with c_n := addHaarScalarFactor(volume, μH[n]) ∈ (0, ∞) (Measure.euclideanHausdorffMeasure_def, Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero). So Hⁿ and μH[n] have the same null sets. For a measure λ, x ∈ ℝ^P and ρ > 0 put r_λ(x, ρ) := λ(B̄_ρ(x))/ofReal(ρ)ⁿ ∈ [0, ∞]; ofReal(ρ)ⁿ ∈ (0, ∞) for ρ > 0.

U1. (Comparison lemma, Simon 3.2 with the crude constant 6ⁿ.) Let λ be a Borel measure, G a Borel set with λ(G) < ∞, t ∈ (0, ∞) and E ⊆ ℝ^P. Assume that for every x ∈ E and every δ > 0 there is ρ ∈ (0, δ) with t·ofReal(ρ)ⁿ ≤ λ(G ∩ B̄_ρ(x)). Then t·μH[n](E) ≤ 6ⁿ·λ(G).
Proof. Fix j ∈ ℕ and put δ_j := 1/(j + 1).
(a) Vitali selection. Consider the family of pairs a = (x_a, ρ_a) with x_a ∈ E, 0 < ρ_a < δ_j and t·ofReal(ρ_a)ⁿ ≤ λ(G ∩ B̄_{ρ_a}(x_a)), with the closed balls B̄_{ρ_a}(x_a) (nonempty) and radii ρ_a ≤ δ_j. Mathlib's Vitali.exists_disjoint_subfamily_covering_enlargement with τ = 2 gives a pairwise disjoint subfamily u_j such that every ball of the family meets some ball b ∈ u_j with ρ_a ≤ 2ρ_b. The balls of u_j are disjoint with nonempty interior, so u_j is countable (Set.PairwiseDisjoint.countable_of_nonempty_interior).
(b) Covering. For x ∈ E the hypothesis with δ = δ_j gives a member a = (x, ρ) of the family. Let b ∈ u_j be a ball meeting B̄_ρ(x) at a point w, with ρ ≤ 2ρ_b. Then |x − x_b| ≤ |x − w| + |w − x_b| ≤ ρ + ρ_b ≤ 3ρ_b. So E ⊆ ⋃_{b∈u_j} B̄_{3ρ_b}(x_b), and diam B̄_{3ρ_b}(x_b) ≤ 6ρ_b ≤ 6δ_j (ediam_le_of_forall_dist_le).
(c) Packing. By disjointness,
t·Σ_{b∈u_j} ofReal(ρ_b)ⁿ ≤ Σ_{b∈u_j} λ(G ∩ B̄_{ρ_b}(x_b)) = λ(⋃_{b∈u_j} G ∩ B̄_{ρ_b}(x_b)) ≤ λ(G)
(measure_biUnion). Hence t·Σ_{b∈u_j} diam(B̄_{3ρ_b}(x_b))ⁿ ≤ 6ⁿ·λ(G) for every j.
(d) Limit. Mathlib's MeasureTheory.Measure.hausdorffMeasure_le_liminf_tsum applies to the covers {B̄_{3ρ_b}(x_b) : b ∈ u_j} of E, whose diameters are ≤ 6δ_j → 0. It gives μH[n](E) ≤ liminf_j Σ_{b∈u_j} diam(B̄_{3ρ_b}(x_b))ⁿ ≤ 6ⁿλ(G)/t (ENNReal.le_div_iff_mul_le with t ∉ {0, ∞}). Multiplying by t gives the claim. For n = 0 the same computation holds with every n-th power equal to 1.

U2. (Finite measures.) Let λ be a finite Borel measure and A′ a Borel set with λ(A′ᶜ) = 0. Then for Hⁿ-a.e. x ∉ A′, r_λ(x, ρ) → 0 as ρ ↓ 0.
Proof.
(a) Thresholds. For t ∈ (0, ∞) let N_t := {x : x ∉ A′ and t < r_λ(x, ρ) for ρ frequently in 𝓝[>]0}. Suppose x ∉ A′ and r_λ(x, ·) does not tend to 0. By ENNReal.tendsto_nhds_zero there is ε > 0 with ε < r_λ(x, ρ) frequently. Choosing k with 1/(k + 1) < ε (ENNReal.exists_inv_nat_lt) gives x ∈ N_{1/(k+1)}. By measure_iUnion_null it therefore suffices to show Hⁿ(N_t) = 0 for every t ∈ (0, ∞), and for that it suffices to show μH[n](N_t) = 0.
(b) Fix t and ε′ ∈ (0, ∞). The finite Borel measure λ on the metric space ℝ^P is weakly regular (Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure). MeasurableSet.exists_isClosed_sdiff_lt (the current name of the deprecated exists_isClosed_diff_lt) gives a closed F ⊆ A′ with λ(A′ ∖ F) < t·ε′/6ⁿ. Put G := A′ ∖ F; it is Borel and λ(G) < ∞.
(c) Let x ∈ N_t and δ > 0. Then x ∉ F, since F ⊆ A′. As F is closed, some r₁ > 0 has B_{r₁}(x) ∩ F = ∅. Since the threshold holds frequently and ρ ∈ (0, min(δ, r₁/2)) holds eventually in 𝓝[>]0, pick ρ satisfying both (Frequently.and_eventually). Then B̄_ρ(x) ∩ F = ∅. As λ(A′ᶜ) = 0, λ(B̄_ρ(x)) = λ(A′ ∩ B̄_ρ(x)) = λ(G ∩ B̄_ρ(x)). From t < r_λ(x, ρ) and 0 < ofReal(ρ)ⁿ < ∞ (ENNReal.lt_div_iff_mul_lt) we get t·ofReal(ρ)ⁿ < λ(G ∩ B̄_ρ(x)).
(d) Step U1 with E := N_t gives t·μH[n](N_t) ≤ 6ⁿλ(G) < 6ⁿ·(tε′/6ⁿ) = tε′. Hence μH[n](N_t) < ε′. As ε′ > 0 is arbitrary, μH[n](N_t) = 0, and Hⁿ(N_t) = c_n·0 = 0.

U3. (Localization; the statement.) For j ∈ ℕ let λ_j := μ.restrict (A ∩ B_j(0)), where B_j(0) is the open ball.
- λ_j is finite: λ_j(ℝ^P) = μ(A ∩ B_j(0)) ≤ μ(B̄_j(0)) < ∞, as B̄_j(0) is compact.
- λ_j((A ∩ B_j(0))ᶜ) = 0.
By step U2 for each j and ae_all_iff, Hⁿ-a.e. x satisfies: for every j, if x ∉ A ∩ B_j(0) then r_{λ_j}(x, ρ) → 0.
Fix such an x with x ∉ A. Choose j ∈ ℕ with |x| < j and put ε := (j − |x|)/2 > 0, so B̄_ε(x) ⊆ B_j(0). For 0 < ρ < ε, since μ(Aᶜ) = 0,
μ(B̄_ρ(x)) = μ(A ∩ B̄_ρ(x)) = μ(A ∩ B_j(0) ∩ B̄_ρ(x)) = λ_j(B̄_ρ(x)).
So r_μ(x, ρ) = r_{λ_j}(x, ρ) on (0, ε), a set in 𝓝[>]0. Since x ∉ A ∩ B_j(0), r_{λ_j}(x, ·) → 0, and therefore r_μ(x, ρ) → 0 as ρ ↓ 0 (Tendsto.congr′). This holds for Hⁿ-a.e. x ∉ A, which is the claim. ∎

Main argument.
Notation.
- Hⁿ := μHE[n].
- ω_n := unitBallVolume n = volume(B_1(0) ⊆ Euclid n) ∈ (0, ∞): a nonempty bounded open set under Lebesgue measure; for n = 0 it equals 1.
- M′ := M ∩ W, a Borel set.
- μ := R.measure.restrict W, so μ(B) = R.measure(B ∩ W) = ∫_{M′∩B} θ dHⁿ for Borel B.
- ν := Hⁿ.restrict M′.
- q(x, ρ) := μ(B_ρ(x))/(ω_n·ofReal(ρⁿ)) for ρ > 0.
Since balls are Borel, R.measure(B_ρ(x) ∩ W) = μ(B_ρ(x)) (Measure.restrict_apply). Also 1_{M′}(x)θ(x) = Set.indicator (R.carrier ∩ W) (fun y ↦ (R.mult y : ℝ≥0∞)) x. So the claim is: q(x, ρ) → 1_{M′}(x)θ(x) as ρ ↓ 0 for Hⁿ-a.e. x.

1. (Local finiteness and concentration.)
- μ(K) = R.measure(K ∩ W) < ∞ for every compact K, by hypothesis.
- θ ≥ 1 on M, so ν(B) = Hⁿ(M′ ∩ B) ≤ ∫_{M′∩B} θ dHⁿ = μ(B) for Borel B; in particular ν(K) < ∞ for compact K.
- R.measure = (Hⁿ⌞M).withDensity θ vanishes off M, and μ vanishes off W, so μ(M′ᶜ) = 0. Likewise ν(M′ᶜ) = 0.
- For ρ ≥ 0, ofReal(ρⁿ) = ofReal(ρ)ⁿ (ENNReal.ofReal_pow), and B_ρ(x) ⊆ B̄_ρ(x). Hence, for every measure λ, λ(B_ρ(x))/(ω_n·ofReal(ρⁿ)) ≤ ω_n⁻¹·λ(B̄_ρ(x))/ofReal(ρ)ⁿ.
 (†) So the open-ball ratio, normalized by ω_n, tends to 0 whenever the closed-ball ratio λ(B̄_ρ(x))/ofReal(ρ)ⁿ does.

2. (Off the carrier.) Apply Lemma U (Step 0) to the measure μ and the Borel set M′. Its hypotheses hold by step 1. It gives an Hⁿ-null set E₀ such that for x ∉ M′ ∪ E₀, μ(B̄_ρ(x))/ofReal(ρ)ⁿ → 0. By (†), q(x, ρ) → 0 = 1_{M′}(x)θ(x).

3. (Unit density at approximate-tangent points; Simon Ch. 3, Remark 1.5(3).) By the IMRep field orients, for Hⁿ-a.e. x ∈ M there is a subspace Q with HasApproximateTangentSpaceAt n M x Q (in particular finrank Q = n). By definition this means: ∫_{blowUpMap x ρ '' M} f dHⁿ → ∫_Q f dHⁿ as ρ ↓ 0 for every f ∈ C_c(ℝ^P, ℝ), where blowUpMap x ρ (p) = ρ⁻¹(p − x). Let E′ ⊆ M be the Hⁿ-null set of points of M where this fails. Fix x ∈ M′ ∖ E′, the subspace Q, and δ > 0 with B_{2δ}(x) ⊆ W (W is open). Write η_ρ := blowUpMap x ρ. Claim: ν(B_ρ(x))/(ω_n·ofReal(ρⁿ)) → 1.
(a) Scaling. For every set A, Hⁿ(η_ρ(A)) = ofReal(ρ⁻¹)ⁿ·Hⁿ(A). Indeed η_ρ(A) = ρ⁻¹ • (A − x). The translation y ↦ y − x is an isometry, so it preserves Hⁿ (Isometry.euclideanHausdorffMeasure_image applied to (IsometryEquiv.subRight x).isometry), and Hⁿ(c • B) = ‖c‖₊ⁿ·Hⁿ(B) for c ≠ 0 (Measure.euclideanHausdorffMeasure_smul₀). This combination compiles after import GMT.Ch07.Submission. (MeasureTheory.euclideanHausdorffMeasure_homothety_image concerns y ↦ x + c(y − x) and can also be used after rewriting.)
(b) For 0 < ρ < δ, M ∩ B_{2ρ}(x) = M′ ∩ B_{2ρ}(x). Hence:
 - η_ρ(M) ∩ B_2(0) = η_ρ(M′ ∩ B_{2ρ}(x));
 - Hⁿ(η_ρ(M) ∩ B_1(0)) = ofReal(ρ)⁻ⁿ·ν(B_ρ(x));
 - Hⁿ(η_ρ(M) ∩ B_2(0)) = ofReal(ρ)⁻ⁿ·ν(B_{2ρ}(x)) < ∞.
(c) Fix 0 < ε < 1 and take continuous f^±: ℝ^P → [0, 1] with compact support:
 - f⁺(p) := min(1, max(0, (1 + ε − |p|)/ε)), which is 1 on B̄_1(0) and 0 off B_{1+ε}(0) ⊆ B_2(0);
 - f⁻(p) := min(1, max(0, (1 − |p|)/ε)), which is 1 on B̄_{1−ε}(0) and 0 off B_1(0).
 Both are integrable over η_ρ(M), since they are bounded and supported in B_2(0), which has finite measure by (b). As 1_{B_1(0)} lies between f⁻ and f⁺, the following holds as real numbers. All quantities are finite by (b), and the measure values are compared through toReal.
 ∫_{η_ρ(M)} f⁻ dHⁿ ≤ (Hⁿ(η_ρ(M) ∩ B_1(0))).toReal = (ofReal(ρ)⁻ⁿ·ν(B_ρ(x))).toReal ≤ ∫_{η_ρ(M)} f⁺ dHⁿ.
(d) Hⁿ(Q ∩ B_t(0)) = ω_n·tⁿ for t > 0. Indeed, Q with the induced inner product is an n-dimensional inner product space, and the inclusion Q → ℝ^P is an isometry (Isometry.euclideanHausdorffMeasure_image). Hⁿ on Q is its volume (InnerProductSpace.euclideanHausdorffMeasure_eq_volume with finrank Q = n). An orthonormal basis gives a linear isometry Q ≃ Euclid n, which preserves volume. In Euclid n the ball of radius t > 0 has volume ofReal(tⁿ)·ω_n (Measure.addHaar_ball_of_pos, which needs no nontriviality, so n = 0 is included). Since 1_{B̄_{1−ε}(0)} ≤ f⁻ and f⁺ ≤ 1_{B_{1+ε}(0)},
 ω_n(1 − ε)ⁿ ≤ ∫_Q f⁻ dHⁿ and ∫_Q f⁺ dHⁿ ≤ ω_n(1 + ε)ⁿ.
(e) Let ρ ↓ 0 in (c), using the approximate-tangent convergence for f^±. This gives
 ω_n(1 − ε)ⁿ ≤ liminf ν(B_ρ(x))/ofReal(ρⁿ) ≤ limsup ν(B_ρ(x))/ofReal(ρⁿ) ≤ ω_n(1 + ε)ⁿ.
 Then let ε ↓ 0 and divide by ω_n ∈ (0, ∞); this proves the claim.

4. (Density θ on the carrier; Simon Ch. 3, Remark 1.8.) For m ≥ 1 let M′_m := {p ∈ M′ : θ(p) = m} and A_m := M′ ∖ M′_m; both are Borel. Since θ is ℕ-valued and ≥ 1 on M, M′ = ⋃_{m≥1} M′_m (disjoint union).
Fix m. The measures μ.restrict A_m and ν.restrict A_m are finite on compact sets (step 1) and vanish off A_m. Apply Lemma U (Step 0) to each of them with the set A_m. This gives an Hⁿ-null set E_m such that, for x ∉ A_m ∪ E_m:
 μ(A_m ∩ B̄_ρ(x))/ofReal(ρ)ⁿ → 0 and ν(A_m ∩ B̄_ρ(x))/ofReal(ρ)ⁿ → 0.
By (†), the corresponding open-ball ratios normalized by ω_n also tend to 0.
Now let x ∈ M′_m ∖ (E_m ∪ E′); note M′_m ⊆ ℝ^P ∖ A_m. For ρ ∈ (0, δ) all terms below are finite, and
 μ(B_ρ(x)) = μ(M′_m ∩ B_ρ(x)) + μ(A_m ∩ B_ρ(x))
 = m·ν(M′_m ∩ B_ρ(x)) + μ(A_m ∩ B_ρ(x))
 = m·[ν(B_ρ(x)) − ν(A_m ∩ B_ρ(x))] + μ(A_m ∩ B_ρ(x)).
The first equality holds because μ vanishes off M′ = M′_m ∪ A_m; the second because θ = m on M′_m. Dividing by ω_n·ofReal(ρⁿ) and using step 3 together with the two vanishing ratios gives q(x, ρ) → m·1 − m·0 + 0 = m = θ(x) = 1_{M′}(x)θ(x). This is arithmetic of finite limits, for example after passing to toReal.

5. (Conclusion.) The set E₀ ∪ E′ ∪ ⋃_{m≥1} E_m is Hⁿ-null (countable union). Outside it, q(x, ρ) → 1_{M′}(x)θ(x) as ρ ↓ 0: by step 2 if x ∉ M′, and by step 4 with m = θ(x) if x ∈ M′. ∎

## Key steps

1. Lemma U (Simon 1.3.6, 3.7(2)): Vitali comparison t·μH[n](E) ≤ 6ⁿλ(G), inner regularity by closed sets for finite measures, and localization to balls give vanishing upper density Hⁿ-a.e. off a set carrying a locally finite measure.
2. μ := R.measure⌞W and ν := Hⁿ⌞(M ∩ W) are finite on compact sets (θ ≥ 1 on M) and concentrated on M′ = M ∩ W; open-ball ratios normalized by ω_n are bounded by closed-ball ratios.
3. Off M′: Lemma U applied to (μ, M′) gives zero density Hⁿ-a.e. off M′.
4. At Hⁿ-a.e. x ∈ M′ the carrier has an approximate tangent plane Q. Testing with cut-offs of B_1(0), using Hⁿ(η_{x,ρ}A) = ρ^{−n}Hⁿ(A) and Hⁿ(Q ∩ B_t) = ω_ntⁿ, gives ν(B_ρ(x))/(ω_nρⁿ) → 1.
5. Split M′ into the Borel level sets {θ = m}. Lemma U applied to μ⌞A_m and ν⌞A_m, with A_m = M′ ∖ {θ = m}, makes the other levels negligible, so the ratio tends to m = θ(x) at Hⁿ-a.e. point of {θ = m}.
6. The countable union of exceptional sets is Hⁿ-null.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD`
- `sha256sum GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `grep -n 'theorem hausdorffMeasure_image_le' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `grep -n 'addHaarScalarFactor_volume_hausdorffMeasure_ne_zero\|theorem euclideanHausdorffMeasure_def' <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -c dimred_tr_ <snapshot>/project (exit 1, no match); rg -l dimred_tr_ GMT .lake/packages/simongmt/Poincare --glob '*.lean' (exit 1, no match)`
- `grep -n 'def HasApproximateTangentSpaceAt' -A 14 and grep -n 'def blowUpMap' -A 5 .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `sed -n 85,125p .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean (VanishesOn, zeroRegion, support)`
- `python3 inspection of dag.json: status, candidate_commit and lean_statement of the selected node, of its registered dependencies im_mass_measure, monotonicity and moving_blowups, of root.abstract_dimension_reduction-a1 and of the six reused nodes; string comparison of the children's leading premises with these frozen types`
- `python3 /tmp/tr-a7/scripts/check_reuse_types.py dag.json (git show <candidate>:GMT/Ch07/Submission.lean, declared type vs dag.json up to whitespace, sorry occurrences); git cat-file -e <candidate>^{commit}; isolated-comparator-result.json and comparator-v1.log of the six reused nodes`
- `python3 /tmp/tr-a7/scripts/graph_check.py decomposition-v6.json dag.json 5000 12 (replica of _dependency_problem, _existing_lean_name_problem and the max_nodes bound)`
- `lake env lean /tmp/tr-a7/lean/Types.lean; lake env lean /tmp/tr-a7/lean/Assembly.lean; lake env lean /tmp/tr-a7/lean/TangentCheck.lean`
- `python3 reading of decomposition-v1..v6.json, decomposition-audit-v*.json, decomposition-review-receipt-v*.json and decomposition-scope-v*.json of the selected node; grep -l 'threshold_reduction' cluster-state/logs/gmt-ch07/*.log; max_nodes in .humanize/swarm-configs/9619fab3de46466e954c3c0e22455dff.json and 53f9bac0ca76443b9b296465895cebc9.json`
- `gh api repos/humanfia/math-lean-flow/contents/_recursive_lean/{runtime,store,github_runtime,decomposition_scope}.py?ref=feature/humanize-api-update-claude; grep -n '_decompose\|_solve_children\|_existing_lean_name_problem\|_overlay_accepted_children\|_reference_use_problem\|def ensure' on the fetched copies`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1/decomposition-v6.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1/decomposition-audit-v6.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1/decomposition-review-receipt-v5.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1/decomposition-scope-v6.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-stationary-of-minimizing-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-density-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-cone-measure-homogeneous-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-scaling-a1-rep-pushforward-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/9619fab3de46466e954c3c0e22455dff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/53f9bac0ca76443b9b296465895cebc9.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/cluster-state/logs/gmt-ch07/9619fab3de46466e954c3c0e22455dff.log`
- `/tmp/tr-a7/lean/Types.lean`
- `/tmp/tr-a7/lean/Assembly.lean`
- `/tmp/tr-a7/lean/TangentCheck.lean`
- `/tmp/tr-a7/scripts/graph_check.py`
- `/tmp/tr-a7/scripts/check_reuse_types.py`
- `/tmp/tr7-mlf/runtime.py`

Pins match. The snapshot manifest records project b4d606d and mathlib 25730c7c, equal to the workspace HEAD and to .lake/packages/mathlib; simongmt is 2b36630 as pinned in lakefile.toml. The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).

Library facts the children use exist where cited:
- The snapshot mathlib has LipschitzWith.hausdorffMeasure_image_le (Hausdorff.lean:745), used in the parent assembly.
- It has addHaarScalarFactor_volume_hausdorffMeasure_ne_zero (Measure.lean:96), used for the normalization Hⁿ = c_n·μH[n].
- SimonGMT's HasApproximateTangentSpaceAt (Rectifiable.lean:102) and support = U ∖ zeroRegion are as the children's proofs use them. zeroRegion is a union of open sets with compact closure in U on which the current vanishes (CurrentLocalEquality.lean:99–117).

No dimred_tr_ identifier exists in the snapshot project, GMT, SimonGMT or dag.json.

The six reused declarations are accepted, and their candidate commits are present. Their dag.json types equal the children's lean_statements and the candidates' declarations (up to whitespace). Each candidate's only sorry is the frozen main_theorem, and each isolated comparator result passed.

Lean checks:
- All 12 child types elaborate after import GMT.Ch07.Submission.
- The parent assembly compiles from exactly the three registered dependencies, abstract_dimension_reduction and the three new children it uses, with no sorryAx.
- The tangent child compiles from exactly its four reused siblings.

The graph and name replica passes against the current 2327-node DAG, with room for 6 new nodes under max_nodes = 5000.

Attempt 6 was audited acceptable. It failed activation only because the old worker's max_nodes was 1000, below the DAG size, so it is resubmitted unchanged.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
