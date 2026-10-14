<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.threshold_reduction-a1.imrep_density_ae-a1.density_on_carrier-a1 -->

## Theorem `Submission.dimred_tr_ida_density_on_carrier`

Let P, n ∈ ℕ, let V ⊆ ℝ^P be any set and let R = (M, θ, ξ) be an integer multiplicity triple in V (IMRep V n: M ⊆ V Borel and countably n-rectifiable, θ : ℝ^P → ℕ Borel with θ ≥ 1 on M, ξ orienting the approximate tangent space of M at Hⁿ-a.e. point of M, Hⁿ = μHE[n]), with weight μ_R = θHⁿ⌞M (R.measure). Let W ⊆ ℝ^P be open and assume μ_R(K ∩ W) < ∞ for every compact K ⊆ ℝ^P. Then for Hⁿ-a.e. x ∈ ℝ^P with x ∈ M ∩ W, μ_R(B_ρ(x) ∩ W)/(ω_nρⁿ) → θ(x) in [0, ∞] as ρ ↓ 0. Here B_ρ(x) is the open ball, ω_n = unitBallVolume n, and the denominator is written unitBallVolume n · ofReal(ρⁿ) (division in [0, ∞]).

Node: `root.dimension_reduction_results-a1.threshold_reduction-a1.imrep_density_ae-a1.density_on_carrier-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7930

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5283, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1255, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1257

Decomposition children: None

## Lean problem

Declaration: `Submission.dimred_tr_ida_density_on_carrier`

```lean
∀ (P n : ℕ) (V W : Set (Euclid P)) (R : IMRep V n), IsOpen W → (∀ K : Set (Euclid P), IsCompact K → R.measure (K ∩ W) ≠ ∞) → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ R.carrier ∩ W → Tendsto (fun ρ : ℝ => R.measure (ball x ρ ∩ W) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 (R.mult x : ℝ≥0∞))
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

- Parent DAG node: `root.dimension_reduction_results-a1.threshold_reduction-a1.imrep_density_ae-a1`
- Child DAG node: `root.dimension_reduction_results-a1.threshold_reduction-a1.imrep_density_ae-a1.density_on_carrier-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1, 3 and 4 of the parent proof (node root.dimension_reduction_results-a1.threshold_reduction-a1.imrep_density_ae-a1). These are Simon Ch. 3, Remark 1.5(3), Remark 1.8 and Theorem 1.9, specialized to integer multiplicities: the level sets of θ replace Lusin's theorem in Remark 1.8(1). Two sub-arguments of the parent proof are supplied by siblings.
- Step 3 of the parent proof is the unit density of the carrier at approximate-tangent points. It is supplied by unweighted_density_one, the accepted declaration Submission.rsd_tendsto_closedBall_density_of_approxTangent. Its accepted proof is step 3's argument on closed balls: the scaling Hⁿ(η_{x,r}A) = r⁻ⁿHⁿ(A), Hⁿ(Q ∩ B̄_t(0)) = ω_ntⁿ, and radial cut-offs. The passage to open balls is supplied by closed_to_open_ball_density (Submission.rsd_tendsto_ball_density_of_closedBall).
- Lemma U, with (†), is supplied by the sibling upper_density_zero. This is the accepted declaration Submission.idtp_dema_upper_density_zero, reused at its exact type.
The parent's step 4 applies Lemma U to both μ⌞A_m and ν⌞A_m. Below it is applied once per level, to μ. The ν-term is then controlled by ν ≤ μ (step 1(c)), which gives the same estimate. The parent's identity μ(B) = m·[ν(B) − ν(A_m ∩ B)] + μ(A_m ∩ B) is used in the subtraction-free form of two inequalities in [0, ∞] (step 6).

Siblings used (exact statements):
- upper_density_zero: for every measure λ on ℝ^P with λ(K) < ∞ for all compact K, and every Borel A ⊆ ℝ^P: for Hⁿ-a.e. x with x ∉ A, λ(A ∩ B_ρ(x))/(ω_n·ofReal(ρⁿ)) → 0 as ρ ↓ 0.
- unweighted_density_one: if s > 0, Hⁿ(M ∩ B̄_s(x)) ≠ ∞ and HasApproximateTangentSpaceAt n M x Q, then Hⁿ(M ∩ B̄_ρ(x))/(ω_n·ofReal(ρⁿ)) → 1 as ρ ↓ 0.
- closed_to_open_ball_density: for every measure ν′, point x and θ′ ∈ [0, ∞], if ν′(B̄_ρ(x))/(ω_n·ofReal(ρⁿ)) → θ′, then ν′(B_ρ(x))/(ω_n·ofReal(ρⁿ)) → θ′.

Notation.
- Hⁿ := μHE[n] on ℝ^P.
- M := R.carrier, Borel by the field measurableSet_carrier.
- θ := R.mult : ℝ^P → ℕ, measurable by the field measurable_mult, with θ ≥ 1 on M by the field mult_pos.
- M′ := M ∩ W, Borel since W is open.
- μ := R.measure⌞W, i.e. μ(S) = R.measure(S ∩ W) for Borel S.
- ν := Hⁿ⌞M′.
- c(ρ) := ω_n·ofReal(ρⁿ) with ω_n := unitBallVolume n.
- B_ρ(x) is the open ball and B̄_ρ(x) the closed ball.
- All limits are taken as ρ ↓ 0 (filter 𝓝[>] 0) in [0, ∞].
Since R.measure = (Hⁿ⌞M).withDensity θ (definition IMRep.measure), we have R.measure(S′) = ∫_{S′∩M} θ dHⁿ for Borel S′ (withDensity_apply, Measure.restrict_restrict).

1. (Local finiteness and concentration; parent step 1.)
(a) For Borel S: μ(S) = R.measure(S ∩ W) = ∫_{S∩W∩M} θ dHⁿ = ∫_{S∩M′} θ dHⁿ (Measure.restrict_apply).
(b) For compact K: μ(K) = R.measure(K ∩ W) < ∞ by hypothesis (Measure.restrict_apply', W Borel).
(c) For Borel S: ν(S) = Hⁿ(S ∩ M′) = ∫_{S∩M′} 1 dHⁿ ≤ ∫_{S∩M′} θ dHⁿ = μ(S), because θ(y) ≥ 1 for y ∈ M′ ⊆ M (setLIntegral_mono').

2. (Level sets; parent step 4.) For k ∈ ℕ let A_k := M′ ∩ θ⁻¹(ℕ ∖ {k}). In the parent's notation this is A_k = M′ ∖ M′_k, where M′_k = {p ∈ M′ : θ(p) = k}. It is Borel, since M′ is Borel and θ is measurable.

3. (Upper densities; parent step 4, via Lemma U.) Apply upper_density_zero with λ := μ, which is finite on compact sets by 1(b), and the Borel set A_k. For each k this gives: for Hⁿ-a.e. x with x ∉ A_k, e_k(ρ) := μ(A_k ∩ B_ρ(x))/c(ρ) → 0. As there are countably many k (ae_all_iff), for Hⁿ-a.e. x this holds simultaneously for every k with x ∉ A_k.

4. (Approximate tangent planes; parent step 3.) The field orients of R says: for (Hⁿ⌞M)-a.e. x there is a subspace Q with HasApproximateTangentSpaceAt n M x Q (and IsUnitOrientationOf (R.orient x) Q, which is not needed). As M is Borel, this means (ae_restrict_iff'): for Hⁿ-a.e. x, if x ∈ M then such a Q exists.

5. (Unit density of ν; parent step 3.) Let x ∈ M′ = M ∩ W be a point at which steps 3 and 4 hold; this is the case for Hⁿ-a.e. x ∈ M′. Fix Q as in step 4.
- W is open and x ∈ W, so there is r > 0 with B_r(x) ⊆ W. Put s := r/2 > 0. Then B̄_ρ(x) ⊆ B̄_s(x) ⊆ W for 0 < ρ ≤ s.
- Hence B̄_ρ(x) ∩ M′ = M ∩ B̄_ρ(x) for 0 < ρ ≤ s (parent step 3(b)).
- Hⁿ(M ∩ B̄_s(x)) = ν(B̄_s(x)) ≤ μ(B̄_s(x)) < ∞, by 1(c), 1(b) and compactness of B̄_s(x).
- unweighted_density_one, applied to M, x, Q and s, gives Hⁿ(M ∩ B̄_ρ(x))/c(ρ) → 1.
- For 0 < ρ ≤ s, ν(B̄_ρ(x)) = Hⁿ(B̄_ρ(x) ∩ M′) = Hⁿ(M ∩ B̄_ρ(x)) (Measure.restrict_apply). Since (0, s] belongs to 𝓝[>] 0, ν(B̄_ρ(x))/c(ρ) → 1 (Tendsto.congr').
- closed_to_open_ball_density, applied to the measure ν with θ′ = 1, gives b(ρ) := ν(B_ρ(x))/c(ρ) → 1.

6. (Splitting the ball; parent step 4.) With x as in step 5, let k := θ(x); then k ≥ 1, as x ∈ M. Let T := θ⁻¹({k}), a Borel set. Then x ∉ A_k, so e_k(ρ) → 0 by step 3. Fix ρ and write B := B_ρ(x), a Borel set.
- (B ∩ M′) ∖ T = (A_k ∩ B) ∩ M′, directly from the definitions.
- By 1(a), μ(B) = ∫_{B∩M′} θ dHⁿ. Splitting B ∩ M′ along T (lintegral_inter_add_sdiff) and using θ ≡ k on T (setLIntegral_congr_fun, lintegral_const), together with 1(a) for the Borel set A_k ∩ B, gives
 μ(B) = ∫_{(B∩M′)∩T} θ dHⁿ + ∫_{(B∩M′)∖T} θ dHⁿ = k·Hⁿ((B ∩ M′) ∩ T) + μ(A_k ∩ B).
- Similarly (measure_inter_add_sdiff), ν(B) = Hⁿ(B ∩ M′) = Hⁿ((B ∩ M′) ∩ T) + ν(A_k ∩ B).
Now use Hⁿ((B ∩ M′) ∩ T) ≤ Hⁿ(B ∩ M′) = ν(B) and ν(A_k ∩ B) ≤ μ(A_k ∩ B) (1(c)). This gives, for every ρ:
 (U) μ(B) ≤ k·ν(B) + μ(A_k ∩ B);
 (L) k·ν(B) ≤ μ(B) + k·μ(A_k ∩ B).
These two inequalities are the parent's identity μ(B) = m·[ν(B) − ν(A_m ∩ B)] + μ(A_m ∩ B), with m = k, written without subtraction in [0, ∞].

7. (Limits.) The quantity in the statement is R.measure(B_ρ(x) ∩ W)/c(ρ) = μ(B_ρ(x))/c(ρ) =: a(ρ), because the open ball is Borel (Measure.restrict_apply). Divide (U) and (L) by c(ρ) (ENNReal.div_le_div_right, ENNReal.add_div, mul_div_assoc). This gives, for every ρ,
 k·b(ρ) − k·e_k(ρ) ≤ a(ρ) ≤ k·b(ρ) + e_k(ρ),
where the left inequality is (L) rewritten with truncated subtraction (tsub_le_iff_right). Since k ∈ ℕ is finite, b(ρ) → 1 and e_k(ρ) → 0, we get:
- k·b(ρ) + e_k(ρ) → k·1 + 0 = k (ENNReal.Tendsto.const_mul, Tendsto.add);
- k·b(ρ) − k·e_k(ρ) → k − 0 = k (ENNReal.Tendsto.sub, the limit k being finite).
By the squeeze theorem, a(ρ) → k = θ(x).

8. (Conclusion.) Every x ∈ M ∩ W at which the conclusion fails lies in the union of the Hⁿ-null exceptional sets of steps 3 and 4. Hence for Hⁿ-a.e. x with x ∈ M ∩ W, R.measure(B_ρ(x) ∩ W)/(ω_n·ofReal(ρⁿ)) → θ(x) as ρ ↓ 0. The argument uses no case distinction on n, so n = 0 is included; V plays no role. ∎

Appendix (verified Lean realization of the numbered proof above; context, not part of the numbered proof). The declaration below compiles with Lean v4.35.0-rc3 and Mathlib 25730c7c after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the frozen contract's `open` commands (`open Filter Function Set MeasureTheory Metric`, `open scoped ENNReal Topology`, `open Poincare.SimonGMT.Chapter06`, `open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt)`). It requires the three sibling declarations to be present: Submission.idtp_dema_upper_density_zero, Submission.rsd_tendsto_closedBall_density_of_approxTangent and Submission.rsd_tendsto_ball_density_of_closedBall. It was checked together with the accepted proofs of these three declarations, taken from candidates ee6fe01ff88a4fae79345889f39a366b44e8e0b9, dbef2c15948a21d9574315bea458a9edb4f708e3 and c3ca64f29e6259bb0947d084036f55b096f91e3f. The comments `-- Step k` refer to the numbered steps above. It is a single declaration with no helper lemmas, and `#print axioms Submission.dimred_tr_ida_density_on_carrier` reports only propext, Classical.choice and Quot.sound.

```lean
theorem Submission.dimred_tr_ida_density_on_carrier : ∀ (P n : ℕ) (V W : Set (Euclid P)) (R : IMRep V n), IsOpen W → (∀ K : Set (Euclid P), IsCompact K → R.measure (K ∩ W) ≠ ∞) → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ R.carrier ∩ W → Tendsto (fun ρ : ℝ => R.measure (ball x ρ ∩ W) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 (R.mult x : ℝ≥0∞)) := by
  intro P n V W R hW hfin
  have hWm : MeasurableSet W := hW.measurableSet
  set M := R.carrier with hM
  have hMm : MeasurableSet M := R.measurableSet_carrier
  set M' := M ∩ W with hM'
  have hM'm : MeasurableSet M' := hMm.inter hWm
  set μ : Measure (Euclid P) := R.measure.restrict W with hμ
  set ν : Measure (Euclid P) := (μHE[n] : Measure (Euclid P)).restrict M' with hν
  -- Step 1: μ is finite on compact sets, μ is a set integral over M', and ν ≤ μ
  have hμfin : ∀ K : Set (Euclid P), IsCompact K → μ K ≠ ∞ := by
    intro K hK
    rw [hμ, Measure.restrict_apply' hWm]
    exact hfin K hK
  have hmeas : ∀ S : Set (Euclid P), MeasurableSet S →
      μ S = ∫⁻ y in S ∩ M', (R.mult y : ℝ≥0∞) ∂μHE[n] := by
    intro S hS
    rw [hμ, Measure.restrict_apply hS]
    simp only [IMRep.measure]
    rw [withDensity_apply _ (hS.inter hWm), Measure.restrict_restrict (hS.inter hWm)]
    have hSet : S ∩ W ∩ M = S ∩ M' := by
      ext y
      simp only [hM', mem_inter_iff]
      tauto
    rw [hSet]
  have hνle : ∀ S : Set (Euclid P), MeasurableSet S → ν S ≤ μ S := by
    intro S hS
    rw [hmeas S hS, hν, Measure.restrict_apply hS]
    calc μHE[n] (S ∩ M') = ∫⁻ _y in S ∩ M', (1 : ℝ≥0∞) ∂μHE[n] := by simp
      _ ≤ ∫⁻ y in S ∩ M', (R.mult y : ℝ≥0∞) ∂μHE[n] := by
        apply setLIntegral_mono' (hS.inter hM'm)
        intro y hy
        have h := R.mult_pos y hy.2.1
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr h.ne'
  -- Step 2: the level sets A k = M' ∖ {θ = k}
  set A : ℕ → Set (Euclid P) := fun k => M' ∩ R.mult ⁻¹' ({k}ᶜ) with hA
  have hAm : ∀ k, MeasurableSet (A k) := fun k =>
    hM'm.inter (R.measurable_mult (measurableSet_singleton k).compl)
  -- Step 3: upper densities of μ on the other levels (sibling upper_density_zero)
  have hUD : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), ∀ k : ℕ, x ∉ A k →
      Tendsto (fun ρ : ℝ => μ (A k ∩ ball x ρ) /
        (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 0) :=
    ae_all_iff.2 fun k => Submission.idtp_dema_upper_density_zero P n μ (A k) (hAm k) hμfin
  -- Step 4: approximate tangent planes (field orients)
  have htan : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ M →
      ∃ Q, HasApproximateTangentSpaceAt n M x Q := by
    have h := R.orients
    rw [ae_restrict_iff' hMm] at h
    filter_upwards [h] with x hx hxM
    obtain ⟨Q, hQ, -⟩ := hx hxM
    exact ⟨Q, hQ⟩
  filter_upwards [hUD, htan] with x hxUD hxtan hxMW
  obtain ⟨hxM, hxW⟩ := hxMW
  obtain ⟨Q, hQ⟩ := hxtan hxM
  -- Step 5: a closed ball around x inside W
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 hW x hxW
  have hs : 0 < r / 2 := by positivity
  have hsW : closedBall x (r / 2) ⊆ W := (closedBall_subset_ball (by linarith)).trans hrW
  have hloc : ∀ ρ : ℝ, ρ ≤ r / 2 → closedBall x ρ ∩ M' = M ∩ closedBall x ρ := by
    intro ρ hρ
    ext y
    simp only [hM', mem_inter_iff]
    constructor
    · rintro ⟨hyB, hyM, -⟩
      exact ⟨hyM, hyB⟩
    · rintro ⟨hyM, hyB⟩
      exact ⟨hyB, hyM, hsW (closedBall_subset_closedBall hρ hyB)⟩
  -- Step 5: unit density of ν (siblings unweighted_density_one and closed_to_open_ball_density)
  have hfinball : μHE[n] (M ∩ closedBall x (r / 2)) ≠ ∞ := by
    have h1 := hνle (closedBall x (r / 2)) measurableSet_closedBall
    have h2 := hμfin (closedBall x (r / 2)) (isCompact_closedBall x (r / 2))
    rw [hν, Measure.restrict_apply measurableSet_closedBall, hloc _ le_rfl] at h1
    exact ne_top_of_le_ne_top h2 h1
  have hTD := Submission.rsd_tendsto_closedBall_density_of_approxTangent P n M x Q (r / 2) hs
    hfinball hQ
  have hTD' : Tendsto (fun ρ : ℝ => ν (closedBall x ρ) /
      (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 1) := by
    refine hTD.congr' ?_
    have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ ∈ Ioo 0 (r / 2) := Ioo_mem_nhdsGT hs
    filter_upwards [hev] with ρ hρ
    rw [hν, Measure.restrict_apply measurableSet_closedBall, hloc ρ hρ.2.le]
  have hb := Submission.rsd_tendsto_ball_density_of_closedBall P n ν x 1 hTD'
  -- Step 6: splitting the ball along the level k = θ(x)
  set k : ℕ := R.mult x with hk
  have hxA : x ∉ A k := fun h => h.2 (by simp [hk])
  have he := hxUD k hxA
  set T : Set (Euclid P) := R.mult ⁻¹' {k} with hT
  have hTm : MeasurableSet T := R.measurable_mult (measurableSet_singleton k)
  have hset : ∀ ρ : ℝ, (ball x ρ ∩ M') \ T = (A k ∩ ball x ρ) ∩ M' := by
    intro ρ
    ext y
    simp only [hA, hT, mem_inter_iff, Set.mem_sdiff, mem_preimage, mem_compl_iff,
      mem_singleton_iff]
    tauto
  have hsplit : ∀ ρ : ℝ, μ (ball x ρ) =
      (k : ℝ≥0∞) * μHE[n] ((ball x ρ ∩ M') ∩ T) + μ (A k ∩ ball x ρ) := by
    intro ρ
    rw [hmeas _ measurableSet_ball, hmeas _ ((hAm k).inter measurableSet_ball),
      ← lintegral_inter_add_sdiff (B := T) _ _ hTm]
    congr 1
    · rw [setLIntegral_congr_fun ((measurableSet_ball.inter hM'm).inter hTm)
        (g := fun _ => (k : ℝ≥0∞)) (fun y hy => by
          have : R.mult y = k := hy.2
          simp [this])]
      simp
    · rw [hset ρ]
  have hνsplit : ∀ ρ : ℝ, ν (ball x ρ) =
      μHE[n] ((ball x ρ ∩ M') ∩ T) + ν (A k ∩ ball x ρ) := by
    intro ρ
    rw [hν, Measure.restrict_apply measurableSet_ball,
      Measure.restrict_apply ((hAm k).inter measurableSet_ball),
      ← measure_inter_add_sdiff (ball x ρ ∩ M') hTm, hset ρ]
  have hup : ∀ ρ : ℝ, μ (ball x ρ) ≤
      (k : ℝ≥0∞) * ν (ball x ρ) + μ (A k ∩ ball x ρ) := by
    intro ρ
    rw [hsplit ρ]
    have h1 : μHE[n] ((ball x ρ ∩ M') ∩ T) ≤ ν (ball x ρ) := by
      rw [hν, Measure.restrict_apply measurableSet_ball]
      exact measure_mono inter_subset_left
    exact add_le_add (mul_le_mul_right h1 _) le_rfl
  have hlow : ∀ ρ : ℝ, (k : ℝ≥0∞) * ν (ball x ρ) ≤
      μ (ball x ρ) + (k : ℝ≥0∞) * μ (A k ∩ ball x ρ) := by
    intro ρ
    rw [hνsplit ρ, mul_add, hsplit ρ, add_assoc]
    have h2 := hνle (A k ∩ ball x ρ) ((hAm k).inter measurableSet_ball)
    exact add_le_add le_rfl ((mul_le_mul_right h2 _).trans le_add_self)
  -- Step 7: the quantity in the statement is μ (ball x ρ)
  have htarget : ∀ ρ : ℝ, R.measure (ball x ρ ∩ W) = μ (ball x ρ) := by
    intro ρ
    rw [hμ, Measure.restrict_apply measurableSet_ball]
  simp_rw [htarget]
  -- Step 7: limits
  set c : ℝ → ℝ≥0∞ := fun ρ => unitBallVolume n * ENNReal.ofReal (ρ ^ n) with hc
  have hk_top : (k : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top k
  have hupper : Tendsto (fun ρ => (k : ℝ≥0∞) * (ν (ball x ρ) / c ρ) +
      μ (A k ∩ ball x ρ) / c ρ) (𝓝[>] 0) (𝓝 (k : ℝ≥0∞)) := by
    have := (ENNReal.Tendsto.const_mul hb (Or.inr hk_top)).add he
    simpa using this
  have hlower : Tendsto (fun ρ => (k : ℝ≥0∞) * (ν (ball x ρ) / c ρ) -
      (k : ℝ≥0∞) * (μ (A k ∩ ball x ρ) / c ρ)) (𝓝[>] 0) (𝓝 (k : ℝ≥0∞)) := by
    have h1 := ENNReal.Tendsto.const_mul hb (Or.inr hk_top)
    have h2 := ENNReal.Tendsto.const_mul he (Or.inr hk_top)
    have := ENNReal.Tendsto.sub h1 h2 (Or.inl (by simp))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hupper (fun ρ => ?_) (fun ρ => ?_)
  · simp only
    rw [tsub_le_iff_right, ← mul_div_assoc, ← mul_div_assoc, ← ENNReal.add_div]
    exact ENNReal.div_le_div_right (hlow ρ) _
  · simp only
    rw [← mul_div_assoc, ← ENNReal.add_div]
    exact ENNReal.div_le_div_right (hup ρ) _
```

## Key steps

1. μ := R.measure⌞W is finite on compact sets and μ(S) = ∫_{S∩M′} θ dHⁿ with M′ = M ∩ W; θ ≥ 1 on M gives ν := Hⁿ⌞M′ ≤ μ.
2. Level sets A_k = M′ ∩ θ⁻¹(ℕ ∖ {k}): sibling upper_density_zero with λ = μ gives μ(A_k ∩ B_ρ(x)) = o(ρⁿ) for Hⁿ-a.e. x ∉ A_k, for all k at once.
3. Field orients, local finiteness in a closed ball inside W, and the siblings unweighted_density_one and closed_to_open_ball_density give ν(B_ρ(x))/(ω_nρⁿ) → 1 at Hⁿ-a.e. x ∈ M′.
4. With k = θ(x) and T = θ⁻¹(k): μ(B) = k·Hⁿ(B ∩ M′ ∩ T) + μ(A_k ∩ B), whence μ(B) ≤ kν(B) + μ(A_k ∩ B) and kν(B) ≤ μ(B) + kμ(A_k ∩ B).
5. Divide by ω_nρⁿ and squeeze: R.measure(B_ρ(x) ∩ W)/(ω_nρⁿ) = μ(B_ρ(x))/(ω_nρⁿ) → k = θ(x).

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; git diff --quiet b4d606d 2d804b9 -- GMT/ lakefile.toml lake-manifest.json lean-toolchain (exit 0)`
- `sha256sum GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean <snapshot>/project/GMT/Ch07/Contract.lean <snapshot>/project/GMT/Ch07/Submission.lean`
- `rg -n 'structure IMRep|def IMRep.measure|def unitBallVolume|orients :' <snapshot>/project/GMT/Ch07/Contract.lean`
- `rg -n 'theorem exists_disjoint_subfamily_covering_enlargement|theorem hausdorffMeasure_le_liminf_tsum|exists_isClosed_sdiff_lt|of_pseudoMetrizableSpace_of_isFiniteMeasure|addHaarScalarFactor_volume_hausdorffMeasure_ne_zero|theorem lintegral_inter_add_sdiff|theorem measure_inter_add_sdiff|theorem setLIntegral_mono|protected theorem Tendsto.sub|protected theorem add_div|theorem div_le_div_right|theorem withDensity_apply|theorem ae_restrict_iff' <snapshot>/mathlib/Mathlib --glob '*.lean'`
- `rg -n 'euclideanHausdorffMeasure_def|notation.*μHE' <snapshot>/mathlib/Mathlib --glob '*.lean'`
- `rg -n -F 'dimred_tr_ida_' <snapshot>/project <snapshot>/mathlib --glob '*.lean' (exit 1, no match)`
- `python3 scans of dag.json: status, candidate_commit, updated_at and lean_statement of the selected node and of the owners of idtp_dema_upper_density_zero, rsd_tendsto_closedBall_density_of_approxTangent, rsd_tendsto_ball_density_of_closedBall and dimred_tr_ida_density_on_carrier; parents and depends_on users of the three reused nodes; accepted statements of the form x ∉ A → … (𝓝 0); cross-branch child edges`
- `cat isolated-comparator-result.json, lean-audit-v1.json, accepted-candidate.json and parent-child-handoff.json of the three reused nodes; comparison of their handoff natural proofs, statements and key steps with the children here`
- `git show {ee6fe01,dbef2c1,c3ca64f}:GMT/Ch07/Submission.lean; difflib extraction of the single block each adds to Contract.lean (/tmp/idae2/scripts/extract_blocks.py)`
- `cat cluster-state/logs/gmt-ch07/322e06219c1847d6b763362645586939.log (worker of issue #7930: attempt 1, name-check failure, attempt 2)`
- `gh api repos/humanfia/math-lean-flow/contents/_recursive_lean/{runtime,store,prompts,models,lean_contract,decomposition_scope}.py?ref=feature/humanize-api-update-claude; read _existing_lean_name_problem, _accepted_checkpoint, _decompose, _solve_children, Store.update/refresh/ensure, _install_parent_supplied_child_handoff, _dependency_problem, _reference_use_problem, validate_lean_statement`
- `python3 /tmp/idae2/scripts/make_lean.py; lake env lean /tmp/idae2/lean/Types3.lean; lake env lean /tmp/idae2/lean/CarrierOnly3.lean; lake env lean /tmp/idae2/lean/Full3.lean (each with #print axioms)`
- `python3 /tmp/idae2/scripts/graph_check.py dag.json decomposition.json (replica of the key/name patterns, _dependency_problem, _existing_lean_name_problem and node bounds)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-imrep-density-ae-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-imrep-density-ae-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-5625b30197/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-5625b30197/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-unweighted-density-one-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-unweighted-density-one-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-closed-to-open-b-2625a8c412/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-closed-to-open-b-2625a8c412/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/cluster-state/logs/gmt-ch07/322e06219c1847d6b763362645586939.log`
- `/tmp/idae2/lean/Types3.lean`
- `/tmp/idae2/lean/CarrierOnly3.lean`
- `/tmp/idae2/lean/Full3.lean`
- `/tmp/idae2/scripts/graph_check.py`

Pins match. The snapshot manifest records project b4d606d and mathlib 25730c7c, equal to the workspace HEAD and to .lake/packages/mathlib; simongmt is 2b36630 as pinned in lakefile.toml. The snapshot Contract.lean and Submission.lean and the workspace ones are byte-identical (sha256 e4148e7f…), and the proof base 2d804b9 changes nothing under GMT/.

Library facts the children use exist in the snapshot:
- Vitali.exists_disjoint_subfamily_covering_enlargement (Covering/Vitali.lean:59) and hausdorffMeasure_le_liminf_tsum (Measure/Hausdorff.lean:555).
- MeasurableSet.exists_isClosed_sdiff_lt (Measure/Regular.lean:1036) and the WeaklyRegular instance of_pseudoMetrizableSpace_of_isFiniteMeasure (Regular.lean:1072).
- euclideanHausdorffMeasure_def and addHaarScalarFactor_volume_hausdorffMeasure_ne_zero (Geometry/Euclidean/Volume/Measure.lean:74, 96).
- lintegral_inter_add_sdiff (Lebesgue/Basic.lean:637), measure_inter_add_sdiff (Measure/Basic.lean:83), setLIntegral_mono' (Lebesgue/Basic.lean:254), withDensity_apply (WithDensity.lean:44) and ae_restrict_iff' (Restrict.lean:629).
- ENNReal.Tendsto.sub (Topology/Instances/ENNReal/Lemmas.lean:309), ENNReal.add_div and ENNReal.div_le_div_right.
The contract defines IMRep with fields measurableSet_carrier, measurable_mult, mult_pos and orients, and defines IMRep.measure = (μHE[n]⌞carrier).withDensity mult and unitBallVolume n = volume(ball 0 1) (Contract.lean:61–143), as the children use them.

Reuse is valid. The three reused nodes are accepted, with candidate commits ee6fe01, dbef2c1 and c3ca64f, isolated comparators passed and comparator_passed audits. Their dag.json types equal the lean_statements here and the declarations in their candidates byte for byte. idtp_dema_upper_density_zero has been accepted since 12:53:48Z. Attempt 1 rejected it only because its worker had loaded the DAG before then, as the worker log and the runtime's in-memory name check show; the runtime's accepted-checkpoint condition now holds. dimred_tr_ida_density_on_carrier is unused in dag.json and in the snapshot.

Lean checks of this attempt all exit 0. The four child types elaborate, and the assembly proves the frozen selected type from them. The carrier proof compiles from its three siblings. Together with the three accepted proofs, all five declarations compile without sorry; #print axioms gives propext, Classical.choice and Quot.sound. The replica graph and name check passes against the live 2416-node DAG.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
