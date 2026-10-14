<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1 -->

## Theorem `Submission.dmcbr_ci_constant_cycle_planes`

Let P, d ∈ ℕ, n := d+1, ν a Borel measure on ℝ^P finite on compact sets, ζ₀ ∈ Λ_n(ℝ^P) with |ζ₀(β)| ≤ |β| for all n-covectors β and ζ₀(β₁) = 1 for some β₁ with |β₁| ≤ 1 (|·| = covectorEuclideanNorm), and c > 0. Assume: (1) ∫ζ₀(dφ(y))dν(y) = 0 for every test d-form φ on ℝ^P; (2) ν(B_R(0)) ≤ ω_nRⁿ for all R > 0 (ω_n = unitBallVolume n); (3) ν(B_r(0)) > 0 for all r > 0; (4) liminf_{r↓0}ν(B_r(y))/(ω_nrⁿ) ≥ c for ν-a.e. y. Then there are an orthonormal family v = (v_1, …, v_n) in ℝ^P, N ∈ ℕ, pairwise distinct w_1, …, w_N ∈ ℝ^P orthogonal to every v_j, and reals α_1, …, α_N ≥ c with Σ_iα_i ≤ 1, such that ζ₀(β) = β(v_1, …, v_n) for all β, some w_i = 0, and ν = Σ_iα_iHⁿ⌞{y : y − w_i ∈ span(v)} (Hⁿ = μHE[n]).

Node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5833

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1298, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1299, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5346, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3487, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6261, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6268, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6274, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6285, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6297, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6305, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6316, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6325

## Lean problem

Declaration: `Submission.dmcbr_ci_constant_cycle_planes`

```lean
∀ (P d : ℕ) (ν : Measure (Euclid P)) (ζ₀ : MultiVector P (d + 1)) (c : ℝ), 0 < c → (∀ K : Set (Euclid P), IsCompact K → ν K < ∞) → (∀ β : Covector (Euclid P) (d + 1), |ζ₀ β| ≤ covectorEuclideanNorm β) → (∃ β : Covector (Euclid P) (d + 1), covectorEuclideanNorm β ≤ 1 ∧ ζ₀ β = 1) → (∀ φ : TestFormOn (univ : Set (Euclid P)) d, ∫ y, ζ₀ (exteriorDerivative (φ : DifferentialForm (Euclid P) d) y) ∂ν = 0) → (∀ R : ℝ, 0 < R → ν (ball 0 R) ≤ unitBallVolume (d + 1) * ENNReal.ofReal (R ^ (d + 1))) → (∀ r : ℝ, 0 < r → 0 < ν (ball 0 r)) → (∀ᵐ y ∂ν, ENNReal.ofReal c ≤ liminf (fun r : ℝ => ν (ball y r) / (unitBallVolume (d + 1) * ENNReal.ofReal (r ^ (d + 1)))) (𝓝[>] 0)) → ∃ (v : Fin (d + 1) → Euclid P) (N : ℕ) (w : Fin N → Euclid P) (α : Fin N → ℝ), Orthonormal ℝ v ∧ (∀ β : Covector (Euclid P) (d + 1), ζ₀ β = β v) ∧ Injective w ∧ (∀ (i : Fin N) (j : Fin (d + 1)), inner ℝ (w i) (v j) = 0) ∧ (∀ i, c ≤ α i) ∧ ∑ i, α i ≤ 1 ∧ (∃ i, w i = 0) ∧ ν = ∑ i, ENNReal.ofReal (α i) • (μHE[(d + 1)]).restrict {y : Euclid P | y - w i ∈ Submodule.span ℝ (Set.range v)}
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

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, steps 6 (V9, invariance and simplicity) and 7 (V10, structure of ν); hypothesis (1) is ∂C = 0 for C(ω) = ∫ζ₀(ω)dν, (2)–(3) are step 5(α), (β), and (4) is the output of lower_density used in step 7. Fact (O) (orthogonal invariance of the coefficient norm; proved here because the accepted DAG lemmas regcomp_covector_sq_sum_orthonormalBasis / regcomp_covector_eval_orthonormal_le / regcomp_exists_covector_eval_orthonormal_eq_one are not prerequisites of this node). For an orthonormal basis f = (f_1, …, f_P) of ℝ^P and a k-covector α, Σ_{j : Fin k → Fin P} α(f_{j(1)}, …, f_{j(k)})² = k!·|α|²: the left side is the squared Hilbert–Schmidt norm of the multilinear map α and does not depend on the orthonormal basis (expand α(Of_{j(1)}, …) multilinearly and use Σ_l O_{la}O_{lb} = δ_{ab}); for the standard basis non-injective j contribute 0 and each increasing multi-index I contributes k! equal terms α(e_I)². Consequences: (O1) if v = (v_1, …, v_k) is orthonormal then |α(v)| ≤ |α| (extend v to an orthonormal basis; the k! permutations of (1, …, k) already contribute k!α(v)²); (O2) β_v(u) := det(⟨u_i, v_j⟩)_{i,j} is a k-covector (multilinear and alternating in u) with β_v(v) = 1 and |β_v| = 1 (in a basis extending v its only non-zero values are ±1 on the permutations of (1, …, k)); (O3) if p : ℝ^P → ℝ^k, p(x) = (⟨x, v_1⟩, …, ⟨x, v_k⟩) with v orthonormal, then the pulled-back covector p^#γ := γ∘(p × ⋯ × p) of an l-covector γ on ℝ^k has |p^#γ| = |γ| (in a basis f extending v, p(f_i) = e_i for i ≤ k and 0 otherwise). 
0. Notation. For w ∈ ℝ^P let w^♭ := ⟨w, ·⟩. For a d-covector α (a real number if d = 0) let w^♭∧α be the n-covector (u_1, …, u_n) ↦ Σ_j(−1)^{j−1}⟨w, u_j⟩α(u_1, …, û_j, …, u_n) (for d = 0: α⟨w, u_1⟩). w ↦ ζ₀(w^♭∧α) is linear; let v_α ∈ ℝ^P be its Riesz representative: ⟨v_α, w⟩ = ζ₀(w^♭∧α).
1. Directional identity. For φ ∈ C_c^∞(ℝ^P) and a fixed d-covector α, the test d-form φα : y ↦ φ(y)α has d(φα)(y) = (∇φ(y))^♭∧α (exteriorDerivative_apply: the alternating sum of the directional derivatives Dφ(y)[u_j]α(…û_j…)). By (1), 0 = ∫ζ₀((∇φ)^♭∧α)dν = ∫⟨v_α, ∇φ⟩dν = ∫Dφ(y)[v_α]dν(y).
2. Translation invariance. Fix α, v := v_α, φ ∈ C_c^∞ and F(s) := ∫φ(y + sv)dν(y). For s in a bounded interval the functions y ↦ φ(y + sv), y ↦ Dφ(y + sv)[v] are bounded and supported in a fixed compact set (of finite ν-measure), so F is differentiable with F'(s) = ∫Dφ(y + sv)[v]dν(y) = 0 by step 1 applied to φ(· + sv) ∈ C_c^∞. Hence ∫φ(y + sv)dν = ∫φ dν for all s and φ ∈ C_c^∞, hence for all φ ∈ C_c (uniform approximation by mollification with supports in a fixed compact set). The translate of ν by sv and ν are locally finite, hence regular, Borel measures on ℝ^P with the same integrals of all of C_c, so they are equal (Mathlib Measure.ext_of_integral_eq_on_compactlySupported). Composing translations, ν is invariant under translation by every vector of V₀ := span{v_α : α a d-covector}.
3. Only coordinates inside V₀ matter. Let r := dim V₀ and choose an orthonormal basis e'_1, …, e'_P of ℝ^P with V₀ = span(e'_1, …, e'_r). Every n-covector expands as β = Σ_Iβ(e'_I)e'^I over increasing multi-indices I, with e'^I := e'^{i_1♭}∧⋯∧e'^{i_n♭} the dual basis. If I contains some i > r then e'^I = ±e'^{i♭}∧e'^{I∖i} and ζ₀(e'^I) = ±⟨v_{e'^{I∖i}}, e'_i⟩ = 0, because v_{e'^{I∖i}} ∈ V₀ ⊥ e'_i. So ζ₀(β) = Σ_{I⊆{1..r}}β(e'_I)ζ₀(e'^I) for all β. As ζ₀(β₁) = 1 ≠ 0, some increasing I ⊆ {1, …, r} with n elements exists: r ≥ n.
4. Growth forces r ≤ n. By (3) m₀ := ν(B_1(0)) > 0, and by step 2, ν(B_1(u)) = m₀ for every u ∈ V₀. For R ≥ 4 consider u = 2Σ_{j≤r}k_je'_j with k ∈ ℤ^r, |k_j| ≤ R/(4√r): these points are at mutual distance ≥ 2 and |u| ≤ R/2, so the balls B_1(u) are pairwise disjoint and contained in B_R(0); there are at least c_rR^r of them for some c_r > 0. Hence c_rm₀R^r ≤ ν(B_R(0)) ≤ ω_nRⁿ (by (2)) for all large R, which forces r ≤ n. So r = n, V₀ = span(e'_1, …, e'_n) and, by step 3, ζ₀(β) = s·β(e'_1, …, e'_n) with s := ζ₀(e'^{(1,…,n)}).
5. Normalisation. For the orthonormal v := (e'_1, …, e'_n), (O1) gives |β(v)| ≤ |β| for all β and (O2) gives β₂ := β_v with |β₂| = 1, β₂(v) = 1. Thus |s| = |ζ₀(β₂)| ≤ 1 and 1 = ζ₀(β₁) = sβ₁(v) ≤ |s||β₁| ≤ |s|, so |s| = 1. If s = −1 replace e'_1 by −e'_1 (still orthonormal, same span; β(v) changes sign). Hence ζ₀(β) = β(v_1, …, v_n) for all β, with v orthonormal and span(v) = V₀.
6. Product structure. Write ℝ^P = V₀ ⊕ V₀^⊥ (orthogonal projections p, q). For a bounded Borel B ⊆ V₀^⊥, A ↦ ν(A + B) (A ⊆ V₀ Borel; A + B is Borel, the image of A × B under the linear isomorphism V₀ × V₀^⊥ → ℝ^P, and (A₁ + B) ∩ (A₂ + B) = (A₁ ∩ A₂) + B) is a translation-invariant Borel measure on V₀ (step 2), finite on compact sets. V₀ is isometric to ℝⁿ with Hⁿ⌞V₀ corresponding to Lebesgue measure (Mathlib Isometry.map_euclideanHausdorffMeasure, EuclideanSpace.euclideanHausdorffMeasure_eq_volume), so by uniqueness of Haar measure (Mathlib Measure.isAddLeftInvariant_eq_smul) ν(A + B) = σ(B)Hⁿ(A) with σ(B) := ν((V₀ ∩ B_1(0)) + B)/ω_n. Defining σ(B) by this formula for all Borel B ⊆ V₀^⊥ gives a Borel measure on V₀^⊥, finite on bounded sets, with ν(A + B) = Hⁿ(A)σ(B) for all Borel A ⊆ V₀, B ⊆ V₀^⊥ (bounded B first, then countable additivity). The sets A + B form a π-system generating the Borel sets of ℝ^P on which ν and the measure (Hⁿ⌞V₀) ⊗ σ (transported to ℝ^P) agree, both finite on the sets (V₀ ∩ B_j(0)) + (V₀^⊥ ∩ B_j(0)) covering ℝ^P; hence ν = (Hⁿ⌞V₀) ⊗ σ (Mathlib Measure.ext_of_generateFrom_of_iUnion).
7. σ is purely atomic with atoms ≥ c. For y = u + w (u ∈ V₀, w ∈ V₀^⊥), B_r(y) ⊆ (V₀ ∩ B_r(u)) + (V₀^⊥ ∩ B_r(w)), so ν(B_r(y)) ≤ Hⁿ(V₀ ∩ B_r(u))σ(B_r(w)) = ω_nrⁿσ(B_r(w)). By (4), for ν-a.e. y: c ≤ liminf_{r↓0}ν(B_r(y))/(ω_nrⁿ) ≤ liminf_{r↓0}σ(B_r(w)) = σ({w}) (continuity from above, σ(B_1(w)) < ∞). The set Z := {w ∈ V₀^⊥ : σ({w}) ≥ c} is locally finite (a bounded B contains at most σ(B)/c of its points), hence closed and countable, and G := V₀^⊥∖Z is Borel. V₀ + G is ν-null by the preceding sentence, so ω_nσ(G) = ν((V₀ ∩ B_1(0)) + G) = 0. Hence σ = Σ_{w∈Z}σ({w})δ_w.
8. Finitely many planes with Σα_i ≤ 1. Enumerate Z = {w_i} and put α_i := σ({w_i}) ≥ c; then ν = Σ_iα_iHⁿ⌞(V₀ + w_i) (step 6). For R > 0, since w_i ⊥ V₀, (V₀ + w_i) ∩ B_R(0) is an n-ball of radius (R² − |w_i|²)_+^{1/2} in the plane V₀ + w_i, so ν(B_R(0)) = Σ_iα_iω_n(R² − |w_i|²)_+^{n/2}. By (2), for every finite subfamily F, Σ_{i∈F}α_i(1 − |w_i|²/R²)_+^{n/2} ≤ 1; letting R → ∞ gives Σ_{i∈F}α_i ≤ 1. As α_i ≥ c > 0, Z is finite, N := #Z ≤ 1/c, and Σ_{i≤N}α_i ≤ 1. The w_i are pairwise distinct and lie in V₀^⊥, i.e. ⟨w_i, v_j⟩ = 0.
9. Some w_i = 0. spt ν = ⋃_i(V₀ + w_i) (a finite union of planes, each the support of Hⁿ⌞(V₀ + w_i)). By (3), 0 ∈ spt ν, so 0 ∈ V₀ + w_i for some i, i.e. w_i ∈ V₀ ∩ V₀^⊥ = {0}.
10. In the required form: V₀ + w_i = {y : y − w_i ∈ span(v)}, ν = Σ_{i : Fin N}ofReal(α_i)·Hⁿ⌞{y : y − w_i ∈ span(v)}, with α_i ≥ c, Σα_i ≤ 1 and ζ₀(β) = β(v). ∎

## Key steps

1. (1) applied to φα gives ∫Dφ·v_α dν = 0, so ν is invariant under translations by V₀ := span{v_α}.
2. ζ₀ only sees coordinates in V₀ (so dim V₀ ≥ n), and the growth bound (2) forces dim V₀ ≤ n; normalise to ζ₀(β) = β(v) using Fact (O).
3. Haar uniqueness on V₀ gives ν = Hⁿ⌞V₀ ⊗ σ; the lower density (4) makes σ a sum of atoms of mass ≥ c.
4. Growth (2) gives Σα_i ≤ 1, hence finitely many planes; (3) puts 0 on one of them.

## Reference use

### local-project

Queries:
- `cat RUN/local-references/123e8435b4a2469b/manifest.json -> mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d; git rev-parse HEAD (workspace b4d606db1, .lake/packages/simongmt 2b366308, .lake/packages/mathlib 25730c7c); cmp SNAPSHOT/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean -> identical`
- `python3 scans of RUN/dag.json (1611 nodes): selected node and its five sibling dependencies; byte comparison of the selected frozen type and of restrict_unique/convergence_tools/slice_limit/lower_density/rectifiable (and all other closure_and_boundary_rectifiability siblings) with root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.* -> all identical; statuses of the 12 children of ...cycle_im-a1 in that branch (const_mass-a1 accepted, candidate bc226ec6ff9a09922237c3ab524c8613d1bdec79; the other 11 unaccepted); lean_name lookup of the 12 proposed names -> only cbr_ci_const_vector_massOn exists, with identical frozen type; no dmcbr_ci* name in the DAG`
- `read RUN/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-33509b6e86/decomposition-v1.json and decomposition-audit-v1.json (acceptable=true, all 12 natural_proof_acceptable=true) and diff of its parent-supplied-natural-proof.md against this node's (same steps 1-11)`
- `git show 50d4743caa68 (speculative assembly of cbr_cycle_isIntegerMultiplicity) and git show 9e7eb961 / 89c100ef / 07f3403b / d2bd669b / 200b612d | grep Submission.* (child drafts reference exactly their declared sibling dependencies)`
- `grep -n '_existing_lean_name_problem|_accepted_checkpoint|existing_by_name|_install_parent_supplied_child_handoff' /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (accepted cross-branch declarations with identical type are reused by name; unaccepted ones are reserved)`
- `rg -c dmcbr_ci SNAPSHOT/project (no match, exit 1); rg -l dmcbr_ci .lake/packages/simongmt GMT (no match, exit 1)`
- `rg -l -F over SNAPSHOT/mathlib/Mathlib for every library name cited in the child proofs: Besicovitch.tendsto_filterAt, Besicovitch.vitaliFamily, ENNReal.liminf_const_mul_of_ne_top, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Isometry.euclideanHausdorffMeasure_image, Isometry.map_euclideanHausdorffMeasure, IsometryEquiv.measurePreserving_euclideanHausdorffMeasure, LipschitzWith.hausdorffMeasure_image_le, Measure.addHaar_closedBall, Measure.addHaar_image_linearMap, Measure.euclideanHausdorffMeasure_smul₀, MeasureTheory.euclideanHausdorffMeasure_homothety_image, Measure.ext_of_generateFrom_of_iUnion, Measure.ext_of_generate_finite, Measure.ext_of_integral_eq_on_compactlySupported, Measure.hausdorffMeasure_apply, Measure.hausdorffMeasure_le_liminf_tsum, Measure.haveLebesgueDecomposition_add, isAddLeftInvariant_eq_smul (to_additive of isMulLeftInvariant_eq_smul), Measure.le_hausdorffMeasure, Measure.le_iff', Measure.rnDeriv_lt_top, Measure.singularPart_eq_zero_of_ac, OrthonormalBasis.volume_parallelepiped, PiLp.volume_preserving_ofLp, volume_preserving_piFinSuccAbove, Real.smoothTransition, Set.exists_isOpen_lt_of_lt, Vitali.exists_disjoint_subfamily_covering_enlargement(_closedBall), VitaliFamily.ae_tendsto_average_norm_sub, VitaliFamily.ae_tendsto_lintegral_enorm_sub_div, ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite, aemeasurable_of_tendsto_metrizable_ae', exists_contDiff_tsupport_subset, finrank_span_eq_card, integral_map_equiv, setIntegral_map_equiv, integral_smul_measure, integral_withDensity_eq_integral_toReal_smul, tendsto_of_subseq_tendsto, measure_toMeasurable_inter_of_sFinite, isAddHaarMeasure_hausdorffMeasure, euclideanHausdorffMeasure_zero -> all found; rg mul_sSup -> no ENNReal.mul_sSup (only ENat/Ordinal/Quantale versions), ENNReal.mul_iSup at Mathlib/Basic/ENNReal/Inv.lean:815 and sSup_image at Mathlib/Order/CompleteLattice/Basic.lean:571`
- `sed -n 1,80p SNAPSHOT/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (μHE[d] := addHaarScalarFactor volume μH[d] • μH[d]) and sed -n 915,925p Mathlib/MeasureTheory/Measure/Haar/Unique.lean (μ' = haarScalarFactor μ' μ • μ)`
- `rg -n over .lake/packages/simongmt/Poincare/SimonGMT: CountablyRectifiable.mono (Chapter03/Rectifiable.lean:55), HasApproximateTangentSpaceAt.unique (:232), blowUpMap / HasApproximateTangentSpaceAt definitions (:96, :102), GeometricCurrentOn.ext (Chapter06/Currents.lean:305), GeometricCurrentOn.boundary_apply (:333), exteriorDerivative_apply (Chapter06/Forms.lean:119), GeometricCurrentOn.affinePushforward / boundary_affinePushforward (Chapter06/AffineCurrentPushforward.lean:172, :188), covectorEuclideanNorm / massOn (Chapter06/Mass.lean:30, :68)`
- `lake env lean /tmp/dmcbr_ci/lean/Types.lean (the 12 child types as Submission.* theorems after import GMT.Ch07.Submission with the contract namespace/opens: sorry warnings only)`
- `lake env lean /tmp/dmcbr_ci/lean/Assembly.lean (exact frozen parent type from the 12 child types and the 5 frozen sibling types as hypotheses, no sorry; #print axioms: propext, Classical.choice, Quot.sound)`
- `python3 -I: _recursive_lean.lean_contract.validate_lean_statement on all 12 child types -> valid and unchanged`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-22612ab17a/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-22612ab17a/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-33509b6e86/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-33509b6e86/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-33509b6e86/parent-supplied-natural-proof.md`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/models.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/Unique.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/CompleteLattice/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/CompleteLattice.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/tmp/dmcbr_ci/lean/Types.lean`
- `/tmp/dmcbr_ci/lean/Assembly.lean`

The snapshot is compatible: pins match, and the snapshot contract is byte-identical to Submission.lean. Neither the snapshot nor SimonGMT contains a dmcbr_ci declaration. The selected node, its five sibling dependencies and its supplied proof coincide with the other branch's cbr_cycle_isIntegerMultiplicity, whose audited 12-child split is mirrored with identical types. cbr_ci_const_vector_massOn is accepted with an identical frozen type and is reused; the 11 other children get fresh, unused dmcbr_ci_ names. Every library result cited by the child proofs exists at the pinned revisions; ENNReal.mul_sSup does not, so ENNReal.mul_iSup with sSup_image is cited instead. All 12 child types elaborate, and the sorry-free conditional assembly proves the exact parent type using only propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
