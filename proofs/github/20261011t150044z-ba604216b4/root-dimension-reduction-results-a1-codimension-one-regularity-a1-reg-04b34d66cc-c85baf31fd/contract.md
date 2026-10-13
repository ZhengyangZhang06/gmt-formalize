<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.rectifiable_criterion-a1.uniform_compact-a1 -->

## Theorem `Submission.codim1_rdo_dg_rc_uniform_compact`

Let m ∈ ℕ, E := ℝ^{m+1}, μ a finite Borel measure on E, ν : E → E Borel, ε > 0 real and η ∈ (0, ∞]. Put ω_m := unitBallVolume m and C(x) := {z ∈ E : ¼|z − x| ≤ |⟨z − x, ν(x)⟩|}. Assume that for μ-a.e. y ∈ E, as r ↓ 0, μ(B̄_r(y))/(ω_m r^m) → 1 and μ(C(y) ∩ B̄_r(y))/r^m → 0 in [0, ∞]. Then there are a compact K ⊆ E and δ > 0 with μ(E \ K) ≤ η such that for every x ∈ K and every ρ ∈ (0, δ): (1 − ε)⁺ ω_m ρ^m ≤ μ(B̄_ρ(x)) and μ(C(x) ∩ B̄_ρ(x)) ≤ ε ω_m ρ^m (in [0, ∞], with (1 − ε)⁺ := max(1 − ε, 0), i.e. ENNReal.ofReal (1 − ε)).

Node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.rectifiable_criterion-a1.uniform_compact-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5227

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5527

Decomposition children: None

## Lean problem

Declaration: `Submission.codim1_rdo_dg_rc_uniform_compact`

```lean
∀ (m : ℕ) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (ε : ℝ) (η : ℝ≥0∞), IsFiniteMeasure μ → Measurable ν → 0 < ε → 0 < η → (∀ᵐ y ∂μ, Tendsto (fun r : ℝ => μ (closedBall y r) / (unitBallVolume m * ENNReal.ofReal (r ^ m))) (𝓝[>] 0) (𝓝 1) ∧ Tendsto (fun r : ℝ => μ ({z | (1 / 4 : ℝ) * ‖z - y‖ ≤ |inner ℝ (z - y) (ν y)|} ∩ closedBall y r) / ENNReal.ofReal (r ^ m)) (𝓝[>] 0) (𝓝 0)) → ∃ K : Set (Euclid (m + 1)), ∃ δ : ℝ, IsCompact K ∧ 0 < δ ∧ μ Kᶜ ≤ η ∧ (∀ x ∈ K, ∀ ρ : ℝ, 0 < ρ → ρ < δ → ENNReal.ofReal (1 - ε) * unitBallVolume m * ENNReal.ofReal (ρ ^ m) ≤ μ (closedBall x ρ)) ∧ (∀ x ∈ K, ∀ ρ : ℝ, 0 < ρ → ρ < δ → μ ({z | (1 / 4 : ℝ) * ‖z - x‖ ≤ |inner ℝ (z - x) (ν x)|} ∩ closedBall x ρ) ≤ ENNReal.ofReal ε * unitBallVolume m * ENNReal.ofReal (ρ ^ m))
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

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.rectifiable_criterion-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.rectifiable_criterion-a1.uniform_compact-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent proof, step 2 (Uniformization), which replaces the printed (4), (7)–(9) of Simon Ch. 3, proof of 1.6 “⇐” (chapter-03.txt lines 162–213, where 1.15 of Ch. 1 and Egoroff's theorem are applied to the functions f_k, q_k). As in the parent, Egoroff's theorem is replaced by explicit Borel sets G_k defined with rational radii, continuity from above of the finite measure, and inner regularity. The parent's threshold ¼λ(U) is the general η/2 here (the parent's application uses η = ½μ(U)). Dependency: ball_cone_measurable. Departure (simplification only): in the parent's 2(b) the cone bound is transferred from rational to real radii by continuity from above; monotonicity in the radius suffices and is used below.

0. Preliminaries. ω_m is the Lebesgue measure of the unit ball of ℝ^m, a nonempty bounded open set, so 0 < ω_m < ∞. For ρ ∈ ℝ put c_ℓ(ρ) := (1 − ε)⁺ ω_m (ρ^m)⁺ and c_u(ρ) := ε ω_m (ρ^m)⁺ in [0, ∞), where (ρ^m)⁺ = ENNReal.ofReal(ρ^m). The constants (1 − ε)⁺ ω_m and ε ω_m are finite, so c_ℓ and c_u are continuous on ℝ, and they are nondecreasing on [0, ∞).

1. Good sets. For k ∈ ℕ let δ_k := 1/(k + 1), and let G_k be the set of x ∈ E such that for every rational q with 0 < q < δ_k: c_ℓ(q) ≤ μ(B̄_q(x)) and μ(C(x) ∩ B̄_q(x)) ≤ c_u(q).

2. Measurability. For a fixed rational q the functions x ↦ μ(B̄_q(x)) and x ↦ μ(C(x) ∩ B̄_q(x)) are Borel (ball_cone_measurable with α = ¼; a finite measure is s-finite), so {x : c_ℓ(q) ≤ μ(B̄_q(x))} and {x : μ(C(x) ∩ B̄_q(x)) ≤ c_u(q)} are Borel. If 0 < q < δ_k fails, the condition for q holds for every x. Hence G_k, an intersection over the countably many rationals q, is Borel.

3. Monotonicity. Let k ≤ k′ and x ∈ G_k. Every rational q with 0 < q < δ_{k′} also satisfies q < δ_k, because δ_{k′} ≤ δ_k; so both bounds hold at x for q, and x ∈ G_{k′}. Thus G_k ⊆ G_{k′}.

4. Almost every point is good. Let y be a point at which both limits of the hypothesis hold (μ-a.e. y). Since ε > 0 we have (1 − ε)⁺ < 1 and 0 < ε⁺ ω_m. By the two limits there is r₁ > 0 such that for all r ∈ (0, r₁): μ(B̄_r(y))/(ω_m (r^m)⁺) > (1 − ε)⁺ and μ(C(y) ∩ B̄_r(y))/(r^m)⁺ < ε ω_m. For r ∈ (0, r₁) the denominators ω_m (r^m)⁺ and (r^m)⁺ lie in (0, ∞), so multiplying out gives c_ℓ(r) ≤ μ(B̄_r(y)) and μ(C(y) ∩ B̄_r(y)) ≤ c_u(r). Choose k with δ_k < r₁; then y ∈ G_k. Consequently μ(E \ ⋃_k G_k) = 0.

5. Choice of k. The Borel sets E \ G_k decrease in k (step 3), their intersection E \ ⋃_k G_k is μ-null (step 4), and μ is finite; by continuity from above, μ(E \ G_k) → 0. Since η/2 > 0, fix k with μ(E \ G_k) < η/2.

6. Inner regularity. A finite Borel measure on the Euclidean space E is inner regular with respect to compact sets on Borel sets of finite measure (Mathlib `MeasurableSet.exists_isCompact_sdiff_lt`; the instance `InnerRegularCompactLTTop` is automatic on E). So there is a compact K ⊆ G_k with μ(G_k \ K) < η/2. Since E \ K ⊆ (E \ G_k) ∪ (G_k \ K), μ(E \ K) ≤ η/2 + η/2 = η.

7. Uniform bounds for real radii. Put δ := δ_k > 0 and let x ∈ K ⊆ G_k and 0 < ρ < δ.
(a) Lower bound. For every real s ∈ (0, ρ) choose a rational q with s < q < ρ. Then 0 < q < δ_k, so x ∈ G_k gives c_ℓ(q) ≤ μ(B̄_q(x)); by monotonicity of c_ℓ and of μ, c_ℓ(s) ≤ c_ℓ(q) ≤ μ(B̄_q(x)) ≤ μ(B̄_ρ(x)). Letting s ↑ ρ and using continuity of c_ℓ at ρ gives c_ℓ(ρ) ≤ μ(B̄_ρ(x)).
(b) Cone bound. For every real s ∈ (ρ, δ) choose a rational q with ρ < q < s. Then 0 < q < δ_k, so μ(C(x) ∩ B̄_ρ(x)) ≤ μ(C(x) ∩ B̄_q(x)) ≤ c_u(q) ≤ c_u(s). Letting s ↓ ρ and using continuity of c_u at ρ gives μ(C(x) ∩ B̄_ρ(x)) ≤ c_u(ρ).
Since c_ℓ(ρ) = (1 − ε)⁺ ω_m ρ^m and c_u(ρ) = ε ω_m ρ^m for ρ > 0, K and δ have all the required properties. ∎

Lean note (non-normative aid). The following tactic proof of `Submission.codim1_rdo_dg_rc_uniform_compact` (the frozen type above, followed by `:= by`) compiles against the frozen contract: `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's `open`s, Lean v4.35.0-rc3, Mathlib 25730c7c; `#print axioms` gives only propext, Classical.choice, Quot.sound. Sibling lemmas used: `Submission.codim1_rdo_dg_rc_ball_cone_measurable`.
```lean
  intro m μ ν ε η hfin hν hε hη hae
  have hω0 : unitBallVolume m ≠ 0 := by
    unfold unitBallVolume; exact (measure_ball_pos _ _ one_pos).ne'
  have hωtop : unitBallVolume m ≠ ∞ := by
    unfold unitBallVolume; exact measure_ball_lt_top.ne
  have hball : ∀ q : ℝ, Measurable (fun x : Euclid (m + 1) => μ (closedBall x q)) :=
    fun q => (Submission.codim1_rdo_dg_rc_ball_cone_measurable m μ ν (1 / 4) q inferInstance hν).1
  have hcone : ∀ q : ℝ, Measurable (fun x : Euclid (m + 1) =>
      μ ({z | (1 / 4 : ℝ) * ‖z - x‖ ≤ |inner ℝ (z - x) (ν x)|} ∩ closedBall x q)) :=
    fun q => (Submission.codim1_rdo_dg_rc_ball_cone_measurable m μ ν (1 / 4) q inferInstance hν).2
  -- monotonicity and continuity of `ρ ↦ c * ofReal (ρ ^ m)`
  have hmono : ∀ (c : ℝ≥0∞) (s t : ℝ), 0 ≤ s → s ≤ t →
      c * ENNReal.ofReal (s ^ m) ≤ c * ENNReal.ofReal (t ^ m) := by
    intro c s t hs hst
    exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hs hst m)) c
  have hcont : ∀ c : ℝ≥0∞, c ≠ ∞ → Continuous (fun s : ℝ => c * ENNReal.ofReal (s ^ m)) :=
    fun c hc => (ENNReal.continuous_const_mul hc).comp
      (ENNReal.continuous_ofReal.comp (continuous_pow m))
  -- the abstract statement
  have main : ∀ (C : Euclid (m + 1) → Set (Euclid (m + 1))) (A B : ℝ≥0∞), A ≠ ∞ → B ≠ ∞ →
      (∀ q : ℝ, Measurable (fun x => μ (C x ∩ closedBall x q))) →
      (∀ᵐ y ∂μ, ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ r : ℝ, 0 < r → r < r₁ →
        A * ENNReal.ofReal (r ^ m) ≤ μ (closedBall y r) ∧
          μ (C y ∩ closedBall y r) ≤ B * ENNReal.ofReal (r ^ m)) →
      ∃ K : Set (Euclid (m + 1)), ∃ δ : ℝ, IsCompact K ∧ 0 < δ ∧ μ Kᶜ ≤ η ∧
        (∀ x ∈ K, ∀ ρ : ℝ, 0 < ρ → ρ < δ → A * ENNReal.ofReal (ρ ^ m) ≤ μ (closedBall x ρ)) ∧
        (∀ x ∈ K, ∀ ρ : ℝ, 0 < ρ → ρ < δ →
          μ (C x ∩ closedBall x ρ) ≤ B * ENNReal.ofReal (ρ ^ m)) := by
    intro C A B hA hB hCmeas hgood
    let G : ℕ → Set (Euclid (m + 1)) := fun k => {x | ∀ q : ℚ, 0 < (q : ℝ) →
      (q : ℝ) < 1 / ((k : ℝ) + 1) →
      A * ENNReal.ofReal ((q : ℝ) ^ m) ≤ μ (closedBall x q) ∧
        μ (C x ∩ closedBall x q) ≤ B * ENNReal.ofReal ((q : ℝ) ^ m)}
    have hGmeas : ∀ k, MeasurableSet (G k) := by
      intro k
      refine Measurable.setOf (Measurable.forall fun q => ?_)
      refine Measurable.imp measurable_const (Measurable.imp measurable_const
        (Measurable.and ?_ ?_))
      · exact measurableSet_setOfPred.1 (measurableSet_le measurable_const (hball q))
      · exact measurableSet_setOfPred.1 (measurableSet_le (hCmeas q) measurable_const)
    have hGmono : Monotone G := by
      intro k l hkl x hx q hq0 hql
      refine hx q hq0 (lt_of_lt_of_le hql ?_)
      have hkl' : (k : ℝ) ≤ l := Nat.cast_le.mpr hkl
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have hGae : ∀ᵐ x ∂μ, x ∈ ⋃ k, G k := by
      filter_upwards [hgood] with y hy
      obtain ⟨r₁, hr₁, hy⟩ := hy
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hr₁
      exact mem_iUnion.mpr ⟨k, fun q hq0 hqk => hy q hq0 (hqk.trans hk)⟩
    have hnull : μ (⋂ k, (G k)ᶜ) = 0 := by
      rw [← compl_iUnion]
      exact mem_ae_iff.mp hGae
    have htend : Tendsto (fun k => μ (G k)ᶜ) atTop (𝓝 0) := by
      have := tendsto_measure_iInter_atTop (μ := μ) (s := fun k => (G k)ᶜ)
        (fun k => (hGmeas k).compl.nullMeasurableSet)
        (fun k l hkl => compl_subset_compl.mpr (hGmono hkl)) ⟨0, measure_ne_top μ _⟩
      rw [hnull] at this
      exact this
    have hη2 : 0 < η / 2 := ENNReal.half_pos hη.ne'
    obtain ⟨k, hk⟩ := (htend.eventually_lt_const hη2).exists
    obtain ⟨K, hKG, hKc, hKμ⟩ :=
      (hGmeas k).exists_isCompact_sdiff_lt (measure_ne_top μ _) hη2.ne'
    refine ⟨K, 1 / ((k : ℝ) + 1), hKc, by positivity, ?_, ?_, ?_⟩
    · calc μ Kᶜ ≤ μ ((G k)ᶜ ∪ (G k \ K)) := by
            apply measure_mono
            intro x hx
            by_cases h : x ∈ G k
            · exact Or.inr ⟨h, hx⟩
            · exact Or.inl h
        _ ≤ μ (G k)ᶜ + μ (G k \ K) := measure_union_le _ _
        _ ≤ η / 2 + η / 2 := add_le_add hk.le hKμ.le
        _ = η := ENNReal.add_halves η
    · intro x hxK ρ hρ hρδ
      have hxG := hKG hxK
      have key : ∀ s ∈ Ioo 0 ρ, A * ENNReal.ofReal (s ^ m) ≤ μ (closedBall x ρ) := by
        intro s hs
        obtain ⟨q, hsq, hqρ⟩ := exists_rat_btwn hs.2
        have hq0 : 0 < (q : ℝ) := hs.1.trans hsq
        calc A * ENNReal.ofReal (s ^ m) ≤ A * ENNReal.ofReal ((q : ℝ) ^ m) :=
              hmono A s q hs.1.le hsq.le
          _ ≤ μ (closedBall x q) := (hxG q hq0 (hqρ.trans hρδ)).1
          _ ≤ μ (closedBall x ρ) := measure_mono (closedBall_subset_closedBall hqρ.le)
      exact le_of_tendsto (((hcont A hA).tendsto ρ).mono_left nhdsWithin_le_nhds)
        (eventually_of_mem (Ioo_mem_nhdsLT hρ) key)
    · intro x hxK ρ hρ hρδ
      have hxG := hKG hxK
      have key : ∀ s ∈ Ioo ρ (1 / ((k : ℝ) + 1)),
          μ (C x ∩ closedBall x ρ) ≤ B * ENNReal.ofReal (s ^ m) := by
        intro s hs
        obtain ⟨q, hρq, hqs⟩ := exists_rat_btwn hs.1
        have hq0 : 0 < (q : ℝ) := hρ.trans hρq
        calc μ (C x ∩ closedBall x ρ) ≤ μ (C x ∩ closedBall x q) :=
              measure_mono (inter_subset_inter_right _ (closedBall_subset_closedBall hρq.le))
          _ ≤ B * ENNReal.ofReal ((q : ℝ) ^ m) := (hxG q hq0 (hqs.trans hs.2)).2
          _ ≤ B * ENNReal.ofReal (s ^ m) := hmono B q s hq0.le hqs.le
      exact ge_of_tendsto (((hcont B hB).tendsto ρ).mono_left nhdsWithin_le_nhds)
        (eventually_of_mem (Ioo_mem_nhdsGT hρδ) key)
  -- apply `main`
  have hA1 : ENNReal.ofReal (1 - ε) < 1 := ENNReal.ofReal_lt_one.mpr (by linarith)
  have hB0 : 0 < ENNReal.ofReal ε * unitBallVolume m :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hε).ne' hω0
  refine main (fun x => {z | (1 / 4 : ℝ) * ‖z - x‖ ≤ |inner ℝ (z - x) (ν x)|})
    (ENNReal.ofReal (1 - ε) * unitBallVolume m) (ENNReal.ofReal ε * unitBallVolume m)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hωtop)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hωtop) hcone ?_
  filter_upwards [hae] with y hy
  obtain ⟨h1, h2⟩ := hy
  have e1 := h1.eventually_const_lt hA1
  have e2 := h2.eventually_lt_const hB0
  obtain ⟨r₁, hr₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (e1.and e2)
  refine ⟨r₁, hr₁, fun r hr0 hr1 => ?_⟩
  obtain ⟨hlow, hup⟩ := hsub ⟨hr0, hr1⟩
  have hpow0 : ENNReal.ofReal (r ^ m) ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hr0 m)).ne'
  have hpowtop : ENNReal.ofReal (r ^ m) ≠ ∞ := ENNReal.ofReal_ne_top
  constructor
  · have := (ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero hω0 hpow0))
      (Or.inl (ENNReal.mul_ne_top hωtop hpowtop))).mp hlow.le
    rw [mul_assoc]
    exact this
  · exact (ENNReal.div_le_iff hpow0 hpowtop).mp hup.le
```

## Key steps

1. Borel sets G_k (bounds at rational radii q < 1/(k+1)) increase in k; measurability comes from ball_cone_measurable.
2. Where both limits hold the bounds hold for all small radii, so μ-a.e. point lies in some G_k.
3. μ is finite, so μ(E \ G_k) → 0: pick k with μ(E \ G_k) < η/2, then compact K ⊆ G_k with μ(G_k \ K) < η/2.
4. Rational radii upgrade to every ρ ∈ (0, 1/(k+1)) by monotonicity in the radius and continuity of ρ ↦ c ω_m ρ^m.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; sha256sum <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `python3 scans of dag.json: selected node (depth 5, no children), sibling flat_tangent_density frozen type, collision check of the 7 codim1_rdo_dg_rc_* names, statements mentioning CountablyRectifiable or 16 ^ (cbrr_*, dpf*, codim1_rdo_*)`
- `rg -n 'theorem measurable_measure_prodMk_left|theorem LipschitzOnWith.extend_real|isClosed_range|finite_cover_balls|exists_isCompact_diff_lt|orthogonal_span_singleton|fromOrthogonalSpanSingleton|isOpen_biUnion_countable|isOpen_iUnion_countable|tendsto_measure_iUnion_atTop|Measurable.inner|instance.*InnerRegularCompactLTTop' <snapshot>/mathlib/Mathlib`
- `grep -n '^theorem|^def' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `sed -n 100,280p book/chapter-03.txt (printed proof of Simon Ch. 3, 1.6 ⇐)`
- `lake env lean -DautoImplicit=false /tmp/rc-split-check/Names.lean and Names2.lean (#check of the lemmas above inside the import closure of GMT.Ch07.Submission)`
- `lake env lean -DautoImplicit=false /tmp/rc-split-check/Types.lean, Assembly.lean, Full.lean and /tmp/rc-final/Verify.lean (7 child types, child proofs rebuilt from the returned JSON, parent assembly with a sorry stub of the uncle; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Antilipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/SpecialFunctions/Inner.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-4681cd171c/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/rc-split-check/Full.lean`
- `/tmp/rc-final/Verify.lean`

Pins: the snapshot manifest pins project b4d606db and Mathlib 25730c7c, and the snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f9503aa28…).

No local declaration states any of the seven children. SimonGMT Chapter03/Rectifiable.lean supplies only the definition CountablyRectifiable and the lemmas countablyRectifiable_range, _iUnion, _sUnion, _of_measure_zero and CountablyRectifiable.mono, which the children use. The related general-codimension DAG branch (cbr_rectifiable_of_approx_tangent → cbrr_cone_claim, cbrr_rectifiable_of_uniform_density) is unaccepted and has different types, so nothing is reused.

Snapshot Mathlib supplies:
- measurable_measure_prodMk_left (Prod.lean:97);
- LipschitzOnWith.extend_real (Lipschitz.lean:308);
- AntilipschitzWith.isClosed_range (Antilipschitz.lean:175);
- OrthonormalBasis.fromOrthogonalSpanSingleton (PiL2.lean:1157);
- MeasurableSet.exists_isCompact_sdiff_lt (Regular.lean:843), with an InnerRegularCompactLTTop instance for every measure on Euclid (RegularityCompacts.lean:186);
- tendsto_measure_iUnion_atTop (Continuity.lean:198);
- IsCompact.finite_cover_balls (Pseudo/Basic.lean:260);
- TopologicalSpace.isOpen_biUnion_countable.
Measurable.inner (SpecialFunctions/Inner.lean) is outside the import closure, so Continuous.measurable2 is used instead.

Lean: all 7 child types elaborate after import GMT.Ch07.Submission in namespace GMT.Ch07 with the contract opens. Every child is proved with axioms propext, Classical.choice, Quot.sound only. The selected frozen type is proved from halving_step, of_halving and a sorry stub of the uncle Submission.codim1_rdo_dg_flat_tangent_density_cone; the only extra axiom is sorryAx, from that stub.

Names: the 7 codim1_rdo_dg_rc_* identifiers occur nowhere in dag.json (945 nodes), GMT/, SimonGMT or Mathlib.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
