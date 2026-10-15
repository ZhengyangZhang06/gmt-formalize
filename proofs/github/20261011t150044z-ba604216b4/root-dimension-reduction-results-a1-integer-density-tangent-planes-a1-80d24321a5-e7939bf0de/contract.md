<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.integer_density-a1 -->

## Theorem `Submission.idtp_integer_density_off_null`

For all n, k, ℓ ∈ ℕ with ℓ ≤ k and n ≥ 1, all sets U, N ⊆ ℝ^{n+k} and every T ∈ 𝒟_n(U): if U is open, N is an embedded C² (n+ℓ)-dimensional submanifold (IsEmbeddedSubmanifold 2 (n + ℓ) N), (closure N ∖ N) ∩ U = ∅, T is minimizing in U ∩ N (IsMinimizingIn T (U ∩ N)), spt T ⊆ U ∩ N and ∂T = 0 in U (BoundaryVanishes T), then there is a set E ⊆ ℝ^{n+k} with μH[n − 3 + α](E) = 0 for every real α > 0 such that for every x ∈ U ∖ E there is an integer m with HasMassDensity T x m (Θ^n(μ_T, x) = m).

Node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.integer_density-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1032

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4777, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4780, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4833

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5469, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5479, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5489, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5495, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5499

## Lean problem

Declaration: `Submission.idtp_integer_density_off_null`

```lean
∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n), 1 ≤ n → IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → ∃ E : Set (Euclid (n + k)), (∀ α : ℝ, 0 < α → μH[(n : ℝ) - 3 + α] E = 0) ∧ ∀ x ∈ U \ E, ∃ m : ℤ, HasMassDensity T x m
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

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.integer_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent steps 1–4 (Simon 7.3.3(1), Lemma 3.5 and the proof of 3.3(1), chapter-07.txt lines 367–510), with the parent's conventions; the classification of 2-dimensional minimizing cones, which the book cites to [Whi82] at lines 501–504, enters only through the sibling child two_dim_cone_density, where it is proved. P := n + k. For an integer multiplicity current A on an open set, μ_A denotes the measure R.measure of any representation R of A (all representations have the same measure), M_W(A) = μ_A(W) for open W inside the domain of A, and spt A = {x in the domain : μ_A(B_ε(x)) > 0 for every ε > 0} (sibling result im_mass_measure (c), (a), (b), `Submission.dimred_im_mass_measure`); Θ_A := Θ^n(μ_A, ·); ω_n := unitBallVolume n; η_{y,λ}(w) := λ^{−1}(w − y), so blowUp T y λ = η_{y,λ#}T ∈ 𝒟_n(η_{y,λ}(U)); H^n := μHE[n] = c_nμH[n] with c_n ∈ (0, ∞) (Mathlib `euclideanHausdorffMeasure_def`, `addHaarScalarFactor_volume_hausdorffMeasure_ne_zero`), so H^n and μH[n] have the same null sets. Mass scaling of blow-ups: M_{η_{y,λ}(W)}(η_{y,λ#}T) = λ^{−n}M_W(T) for λ > 0 (Simon 6.2.23; the accepted `Submission.dtc_blowUp_massOn_image`). B_ρ(x) is the open ball.
1. (Densities.) Since n ≥ 1 and ∂T = 0, boundarySupport T = spt 0 = ∅. By the sibling result monotonicity (`Submission.dimred_minimizing_monotonicity`, with P := n + k and d := n + ℓ, so 1 ≤ n ≤ d ≤ P), there is Θ : ℝ^P → ℝ with HasMassDensity T x Θ(x) for x ∈ U (so Θ ≥ 0 on U), Θ upper semicontinuous on U, and Θ ≥ 1 on spt T; for each compact K ⊆ U there is Λ_K ≥ 0 such that e^{Λ_Kρ}ρ^{−n}μ_T(B_ρ(y)) is nondecreasing on (0, R) whenever closedBall y R ⊆ K (here M_{B_ρ(y)}(T) = μ_T(B_ρ(y)) because B_ρ(y) ⊆ U). Put E := {x ∈ U : Θ(x) ∉ ℤ}. For x ∈ U ∖ E, m := Θ(x) ∈ ℤ satisfies HasMassDensity T x m. It remains to prove μH[n − 3 + α](E) = 0 for every α > 0.
2. (Uniform density bounds.) Let K ⊆ U be compact with Θ < θ₁ on K, let θ₂ > θ₁, and let K'' ⊆ U be a compact set containing a 2σ₀-neighbourhood of K (σ₀ > 0). Then there is ρ₀ > 0 with μ_T(B_ρ(y)) ≤ θ₂ω_nρ^n for y ∈ K and ρ < ρ₀. Proof: for y ∈ K choose ρ_y ∈ (0, σ₀) with e^{Λρ_y}μ_T(B_{ρ_y}(y))/(ω_nρ_y^n) < θ₁ (Λ := Λ_{K''}; possible because the ratio tends to Θ(y) < θ₁ and e^{Λρ} → 1), and τ_y ∈ (0, ρ_y) with θ₁(ρ_y/(ρ_y − τ_y))^n ≤ θ₂. For |y' − y| < τ_y and ρ < ρ_y − τ_y, monotonicity at y' (closedBall y' ρ_y ⊆ K'') and B_{ρ_y−τ_y}(y') ⊆ B_{ρ_y}(y) give e^{Λρ}μ_T(B_ρ(y'))/(ω_nρ^n) ≤ e^{Λρ_y}μ_T(B_{ρ_y}(y))/(ω_n(ρ_y − τ_y)^n) < θ₁(ρ_y/(ρ_y − τ_y))^n ≤ θ₂. Cover K by finitely many B_{τ_y}(y) and let ρ₀ be the least ρ_y − τ_y.
3. (Densities of admissible zero-scale limits.) Let z ∈ ℝ^P and r > 0 with closedBall z (2r) ⊆ U, and θ₂ > 0, ρ₀ > 0 such that μ_T(B_ρ(y)) ≤ θ₂ω_nρ^n for y ∈ B_{3r/2}(z) and ρ < ρ₀. Let x_i ∈ B_r(z), λ_i > 0 with λ_i → 0, and S ∈ 𝒟_n(ℝ^P) with blowUp T x_i λ_i ⇀ S (ConvergesWeakly), S minimizing in ℝ^P with ∂S = 0. Then: (a) M_{B_ρ(w)}(S) ≤ θ₂ω_nρ^n for all w ∈ ℝ^P and ρ > 0, hence θ ≤ θ₂ whenever HasMassDensity S w θ; (b) S is integer multiplicity, and if R_S = (M_S, θ_S, ξ_S) represents S, then for H^n-a.e. y ∈ M_S, HasMassDensity S y θ_S(y), where θ_S(y) is an integer ≥ 1. Proof of (a): fix w and ρ > 0. For all large i, |x_i + λ_iw − z| < r + λ_i|w| < 3r/2 and λ_iρ < min(ρ₀, r/2); then B_{λ_iρ}(x_i + λ_iw) ⊆ B_{2r}(z) ⊆ U, and B_ρ(w) = η_{x_i,λ_i}(B_{λ_iρ}(x_i + λ_iw)) lies in the domain η_{x_i,λ_i}(U) of blowUp T x_i λ_i. By mass scaling and im_mass_measure (a), M_{B_ρ(w)}(blowUp T x_i λ_i) = λ_i^{−n}M_{B_{λ_iρ}(x_i+λ_iw)}(T) = λ_i^{−n}μ_T(B_{λ_iρ}(x_i + λ_iw)) ≤ θ₂ω_nρ^n. The sibling child weak_limit_mass_bound (W := B_ρ(w), B := θ₂ω_nρ^n) gives M_{B_ρ(w)}(S) ≤ θ₂ω_nρ^n. If HasMassDensity S w θ, then ofReal(θ) = lim_{ρ↓0} M_{B_ρ(w)}(S)/(ω_nρ^n) ≤ θ₂, so θ ≤ θ₂. Proof of (b): S is integer multiplicity because it is minimizing. R_S is a representation on ℝ^P, so μ_S(K) = ∫_{M_S ∩ K} θ_S dH^n < ∞ for every compact K (local integrability of the multiplicity). By the sibling child density_eq_multiplicity_ae, for H^n-a.e. y ∈ ℝ^P, μ_S(B_ρ(y))/(ω_nρ^n) → 1_{M_S}(y)θ_S(y); for y ∈ M_S the limit is θ_S(y), a positive integer (θ_S is ℕ-valued and positive on M_S), and since M_{B_ρ(y)}(S) = μ_S(B_ρ(y)) (im_mass_measure (a)), HasMassDensity S y θ_S(y).
4. (μH[n − 3 + α](E) = 0, and E = ∅ if n ≤ 2.) For m ∈ ℕ, m ≥ 1, and β ∈ ℚ ∩ (0, 1/2) let U_{m,β} := {x ∈ U : Θ(x) < m − β} (open, since Θ is upper semicontinuous on the open set U) and E_{m,β} := {x ∈ U_{m,β} : Θ(x) ≥ m − 1 + β}. Every x ∈ E has Θ(x) ≥ 0 and Θ(x) ∉ ℤ, so Θ(x) ∈ (m − 1, m) for the integer m := ⌈Θ(x)⌉ ≥ 1, and then x ∈ E_{m,β} for every rational β with 0 < β < min(1/2, Θ(x) − m + 1, m − Θ(x)); so E = ∪_{m,β}E_{m,β}, a countable union. Fix (m, β) and x₀ ∈ U_{m,β}, and choose σ > 0 with closedBall x₀ (4σ) ⊆ U_{m,β}. By step 2 (K := closedBall x₀ (3σ/2), σ₀ := σ, K'' := closedBall x₀ (4σ), which contains the 2σ-neighbourhood of K, θ₁ := m − β, θ₂ := m − β/2; Θ < m − β on K'') there is ρ₀ > 0 with μ_T(B_ρ(y)) ≤ (m − β/2)ω_nρ^n for y ∈ B_{3σ/2}(x₀) and ρ < ρ₀. Apply the sibling result threshold_reduction (`Submission.dimred_threshold_reduction`) with z := x₀, r := σ (closedBall x₀ (2σ) ⊆ U), c := m − 1 + β > 0 and d₀ := n − 2 (natural subtraction). Call S ∈ 𝒟_n(ℝ^P) an admissible zero-scale limit if blowUp T x_i λ_i ⇀ S (ConvergesWeakly) for some x_i ∈ B_σ(x₀) and λ_i > 0 with λ_i → 0, S is minimizing in ℝ^P and ∂S = 0; step 3 applies to every such S with z := x₀, r := σ, θ₂ := m − β/2. Hypothesis (H1) of threshold_reduction: let S be an admissible zero-scale limit, Q an n-dimensional subspace and c' ≥ c with HasMassDensity S y (1_Q(y)c') for every y ∈ ℝ^P; we derive a contradiction. Since 0 ∈ Q, HasMassDensity S 0 c', so c' ≤ m − β/2 by step 3(a). Let R_S = (M_S, θ_S, ξ_S) represent S and μ_S := R_S.measure. If μ_S = 0, then M_{B_ρ(0)}(S) = μ_S(B_ρ(0)) = 0 for every ρ > 0, so the density ratio of S at 0 vanishes identically and, by uniqueness of limits, ofReal(c') = 0, contradicting c' ≥ c > 0. Hence μ_S ≠ 0, so H^n(M_S) > 0 (μ_S = θ_S·H^n⌞M_S), and by step 3(b) there is y ∈ M_S with HasMassDensity S y θ_S(y), θ_S(y) an integer ≥ 1. By uniqueness of the limit (both values are ≥ 0 and ofReal is injective on [0, ∞)), θ_S(y) = 1_Q(y)c'; as θ_S(y) ≥ 1 > 0, y ∈ Q and c' = θ_S(y) ∈ ℤ. But m − 1 < m − 1 + β = c ≤ c' ≤ m − β/2 < m and no integer lies strictly between m − 1 and m: a contradiction. Hypothesis (H2): let S be an admissible zero-scale limit and L a linear subspace with d₀ ≤ d := dim L < n such that HasMassDensity S w θ implies HasMassDensity S (y + λw) θ for all y ∈ L, λ > 0, w and θ, and such that for every y ∈ ℝ^P: (there is θ ≥ c with HasMassDensity S y θ) ⟺ y ∈ L; we derive a contradiction. Since 0 ∈ L there is θ₀ ≥ c = m − 1 + β with HasMassDensity S 0 θ₀, and θ₀ ≤ m − β/2 by step 3(a). Since d₀ ≤ d < n, n − d ∈ {1, 2} (if n ≥ 2 then d₀ = n − 2 ≤ d ≤ n − 1; if n = 1 then d = 0). By the sibling result cone_splitting (`Submission.dimred_invariant_cone_splitting`; dim L < n, S minimizing in ℝ^P with ∂S = 0, and the density invariance just stated) there is S₀ ∈ 𝒟_{n−d}(ℝ^P), minimizing in ℝ^P, with ∂S₀ = 0 and a cone, such that HasMassDensity S (t + y) θ ⟺ HasMassDensity S₀ y θ for t ∈ L, y ∈ L^⊥; with t = y = 0, HasMassDensity S₀ 0 θ₀. Case n − d = 1: transport S₀ along the equality n − d = 1 to a current in 𝒟_1(ℝ^P) (minimality, ∂S₀ = 0, the cone property and HasMassDensity are preserved); the sibling result one_dim_cones (`Submission.dimred_one_dim_minimizing_cone`) gives e ∈ ℝ^P and m' ∈ ℕ with HasMassDensity S₀ y m' for every y ∈ span{e}; with y = 0 and uniqueness of the density limit, θ₀ = m' ∈ ℤ. Case n − d = 2: transport S₀ along the equality n − d = 2 to a current in 𝒟_2(ℝ^P) (minimality, ∂S₀ = 0, the cone property and HasMassDensity are preserved); the sibling child two_dim_cone_density gives m'' ∈ ℕ with HasMassDensity S₀ 0 m''; by uniqueness of the density limit, θ₀ = m'' ∈ ℤ. In both cases θ₀ ∈ ℤ and m − 1 < m − 1 + β ≤ θ₀ ≤ m − β/2 < m: a contradiction. Hence threshold_reduction gives: μH[d₀ − 1 + α](Z) = 0 for every α > 0, and Z = ∅ if d₀ = 0, where Z := {x ∈ B_σ(x₀) : HasMassDensity T x θ for some θ ≥ m − 1 + β} ⊇ E_{m,β} ∩ B_σ(x₀) (take θ := Θ(x)). If n ≥ 3 then d₀ = n − 2 ≥ 1 and (d₀ : ℝ) − 1 + α = n − 3 + α; if n ≤ 2 then d₀ = 0 and E_{m,β} ∩ B_σ(x₀) = ∅. By Lindelöf, countably many such balls B_σ(x₀) (x₀ ∈ U_{m,β}) cover U_{m,β} ⊇ E_{m,β}. Hence, by countable subadditivity, μH[n − 3 + α](E) = 0 for every α > 0 if n ≥ 3; and if n ≤ 2 then E = ∅, so μH[n − 3 + α](E) = 0 for every real α as well. Together with step 1 this proves the statement. ∎

## Key steps

1. Monotonicity gives an upper semicontinuous density Θ on U, Θ ≥ 1 on spt T, and the e^{Λρ}ρ^{−n} monotone mass ratios; E := {x ∈ U : Θ(x) ∉ ℤ}.
2. Uniform density bounds near compact sets where Θ < θ₁ (monotonicity plus a finite cover).
3. Admissible zero-scale limits S inherit the bound M_{B_ρ(w)}(S) ≤ θ₂ω_nρ^n (weak_limit_mass_bound) and have integer densities ≥ 1 H^n-a.e. on their carrier (density_eq_multiplicity_ae).
4. E = ∪ E_{m,β}; per ball B_σ(x₀) apply threshold_reduction with c = m − 1 + β, d₀ = n − 2: (H1) fails by integrality of c'; (H2) fails by cone_splitting with one_dim_cones (n − d = 1) or two_dim_cone_density (n − d = 2).
5. Lindelöf and countable subadditivity give μH[n − 3 + α](E) = 0, and E = ∅ for n ≤ 2.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (compared with manifest.json)`
- `grep -n '^theorem\|^def' simongmt Chapter02/{AreaNoninjective,AreaLipschitz,AreaMultiplicity,AreaBranches,AreaApproximation,WeightedArea}.lean Chapter03/{Rectifiable,Differential,SubmanifoldCover}.lean`
- `grep -rn 'weighted_area_formula_lipschitz_injOn|area_image_compl_regularSet_eq_zero|measurable_areaJacobianAt|weightedAreaFiberSum_iUnion|exists_injective_partition_of_regular|ae_eq_const_of_weak_coordinate_derivatives_zero' simongmt/Poincare/SimonGMT`
- `grep -rn 'normDet_sq_eq_det_gram|normDet_comp|euclideanHausdorffMeasure_image|exists_partition_approximatesLinearOn_of_hasFDerivWithinAt|LipschitzWith.ae_differentiableAt|Besicovitch.ae_tendsto_measure_inter_div|extend_finite_dimension|ContDiffOn.exists_lipschitzOnWith|lintegral_withDensity_eq_lintegral_mul_non_measurable|EventuallyEq.fderiv_eq|AEMeasurable.ennreal_tsum|lintegral_tsum|restrict_iUnion|exists_antilipschitzWith' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -rln 'C1Approximation|c1_approximation|lusin_c1' simongmt/Poincare/SimonGMT (no match); grep -n 'area formula' book/chapter-03.txt; sed -n 330,412p book/chapter-03.txt`
- `python3 scan of dag.json: lean_names containing idtp (none) or area; lean statements of dpf_rectifiable_bilipschitz_pieces, dpf_approxTangent_ae_bilipschitz_piece, dpf_area_formula_bilipschitz_rectifiable, imrep_approxTangent_starProjection_aesm, dtc_* lemmas and dimred_* siblings`
- `grep -l idtp_ nodes/*/*.json outside this node (none); for d in .swarm-worktrees/*/gmt-ch07/GMT: grep -rl 'idtp_|carrier_area_formula' (none)`
- `lean /tmp/idtp_v3/check/Probe.lean (normDet, weightedAreaFiberSum, areaJacobianAt, tangentialJacobian are not in the import closure of GMT.Ch07.Submission)`
- `lean /tmp/idtp_v3/check/NewChild.lean; lean /tmp/idtp_v3/check/GramCheck.lean (#print axioms idtp_v3_gram_sqrt_eq_normDet)`
- `lean /tmp/idtp_v3/check/FromJsonV3.lean (#print axioms idtp_parent_check_json_v3)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaNoninjective.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaMultiplicity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaBranches.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-bilipschi-4344c8c0d8/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-680a7024c9/parent-supplied-natural-proof.md`
- `/tmp/idtp_v3/check/FromJsonV3.lean`
- `/tmp/idtp_v3/check/GramCheck.lean`
- `/tmp/idtp_v3/check/NewChild.lean`
- `/tmp/idtp_v3/check/Probe.lean`

Pins match. The snapshot has project b4d606d (equal to workspace HEAD) and mathlib 25730c7c; SimonGMT is 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

Library support for the new child.
- SimonGMT provides the Euclidean-domain Lipschitz area formulas: weighted_area_formula_lipschitz_fiberSum and aemeasurable_weightedAreaFiberSum_lipschitz (AreaNoninjective.lean); weighted_area_formula_lipschitz_injOn with arbitrary weights, areaRegularSet, measurableSet_areaRegularSet and area_image_compl_regularSet_eq_zero (AreaLipschitz.lean); measurable_areaJacobianAt; weightedAreaFiberSum_iUnion.
- SimonGMT also provides HasApproximateTangentSpaceAt.unique and ae_eq_const_of_weak_coordinate_derivatives_zero (C¹ test functions).
- SimonGMT has no area formula on rectifiable carriers, no C¹ approximation theorem, and no rectifiable⇒C¹-cover direction of Ch. 3 Lemma 1.2 (searches found no match; the SubmanifoldCover header confirms this). The new child therefore proves Simon 2.4–2.5 from Lipschitz bi-Lipschitz pieces.
- Mathlib provides normDet_sq_eq_det_gram, normDet_comp, LinearMap.euclideanHausdorffMeasure_image, exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, Rademacher's theorem, Besicovitch density, Lipschitz extension, ContDiffOn.exists_lipschitzOnWith, lintegral_withDensity_eq_lintegral_mul_non_measurable and EventuallyEq.fderiv_eq.

Lean statement of the new child. normDet, weightedAreaFiberSum, areaJacobianAt and tangentialJacobian are not in the import closure of GMT.Ch07.Submission. The new type therefore writes the Jacobian as Real.sqrt (Matrix.det (Matrix.of Gram)) and the fibre sum as a tsum over a subtype. GramCheck.lean proves that this equals normDet of the restricted derivative (axioms propext, Classical.choice, Quot.sound).

DAG. The related other-branch nodes dpf_rectifiable_bilipschitz_pieces and dpf_approxTangent_ae_bilipschitz_piece are not comparator-accepted, so they are not reused; their arguments are re-proved inside the new child. Accepted lemmas cited by children (imrep_approxTangent_starProjection_aesm, dtc_*) have DAG types matching their uses.

Names. No idtp_* name occurs in dag.json, in other nodes' decompositions or in any worktree's GMT sources, so the 11 names are unreserved.

Lean check. All 11 statements elaborate, and the hypothesis-only assembly proves IntegerDensityAndTangentPlanes. Its axioms are propext, Classical.choice and Quot.sound, plus sorryAx from the stubs only.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
