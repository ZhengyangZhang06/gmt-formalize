<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.slice_decomposition-a1 -->

## Theorem `Submission.dimred_mbl_lc_slice_decomposition`

Let P, m ∈ ℕ and n := m + 1. Let C ∈ 𝒟_n(ℝ^P) and Ŝ_j ∈ 𝒟_n(ℝ^P) (j ∈ ℕ) be integer multiplicity currents (contract IsIntegerMultiplicity, currents GeometricCurrentOn univ), let κ_j (j ∈ ℕ) be measures on ℝ^P, K ⊆ ℝ^P compact and ε > 0. Assume: (FL′) for every open W₀ ⊆ ℝ^P with compact closure (CompactlyContained W₀ univ) there are integer multiplicity R_j ∈ 𝒟_{n+1}(ℝ^P) and S′_j ∈ 𝒟_n(ℝ^P) with C − Ŝ_j − S′_j = ∂R_j for every j and M_{W₀}(R_j) + M_{W₀}(S′_j) → 0; (SL′) for every T ∈ 𝒟_{n+1}(ℝ^P), all measures μ, μ′ on ℝ^P that are finite on compact sets, all maps ξ : ℝ^P → Λ_{n+1}(ℝ^P), ξ′ : ℝ^P → Λ_n(ℝ^P) (MultiVector) that are a.e. strongly measurable for μ, μ′ respectively, with |ξ(x)(α)| ≤ |α| for μ-a.e. x and all (n+1)-covectors α and |ξ′(x)(α)| ≤ |α| for μ′-a.e. x and all n-covectors α (|·| the Euclidean coefficient norm covectorEuclideanNorm), T(ω) = ∫ ξ(x)(ω(x)) dμ(x) for all ω ∈ 𝒟^{n+1}(ℝ^P) and ∂T(η) = ∫ ξ′(x)(η(x)) dμ′(x) for all η ∈ 𝒟ⁿ(ℝ^P), and every L-Lipschitz f : ℝ^P → ℝ (L ∈ [0, ∞)), there are currents A_t ∈ 𝒟_{n+1}(ℝ^P) and B_t ∈ 𝒟_n(ℝ^P) (t ∈ ℝ) with A_t(ω) = ∫_{f<t} ξ(ω) dμ, B_t(η) = ∫_{f<t} ξ′(η) dμ′, ∂A_t(η) = B_t(η) whenever tsupport η ∩ {f = t} = ∅, and M_W(∂A_t − B_t) ≤ L · liminf_{h→0⁺} h⁻¹ μ(W ∩ {t − h < f < t}) for every open W and every t; (BR′) every integer multiplicity R ∈ 𝒟_{n+1}(ℝ^P) with M_W(∂R) < ∞ for every open W with compact closure has an integer multiplicity boundary ∂R; (κ) for every r ∈ ℝ, κ_j(B_r(0)) < ∞ for all sufficiently large j. Then there are an open W ⊆ ℝ^P, a compact F ⊆ ℝ^P, a strictly increasing φ′ : ℕ → ℕ, numbers e_i ∈ [0, ∞] with e_i → 0, and currents Ŷ_i, Sr_i ∈ 𝒟_n(ℝ^P) (i ∈ ℕ) such that K ⊆ W ⊆ F, W ⊆ thickening(ε, K) (Mathlib Metric.thickening: the points at distance < ε from K; empty if K = ∅), and for every i: Ŷ_i is integer multiplicity, ∂Ŷ_i = 0 and spt Ŷ_i ⊆ F; M(Sr_i) ≤ e_i; μ_R(F ∖ W) ≤ e_i for every integer multiplicity representation R of Ŷ_i in ℝ^P (μ_R = R.measure); κ_{φ′(i)}(F ∖ W) = 0; and C(ω) = Ŝ_{φ′(i)}(ω) + Ŷ_i(ω) + Sr_i(ω) for every ω ∈ 𝒟ⁿ(ℝ^P) with tsupport ω ⊆ W.

Node: `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.slice_decomposition-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5076

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/667, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4196, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4695, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4704, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4728, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4710, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4718

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7040, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4684, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5327, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1174, https://github.com/ZhengyangZhang06/gmt-formalize/issues/667, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4196, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4695, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4704, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4728, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4710, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4718

## Lean problem

Declaration: `Submission.dimred_mbl_lc_slice_decomposition`

```lean
∀ (P m : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (Ŝ : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (κ : ℕ → Measure (Euclid P)) (K : Set (Euclid P)) (ε : ℝ), IsIntegerMultiplicity C → (∀ j, IsIntegerMultiplicity (Ŝ j)) → (∀ W₀ : Set (Euclid P), IsOpen W₀ → CompactlyContained W₀ univ → ∃ (R : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (S' : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ j, IsIntegerMultiplicity (R j) ∧ IsIntegerMultiplicity (S' j) ∧ C - Ŝ j - S' j = (R j).boundary) ∧ Tendsto (fun j => (R j).massOn W₀ + (S' j).massOn W₀) atTop (𝓝 0)) → (∀ (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (m + 2)) (ξ' : Euclid P → MultiVector P (m + 1)) (f : Euclid P → ℝ) (L : NNReal), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (m + 2), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) (m + 1), |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 2), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (m + 2)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) (m + 1), T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) (m + 1)) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (B : ℝ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ (t : ℝ) (ω : TestFormOn (univ : Set (Euclid P)) (m + 2)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (m + 2)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn (univ : Set (Euclid P)) (m + 1)), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) (m + 1)) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn (univ : Set (Euclid P)) (m + 1)), Disjoint (tsupport (η : DifferentialForm (Euclid P) (m + 1))) {x | f x = t} → (A t).boundary η = B t η) ∧ ∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) → (∀ R : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2), IsIntegerMultiplicity R → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W univ → R.boundary.massOn W < ∞) → IsIntegerMultiplicity R.boundary) → (∀ r : ℝ, ∀ᶠ j in atTop, κ j (ball 0 r) ≠ ∞) → IsCompact K → 0 < ε → ∃ (W F : Set (Euclid P)) (φ' : ℕ → ℕ) (e : ℕ → ℝ≥0∞) (Ŷ Sr : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsOpen W ∧ IsCompact F ∧ K ⊆ W ∧ W ⊆ F ∧ W ⊆ thickening ε K ∧ StrictMono φ' ∧ Tendsto e atTop (𝓝 0) ∧ ∀ i, IsIntegerMultiplicity (Ŷ i) ∧ (Ŷ i).boundary = 0 ∧ (Ŷ i).support ⊆ F ∧ (Sr i).mass ≤ e i ∧ (∀ R : IMRep (univ : Set (Euclid P)) (m + 1), R.Represents (Ŷ i) → R.measure (F \ W) ≤ e i) ∧ κ (φ' i) (F \ W) = 0 ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ W → C ω = Ŝ (φ' i) ω + Ŷ i ω + Sr i ω
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

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.slice_decomposition-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, steps 2, 4, 5, 6 and the ∂R̃-part of 8(c) (Simon 7.2.4 (1)–(7), chapter-07.txt lines 176–219, with the corrected sign S̃ = S′⌞W − P). The proof is extracted from those steps and specialized in three harmless ways: (i) the cut-off only has to be Lipschitz, because the slicing hypothesis (SL′) only uses a Lipschitz constant (the parent mollifies an indicator and uses L₀ = sup|Dψ_c|); (ii) the level α and the subsequence are chosen with the sibling good_slice_level, which is the parent's step 5(c) selection (difference quotients, Fatou in j, countably many atoms) packaged as a lemma; (iii) the parent's step 5(b) claim that P_{j,α} is integer multiplicity is not needed — only ∂(R_j⌞W) must be integer multiplicity, and it is, by (BR′).
Siblings: (MR) mass_and_support (first conjunct: M_G(T) = μ_R(G) for open G whenever the IMRep R represents T in an open domain); (IMC) im_calculus ((b) restriction of an IMRep to a Borel set represents a current, (c) differences of integer multiplicity currents are integer multiplicity, (d) |R.orient(x)(α)| ≤ |α| for Hⁿ-a.e. x of the carrier); (IR) imrep_restriction ((a) μ_R ≪ Hⁿ⌞M, (b) R.orient is μ_R-a.e. strongly measurable, (c) for Borel E and the restricted IMRep R′ with carrier M ∩ E: μ_{R′} = μ_R⌞E and R′.action(ω) = ∫_E R.orient(ω) dμ_R); (MT) mass_triangle; (COB) compact_outer_bound; (ML) mass_localization; (GL) good_slice_level.
Conventions. n := m + 1; all currents below are currents in ℝ^P; for an IMRep R write μ_R := R.measure and ξ_R := R.orient. For a set G, M_G is massOn G and M = M_{ℝ^P} is mass. A form ω is admissible for M_G if ω ∈ 𝒟(ℝ^P), tsupport ω ⊆ G and |ω(x)| ≤ 1 for all x.
0. (Local finiteness.) If R is an IMRep in ℝ^P (degree k) and K′ ⊆ ℝ^P is compact, then μ_R(K′) = ∫_{M∩K′} θ dH^k < ∞ (K′ is closed hence Borel; field locallyIntegrable_mult).
1. (Cut-off; parent step 2.) If K = ∅ put ψ := 0 and L := 0. Otherwise put δ := ε/2, ψ(x) := max{0, 1 − dist(x, K)/δ} and L := 1/δ. Then ψ is L-Lipschitz (x ↦ dist(x, K) is 1-Lipschitz, x ↦ 1 − dist(x, K)/δ is (1/δ)-Lipschitz, and taking the maximum with the constant 0 does not increase Lipschitz constants), 0 ≤ ψ ≤ 1 and ψ = 1 on K. Let W₀ := {ψ > 0}. For K ≠ ∅, W₀ = {dist(·, K) < δ} is open, W₀ ⊆ thickening(ε, K) because δ < ε, and closure(W₀) ⊆ {dist(·, K) ≤ δ}, a closed and bounded, hence compact, subset of ℝ^P; for K = ∅, W₀ = ∅. In both cases W₀ is open, closure(W₀) is compact and W₀ ⊆ thickening(ε, K). Put f := −ψ (L-Lipschitz, continuous, hence Borel) and fix r₀ > 0 with closure(W₀) ⊆ B_{r₀}(0).
2. (Flat convergence; parent step 4.) Apply (FL′) to W₀: R_j ∈ 𝒟_{n+1}, S′_j ∈ 𝒟_n integer multiplicity with C − Ŝ_j − S′_j = ∂R_j and a_j := M_{W₀}(R_j) + M_{W₀}(S′_j) → 0. By (IMC)(c) twice, C − Ŝ_j − S′_j = ∂R_j is integer multiplicity. Choose IMReps ρ_j of R_j, β_j of ∂R_j, σ_j of S′_j (all in ℝ^P), and write μ_j := μ_{ρ_j}, μ′_j := μ_{β_j}.
3. (Slicing; parent step 5.) Fix j and apply (SL′) to T := R_j, μ := μ_j, ξ := ξ_{ρ_j}, μ′ := μ′_j, ξ′ := ξ_{β_j} and the L-Lipschitz f. Its hypotheses hold: μ_j and μ′_j are finite on compact sets (step 0); ξ_{ρ_j}, ξ_{β_j} are a.e. strongly measurable for μ_j, μ′_j by (IR)(b); by (IMC)(d) the bound |ξ_{ρ_j}(x)(α)| ≤ |α| (all α) holds H^{n+1}⌞M-a.e. on the carrier M of ρ_j, hence μ_j-a.e. since μ_j ≪ H^{n+1}⌞M by (IR)(a), and likewise for β_j; R_j(ω) = ρ_j.action(ω) = ∫ ξ_{ρ_j}(ω) dμ_j by (IR)(c) with E := ℝ^P and R′ := ρ_j (carrier M = M ∩ ℝ^P), and likewise ∂R_j(η) = ∫ ξ_{β_j}(η) dμ′_j. Obtain A_{j,t} ∈ 𝒟_{n+1}, B_{j,t} ∈ 𝒟_n (t ∈ ℝ) with the four properties of (SL′).
4. (Level and subsequence; parent step 5(c).) By (κ) choose j₁ with κ_j(B_{r₀}(0)) < ∞ for all j ≥ j₁. Apply (GL) with ν_j := μ_j⌞W₀, κ′_j := κ_{j+j₁}, the Borel function f and (a, b) := (−1, 0); the set A′ := {−1 < f < 0} = {0 < ψ < 1} is contained in W₀ ⊆ B_{r₀}(0). Hypotheses: ν_j(A′) ≤ μ_j(W₀) ≤ μ_j(closure W₀) < ∞ (step 0); ν_j(A′) ≤ μ_j(W₀) = M_{W₀}(R_j) ≤ a_j → 0 by (MR) (W₀ open), so ν_j(A′) → 0; κ′_j(A′) ≤ κ_{j+j₁}(B_{r₀}(0)) < ∞. (GL) gives t ∈ (−1, 0) and a strictly increasing φ with (i) κ_{k+j₁}({f = t}) = 0 for every k, (ii) D_j < ∞ for every j and (iii) D_{φ(k)} → 0, where D_j := liminf_{h→0⁺} h⁻¹ν_j({t − h < f < t}). Since W₀ is open (Borel), ν_j(s) = μ_j(s ∩ W₀) = μ_j(W₀ ∩ s) for every set s, so D_j = liminf_{h→0⁺} h⁻¹μ_j(W₀ ∩ {t − h < f < t}).
Put α := −t ∈ (0, 1), W := {f < t} = {ψ > α}, F := {f ≤ t} = {ψ ≥ α}, Σ := F ∖ W = {f = t} = {ψ = α}, and φ′(i) := φ(i + j₁).
5. (W, F, φ′.) W is open and F is closed (f continuous). F ⊆ W₀ (ψ ≥ α > 0 on F), so F ⊆ closure(W₀) is compact, and Σ is a compact subset of the open set W₀. K ⊆ W (ψ = 1 > α on K), W ⊆ F, and W ⊆ W₀ ⊆ thickening(ε, K). φ′ is strictly increasing, and φ′(i) ≥ i + j₁ ≥ j₁ (a strictly increasing map ℕ → ℕ satisfies φ(k) ≥ k); writing φ′(i) = (φ′(i) − j₁) + j₁, (i) gives κ_{φ′(i)}(F ∖ W) = κ_{φ′(i)}({f = t}) = 0.
6. (The currents of index i; parent step 6.) Fix i and put j := φ′(i). By (IMC)(b) applied to ρ_j, β_j, σ_j and the Borel set W there are IMReps ρ′_j, β′_j, σ′_j in ℝ^P with carriers (carrier) ∩ W, the same multiplicities and orientations, each representing a current. By (IR)(c): ρ′_j.action(ω) = ∫_W ξ_{ρ_j}(ω) dμ_j = A_{j,t}(ω), so ρ′_j represents A_{j,t} and A_{j,t} = R_j⌞W is integer multiplicity; β′_j.action(η) = ∫_W ξ_{β_j}(η) dμ′_j = B_{j,t}(η), so β′_j represents B_{j,t}, with μ_{β′_j} = μ′_j⌞W; and σ′_j represents a current S′_j⌞W with (S′_j⌞W)(ω) = ∫_W ξ_{σ_j}(ω) dμ_{σ_j} and μ_{σ′_j} = μ_{σ_j}⌞W. Define
 Ŷ_i := ∂A_{j,t}, P_i := ∂A_{j,t} − B_{j,t}, Sr_i := S′_j⌞W − P_i, e_i := M_{W₀}(S′_{φ′(i)}) + L·D_{φ′(i)}.
7. (Mass of P_i; parent step 5(a).) By (SL′), P_i(η) = ∂A_{j,t}(η) − B_{j,t}(η) = 0 whenever tsupport η ∩ Σ = ∅. Σ is compact and contained in the open set W₀, so (ML) gives M_G(P_i) ≤ M_{W₀}(P_i) for every set G, and (SL′) with W := W₀ gives M_{W₀}(P_i) ≤ L·D_j. Hence M_G(P_i) ≤ L·D_j < ∞ for every G (L < ∞ and (ii)).
8. (Ŷ_i is an integer multiplicity cycle; parent step 5(b).) For every η, ∂A_{j,t}(η) = B_{j,t}(η) + 1·P_i(η). For open G with compact closure, (MT), (MR) for β′_j and step 7 give M_G(∂A_{j,t}) ≤ M_G(B_{j,t}) + M_G(P_i) ≤ μ_{β′_j}(G) + L·D_j ≤ μ′_j(closure G) + L·D_j < ∞ (step 0). Since A_{j,t} is integer multiplicity (step 6), (BR′) shows that Ŷ_i = ∂A_{j,t} is integer multiplicity. ∂Ŷ_i = ∂∂A_{j,t} = 0.
9. (spt Ŷ_i ⊆ F.) Let x ∉ F. As F is closed there is r > 0 with B := B_r(x) disjoint from F; B is open with compact closure. If η ∈ 𝒟ⁿ(ℝ^P) has tsupport η ⊆ B, then tsupport dη ⊆ tsupport η ⊆ B misses W ⊆ F, so dη = 0 on W and Ŷ_i(η) = A_{j,t}(dη) = ∫_{f<t} ξ_{ρ_j}(dη) dμ_j = 0. So B lies in the zero region of Ŷ_i and x ∉ spt Ŷ_i.
10. (Mass of Sr_i; parent step 6.) Sr_i(ω) = (S′_j⌞W)(ω) + (−1)·P_i(ω) for all ω, so (MT) with c = −1, (MR) for σ′_j and step 7 give M(Sr_i) ≤ M(S′_j⌞W) + M(P_i) ≤ μ_{σ_j}(W) + L·D_j = M_W(S′_j) + L·D_j ≤ M_{W₀}(S′_j) + L·D_j = e_i, using (MR) for σ_j and the monotonicity of M_G in G.
11. (Measure of Ŷ_i on F ∖ W; ∂R̃-part of parent step 8(c).) Let R be an IMRep of Ŷ_i. Σ = F ∖ W is compact. For every open G ⊇ Σ with compact closure, (MR), (MT) and steps 7–8 give μ_R(G) = M_G(Ŷ_i) ≤ M_G(B_{j,t}) + M_G(P_i) ≤ μ_{β′_j}(G) + L·D_j. (COB) with U := ℝ^P, E := Σ, ν := μ_{β′_j} (finite on compact sets, step 0) and c := L·D_j gives μ_R(Σ) ≤ μ_{β′_j}(Σ) + L·D_j = μ′_j(Σ ∩ W) + L·D_j = L·D_j ≤ e_i, since Σ ∩ W = ∅.
12. (Identity on W; parent (★).) Let ω ∈ 𝒟ⁿ(ℝ^P) with tsupport ω ⊆ W. (a) Evaluating C − Ŝ_j − S′_j = ∂R_j at ω: C(ω) − Ŝ_j(ω) − S′_j(ω) = R_j(dω) = ∫ ξ_{ρ_j}(dω) dμ_j; as tsupport dω ⊆ tsupport ω ⊆ W, the integrand vanishes off W = {f < t}, so this equals ∫_{f<t} ξ_{ρ_j}(dω) dμ_j = A_{j,t}(dω) = Ŷ_i(ω). (b) (S′_j⌞W)(ω) = ∫_W ξ_{σ_j}(ω) dμ_{σ_j} = ∫ ξ_{σ_j}(ω) dμ_{σ_j} = S′_j(ω), because ω = 0 off W ((IR)(c) with E := ℝ^P). (c) tsupport ω ⊆ W is disjoint from Σ, so P_i(ω) = 0 (step 7) and Sr_i(ω) = S′_j(ω). Therefore C(ω) = Ŝ_j(ω) + Ŷ_i(ω) + Sr_i(ω), with j = φ′(i).
13. (e_i → 0.) M_{W₀}(S′_{φ′(i)}) ≤ a_{φ′(i)} → 0 because φ′(i) → ∞; D_{φ′(i)} = D_{φ(i+j₁)} → 0 by (iii), so L·D_{φ′(i)} → 0 (L < ∞). Hence e_i → 0.
Steps 5–13 give all conclusions: W open, F compact, K ⊆ W ⊆ F, W ⊆ thickening(ε, K), φ′ strictly increasing, e_i → 0, and for every i the properties of Ŷ_i (steps 8, 9, 11), M(Sr_i) ≤ e_i (step 10), κ_{φ′(i)}(F ∖ W) = 0 (step 5) and the identity on W (step 12). ∎

## Key steps

1. Lipschitz cut-off ψ (= max{0, 1 − dist(·,K)/δ}), W₀ = {ψ > 0} with compact closure inside thickening(ε, K); (FL′) on W₀ gives C − Ŝ_j − S′_j = ∂R_j with M_{W₀}(R_j) + M_{W₀}(S′_j) → 0.
2. The representing measures of R_j and ∂R_j satisfy the hypotheses of (SL′) (imrep_restriction, im_calculus (d)); slice R_j by f = −ψ.
3. good_slice_level with ν_j = μ_{R_j}⌞W₀, κ′_j = κ_{j+j₁} on {0 < ψ < 1} gives α = −t, φ with κ-null level set and D_{φ(k)} → 0; W = {ψ > α}, F = {ψ ≥ α}, φ′(i) = φ(i + j₁).
4. P_i = ∂(R_j⌞W) − (∂R_j)⌞W: mass_localization and (SL′) give M(P_i) ≤ L·D_j; (BR′) makes Ŷ_i = ∂(R_j⌞W) an integer multiplicity cycle supported in F.
5. M(Sr_i) ≤ M_{W₀}(S′_j) + L·D_j and μ_{Ŷ_i}(F ∖ W) ≤ L·D_j (mass_triangle, compact_outer_bound); C = Ŝ_j + Ŷ_i + Sr_i on forms supported in W; e_i → 0.

## Reference use

### local-project

Queries:
- `cat RUN/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean`
- `python3 scans of RUN/dag.json: accepted nodes (status accepted, candidate_commit set) whose lean_statement mentions IsIntegerMultiplicity, IMRep, restrictDomain or .support; children of root.compactness_of_minimizing_currents-a1.local_comparison-a1; lean_name collisions for dimred_mbl_lc_slice_decomposition / dimred_mbl_lc_retraction_comparison / dimred_mbl_lc_index_comparison (no match); string comparison of cmc_imRep_locality_restrict_sub with the second conjunct of dimred_mbl_current_foundations (identical)`
- `grep -n '_existing_lean_name_problem\|_accepted_checkpoint' /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py; grep -n 'contract_scope\|child_modules' verifier/gmt-compare.py`
- `grep -n 'def GeometricCurrentOn.massOn\|def GeometricCurrentOn.support\|def GeometricCurrentOn.restrictDomain\|def testFormOnInclusion\|def HasApproximateTangentSpaceAt\|def blowUpMap' in lake-packages-25730c7c/simongmt/Poincare/SimonGMT`
- `grep -rn "norm_fderiv_le_of_lip'\|iSup_comp_le\|protected theorem Tendsto.const_mul\|theorem limsup_le_limsup" lake-packages-25730c7c/mathlib/Mathlib`
- `sed -n 150,275p book/chapter-07.txt (Simon 7.2.4–7.2.5)`
- `lake env lean /tmp/lc_dec/Types.lean (all 12 child types as _root_ theorems after import GMT.Ch07.Submission in the replayed contract scope); lake env lean /tmp/lc_dec/Assembly.lean (#print axioms assembly_check)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-comparison-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-im-calculus-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-localize-a1-restrict-im-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1-imrep-1bd5f15878/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1-mass-triangle-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1-compac-a4168491cb/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1-mass-l-9981f1246a/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1-good-s-2d2986292d/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/lc_dec/Types.lean`
- `/tmp/lc_dec/Assembly.lean`

Pins match the manifest (project b4d606d, Mathlib 25730c7c, SimonGMT 2b366308) and Submission.lean equals the frozen contract. Nine comparator-accepted declarations with candidate commits supply this proof's foundational facts and are reused with byte-identical types: dtc_vanish_off_support (VO), dor_imrep_massOn_eq_measure_and_support (MR), cmc_imRep_locality_restrict_sub (IMC; equal to the second conjunct of the decomposing sibling foundations), dtc_restrictDomain_isIntegerMultiplicity (F5), lcmp_imRep_measure_restrict (F4), lcmp_massOn_le_add_of_eval_eq and lcmp_measure_le_add_of_open_nhds (F3), lcmp_massOn_le_of_vanish_off_compact (step 5(a)) and lcmp_exists_good_slice_level (step 5(c)). The siblings flat_convergence, slicing, closure_and_boundary_rectifiability and pushforward are decomposing, and a child may only use its own children and depends_on, so the new children take them as hypotheses. Neither the pinned libraries nor accepted nodes contain the slice decomposition, the retraction comparison or the per-index comparison, so these are new; the three dimred_mbl_lc_* names are unused in the DAG. Lean checks: all 12 child types elaborate in the comparator scope. The conditional assembly proves the exact parent type from slice_decomposition and index_comparison plus the parent's sibling types FL, SL, BR, PF and MR, with axioms propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
