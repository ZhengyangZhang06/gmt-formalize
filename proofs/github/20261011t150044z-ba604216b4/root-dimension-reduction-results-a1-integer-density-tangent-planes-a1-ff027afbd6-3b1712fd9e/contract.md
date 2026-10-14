<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.class_reduction-a1 -->

## Theorem `Submission.idtp_fons_flat_class_reduction`

Let P, n ∈ ℕ with n ≥ 1, Λ ∈ ℝ, let 𝓜 be a set of measures on ℝ^P and D a map from measures on ℝ^P to subsets of ℝ^P. For a measure μ on ℝ^P and x ∈ ℝ^P let dens μ x := (limsup_{ρ↓0} μ(B_ρ(x))/(ω_nρ^n)).toReal (limsup in [0, ∞] along ρ → 0⁺, ω_n = unitBallVolume n; in the Lean statement dens is a universally quantified function fixed by this defining equation); for y ∈ ℝ^P and λ > 0, μ^{y,λ} := ofReal(λ^{−n})•μ.map(η_{y,λ}) (= λ^{−n}(η_{y,λ})_#μ, η_{y,λ} = dilation y λ); spt μ := {w : μ(B_ε(w)) ≠ 0 for every ε > 0}; μ_j → μ vaguely means ∫ f dμ_j → ∫ f dμ for every continuous compactly supported f : ℝ^P → ℝ. Assume (M1) every μ ∈ 𝓜 is finite on compact sets; (M2) every μ ∈ 𝓜 equals Hⁿ.withDensity(ofReal ∘ dens μ) (Hⁿ = μHE[n]); (M3) for μ ∈ 𝓜, 0 < λ < 1 and |y| ≤ 1 − λ: μ^{y,λ} ∈ 𝓜 and D(μ^{y,λ}) = η_{y,λ}(D μ); (M4) for μ ∈ 𝓜, |y| < 1 and every strictly decreasing sequence λ_j > 0 with λ_j → 0 there are a strictly increasing sub : ℕ → ℕ and ν ∈ 𝓜 with dens ν(tw) = dens ν(w) for all t > 0 and w, and μ^{y,λ_{sub(j)}} → ν vaguely; (M5) for μ ∈ 𝓜, D μ is open and contains B_2(0); (M6) if μ ∈ 𝓜, μ_j ∈ 𝓜 (j ∈ ℕ) and μ_j → μ vaguely, then every compact K ⊆ D μ satisfies K ⊆ D(μ_j) for all large j; (M7) for μ ∈ 𝓜, y ∈ spt μ and ρ > 0 with closedBall y ρ ⊆ D μ: e^{−Λρ}·ω_nρ^n ≤ μ(B_ρ(y)); (M8) if ν ∈ 𝓜 and L is a linear subspace with dim L + 1 = n and dens ν(y + tw) = dens ν(w) for all y ∈ L, t > 0 and w, then spt ν ⊆ Q for some n-dimensional linear subspace Q; (M9) if ν ∈ 𝓜 and dens ν(tw) = dens ν(w) for all t > 0 and w, then D ν = ℝ^P. Then for every μ ∈ 𝓜 and every β > 0 there is a set Z ⊆ ℝ^P such that Z = ∅ if n = 1, μH[n − 2 + α](Z) = 0 for every real α > 0, and every w ∈ B_1(0) ∩ spt μ with w ∉ Z is β-flat in D μ: there are ρ > 0 with B_ρ(w) ⊆ D μ, an n-dimensional linear subspace Q ⊆ ℝ^P and s < βρ such that |(y − w) − p_Q(y − w)| ≤ s for every y ∈ spt μ ∩ B_ρ(w) (p_Q = Q.starProjection).

Node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.class_reduction-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4842

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/385

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6948, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6963, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6976, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6987, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6996, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7005, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7013

## Lean problem

Declaration: `Submission.idtp_fons_flat_class_reduction`

```lean
∀ (P n : ℕ) (Λ : ℝ) (𝓜 : Set (Measure (Euclid P))) (D : Measure (Euclid P) → Set (Euclid P)) (dens : Measure (Euclid P) → Euclid P → ℝ), 1 ≤ n → (∀ (μ : Measure (Euclid P)) (x : Euclid P), dens μ x = (limsup (fun ρ : ℝ => μ (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0)).toReal) → (∀ μ ∈ 𝓜, ∀ K : Set (Euclid P), IsCompact K → μ K ≠ ∞) → (∀ μ ∈ 𝓜, μ = (μHE[n] : Measure (Euclid P)).withDensity (fun x => ENNReal.ofReal (dens μ x))) → (∀ μ ∈ 𝓜, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → ENNReal.ofReal (lam⁻¹ ^ n) • μ.map (dilation y lam) ∈ 𝓜 ∧ D (ENNReal.ofReal (lam⁻¹ ^ n) • μ.map (dilation y lam)) = dilation y lam '' D μ) → (∀ μ ∈ 𝓜, ∀ y : Euclid P, ‖y‖ < 1 → ∀ lams : ℕ → ℝ, (∀ j, 0 < lams j) → StrictAnti lams → Tendsto lams atTop (𝓝 0) → ∃ (sub : ℕ → ℕ) (ν : Measure (Euclid P)), StrictMono sub ∧ ν ∈ 𝓜 ∧ (∀ t : ℝ, 0 < t → ∀ w : Euclid P, dens ν (t • w) = dens ν w) ∧ ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun j => ∫ x, f x ∂(ENNReal.ofReal ((lams (sub j))⁻¹ ^ n) • μ.map (dilation y (lams (sub j))))) atTop (𝓝 (∫ x, f x ∂ν))) → (∀ μ ∈ 𝓜, IsOpen (D μ) ∧ ball (0 : Euclid P) 2 ⊆ D μ) → (∀ μ ∈ 𝓜, ∀ μs : ℕ → Measure (Euclid P), (∀ j, μs j ∈ 𝓜) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun j => ∫ x, f x ∂(μs j)) atTop (𝓝 (∫ x, f x ∂μ))) → ∀ K : Set (Euclid P), IsCompact K → K ⊆ D μ → ∀ᶠ j in atTop, K ⊆ D (μs j)) → (∀ μ ∈ 𝓜, ∀ (y : Euclid P) (ρ : ℝ), 0 < ρ → closedBall y ρ ⊆ D μ → (∀ ε : ℝ, 0 < ε → μ (ball y ε) ≠ 0) → ENNReal.ofReal (Real.exp (-(Λ * ρ))) * (unitBallVolume n * ENNReal.ofReal (ρ ^ n)) ≤ μ (ball y ρ)) → (∀ ν ∈ 𝓜, ∀ L : Submodule ℝ (Euclid P), Module.finrank ℝ L + 1 = n → (∀ y ∈ L, ∀ t : ℝ, 0 < t → ∀ w : Euclid P, dens ν (y + t • w) = dens ν w) → ∃ Q : Submodule ℝ (Euclid P), Module.finrank ℝ Q = n ∧ ∀ w : Euclid P, (∀ ε : ℝ, 0 < ε → ν (ball w ε) ≠ 0) → w ∈ Q) → (∀ ν ∈ 𝓜, (∀ t : ℝ, 0 < t → ∀ w : Euclid P, dens ν (t • w) = dens ν w) → D ν = univ) → ∀ μ ∈ 𝓜, ∀ β : ℝ, 0 < β → ∃ Z : Set (Euclid P), (n = 1 → Z = ∅) ∧ (∀ α : ℝ, 0 < α → μH[(n : ℝ) - 2 + α] Z = 0) ∧ ∀ w ∈ ball (0 : Euclid P) 1, (∀ ε : ℝ, 0 < ε → μ (ball w ε) ≠ 0) → w ∉ Z → ∃ ρ : ℝ, 0 < ρ ∧ ball w ρ ⊆ D μ ∧ ∃ Q : Submodule ℝ (Euclid P), Module.finrank ℝ Q = n ∧ ∃ s : ℝ, s < β * ρ ∧ ∀ y : Euclid P, (∀ ε : ℝ, 0 < ε → μ (ball y ε) ≠ 0) → y ∈ ball w ρ → ‖(y - w) - Q.starProjection (y - w)‖ ≤ s
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

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.class_reduction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof steps 2 (density functions (i)–(vii) and (T3s)), 3 (the flatness maps: closedness, A.3(1)–(3)) and 4 (Appendix A.4 and the exclusion of d = n − 1); Simon 7.3.3, Remark 3.4 and proof of 3.3(2), chapter-07.txt lines 485–583, with the parent's errata (in R_β the bound is sup|q(y − x)| < βρ; ∩_j instead of ∪_j in (12), (13)) and departure [D1] (scalar density functions; the domain of a member enters through D). Here the class properties (M1)–(M9) replace the parent's analysis of the currents; the arguments are those of the parent. Uses the reused accepted declaration abstract_dimension_reduction (Submission.abstract_dimension_reduction).
Notation. e₁ := EuclideanSpace.single 0 1 ∈ Euclid 1 (|e₁| = 1); φ_μ(x) := dens μ x • e₁; Hⁿ := μHE[n] = c•μH[n] with c := addHaarScalarFactor(volume, μH[n]) ∈ ℝ≥0, c ≠ 0 (euclideanHausdorffMeasure_def, addHaarScalarFactor_volume_hausdorffMeasure_ne_zero); μ^{y,t}, spt, vague convergence as in the statement; q_Q(v) := v − p_Q(v) (|q_Q(v)| ≤ |v|). Fix β > 0. For μ ∈ 𝓜 let R(μ) be the set of w ∈ spt μ for which there are ρ > 0 with B_ρ(w) ⊆ D μ, an n-dimensional Q and s < βρ with |q_Q(y − w)| ≤ s for all y ∈ spt μ ∩ B_ρ(w) ('β-flat points'), and sing'(μ) := ((spt μ ∩ D μ) ∖ R(μ)) ∪ (ℝ^P ∖ D μ).
1. (Measurability of dens μ, any measure μ.) For ρ > 0, x ↦ μ(B_ρ(x)) is lower semicontinuous: if x_j → x then 1_{B_ρ(x)} ≤ liminf_j 1_{B_ρ(x_j)} pointwise, so μ(B_ρ(x)) ≤ liminf μ(B_ρ(x_j)) (Fatou). Hence g_ρ(x) := μ(B_ρ(x))/(ω_nρ^n) and G_m := sup_{0<ρ<1/(m+1)} g_ρ are lower semicontinuous (suprema of lsc functions), hence Borel. As the intervals (0, 1/(m+1)) form a basis of 𝓝[>]0 and G_m decreases in m, limsup_{ρ→0⁺} g_ρ(x) = inf_m G_m(x) (Filter.HasBasis.limsup_eq_iInf_iSup) is Borel, so dens μ is Borel measurable, and dens μ ≥ 0.
2. (Normalization.) For μ ∈ 𝓜, (M2) and Hⁿ = c•μH[n] give μ = c•(μH[n].withDensity(ofReal ∘ dens μ)). Hence (a) ∫⁻_A ofReal(dens μ) dμH[n] = c^{−1}μ(A) for Borel A; (b) for f ∈ C_c(ℝ^P), f·dens μ is μH[n]-integrable (by (a) on a ball containing tsupport f and (M1)) and ∫ f·dens μ dμH[n] = c^{−1}∫ f dμ (integral_withDensity_eq_integral_smul with the measurable ℝ≥0-valued density of step 1); (c) ∫ f·φ_μ dμH[n] = (c^{−1}∫ f dμ)•e₁ (integral_smul_const).
3. (Rescaling, any measure μ, y ∈ ℝ^P, t > 0.) μ^{y,t}(B_ρ(w)) = t^{−n}μ(B_{tρ}(y + tw)) (η_{y,t}^{−1}(B_ρ(w)) = B_{tρ}(y + tw), Measure.map_apply), so the density ratio of μ^{y,t} at (w, ρ) equals that of μ at (y + tw, tρ); since ρ ↦ tρ maps 𝓝[>]0 onto 𝓝[>]0, dens μ^{y,t}(w) = dens μ(y + tw), i.e. φ_{μ^{y,t}}(w) = φ_μ(y + tw); likewise spt μ^{y,t} = {w : y + tw ∈ spt μ}.
4. (The family.) F := {φ_μ : μ ∈ 𝓜} ⊆ (ℝ^P → Euclid 1). Injectivity: if φ_μ = φ_ν (μ, ν ∈ 𝓜) then dens μ = dens ν (e₁ ≠ 0), so μ = ν by (M2). Define sing(φ) := {w : ∃ μ ∈ 𝓜, φ = φ_μ ∧ w ∈ sing'(μ)}; by injectivity sing(φ_μ) = sing'(μ).
5. ((H0), (H1).) If φ_μ = φ_ν μH[n]-a.e., then dens μ = dens ν μH[n]-a.e., hence Hⁿ-a.e. (Hⁿ = c•μH[n]), so μ = ν by (M2) and withDensity_congr_ae, and φ_μ = φ_ν. φ_μ is measurable (step 1) and for every x, ∫_{B_1(x)} |φ_μ| dμH[n] = c^{−1}μ(B_1(x)) < ∞ (step 2(a), (M1) on closedBall x 1); so φ_μ is locally μH[n]-integrable.
6. (A.1.) For φ_μ ∈ F, 0 < λ < 1, |y| ≤ 1 − λ: φ_μ(y + λ·) = φ_{μ^{y,λ}} (step 3) and μ^{y,λ} ∈ 𝓜 (M3).
7. (A.2.) Let φ_μ ∈ F, |y| < 1, and λ_k > 0 strictly decreasing to 0. (M4) gives sub and ν ∈ 𝓜 with dens ν homogeneous and μ^{y,λ_{sub(k)}} → ν vaguely. For k ≥ k₀ (λ_{sub(k)} ≤ 1 − |y| and λ_{sub(k)} < 1), μ^{y,λ_{sub(k)}} ∈ 𝓜 by (M3), so by steps 3 and 2(c), for every f ∈ C_c: ∫ f(x)·φ_μ(y + λ_{sub(k)}x) dμH[n](x) = ∫ f·φ_{μ^{y,λ_{sub(k)}}} dμH[n] = (c^{−1}∫ f dμ^{y,λ_{sub(k)}})•e₁ → (c^{−1}∫ f dν)•e₁ = ∫ f·φ_ν dμH[n] (the finitely many k < k₀ do not affect the limit). ψ := φ_ν ∈ F, and ψ(tx) = ψ(x) for t > 0 by the homogeneity of dens ν.
8. (Support semicontinuity, parent (T3s).) If μ_k, μ ∈ 𝓜, μ_k → μ vaguely, y_k ∈ spt μ_k and y_k → y ∈ D μ, then y ∈ spt μ. Proof: D μ is open (M5), so closedBall y (3ρ₁) ⊆ D μ for some ρ₁ ∈ (0, 1]; by (M6) closedBall y (3ρ₁) ⊆ D μ_k for large k; also |y_k − y| < ρ₁ for large k, so closedBall y_k ρ ⊆ D μ_k for 0 < ρ ≤ ρ₁ and (M7) gives μ_k(B_ρ(y_k)) ≥ e^{−Λρ}ω_nρ^n. Let ε ∈ (0, ρ₁] and take f ∈ C_c with 0 ≤ f ≤ 1, f = 1 on closedBall y (ε/2) and tsupport f ⊆ B_ε(y). For large k, B_{ε/4}(y_k) ⊆ closedBall y (ε/2), so ∫ f dμ_k ≥ μ_k(B_{ε/4}(y_k)) ≥ e^{−Λε/4}ω_n(ε/4)^n. Hence μ(B_ε(y)) ≥ ∫ f dμ = lim ∫ f dμ_k ≥ e^{−Λε/4}ω_n(ε/4)^n > 0 (ω_n > 0); larger ε follow by monotonicity.
9. (A.3, closedness.) spt μ is closed (if μ(B_ε(w)) = 0 then μ(B_{ε/2}(w')) = 0 for w' ∈ B_{ε/2}(w)). R(μ) is relatively open in spt μ: if (ρ, Q, s) witnesses w ∈ R(μ) (s ≥ |q_Q(w − w)| = 0, as w ∈ spt μ ∩ B_ρ(w)), w' ∈ spt μ and t := |w' − w| satisfies (1 + β)t < βρ − s, then (ρ − t, Q, s + t) witnesses w' ∈ R(μ): ρ − t > 0, B_{ρ−t}(w') ⊆ B_ρ(w) ⊆ D μ, and for y ∈ spt μ ∩ B_{ρ−t}(w'), |q_Q(y − w')| ≤ |q_Q(y − w)| + |q_Q(w − w')| ≤ s + t < β(ρ − t). Hence sing'(μ) is closed: if w ∉ sing'(μ) then w ∈ D μ (open) and either w ∉ spt μ — then some ball around w lies in D μ and misses the closed set spt μ, hence misses sing'(μ) — or w ∈ R(μ) — then some ball B around w lies in D μ with B ∩ spt μ ⊆ R(μ), and no point of B is in sing'(μ).
10. (A.3(1).) Let φ_μ = 1_L·c' with dim L = n and c' ∈ Euclid 1. Then dens μ(x) = 0 for x ∉ L and dens μ(x) = a (the coordinate of c') for x ∈ L; in particular dens μ(tx) = dens μ(x) for t > 0 (tx ∈ L ⟺ x ∈ L), so D μ = ℝ^P by (M9). For w ∉ L there is ε > 0 with B_ε(w) ∩ L = ∅ (L is closed), and by (M2) μ(B_ε(w)) = ∫_{B_ε(w)} ofReal(dens μ) dHⁿ = 0; so spt μ ⊆ L. Every w ∈ spt μ lies in R(μ) with (ρ, Q, s) = (1, L, 0): B_1(w) ⊆ ℝ^P = D μ, and for y ∈ spt μ, y − w ∈ L, so q_L(y − w) = 0 and 0 < β. Hence sing(φ_μ) = sing'(μ) = ∅.
11. (A.3(2).) Let φ_μ ∈ F, 0 < λ < 1, |y| ≤ 1 − λ, μ' := μ^{y,λ} ∈ 𝓜 (M3) and g(w) := y + λw. Then φ_μ∘g = φ_{μ'} and spt μ' = g^{−1}(spt μ) (step 3), D μ' = η_{y,λ}(D μ) = g^{−1}(D μ) (M3; η_{y,λ} = g^{−1}), and R(μ') = g^{−1}(R(μ)): (ρ, Q, s) witnesses w ∈ R(μ') iff (λρ, Q, λs) witnesses g(w) ∈ R(μ), since g maps B_ρ(w) onto B_{λρ}(g(w)) and spt μ' ∩ B_ρ(w) onto spt μ ∩ B_{λρ}(g(w)), and q_Q(g(y) − g(w)) = λq_Q(y − w). Hence sing(φ_μ∘g) = sing'(μ') = g^{−1}(sing'(μ)) = g^{−1}(sing φ_μ).
12. (A.3(3).) Let μ, μ_k ∈ 𝓜 with ∫ f·φ_{μ_k} dμH[n] → ∫ f·φ_μ dμH[n] for every f ∈ C_c; by step 2(c) (c ≠ 0, e₁ ≠ 0), μ_k → μ vaguely. Let ε > 0 and suppose that for infinitely many k there is w_k ∈ B_1(0) ∩ sing'(μ_k) with |w_k − z'| ≥ ε for every z' ∈ sing'(μ). Pass to a subsequence along which this holds for every k and w_k → w, |w| ≤ 1 (vague convergence is kept). As B_2(0) ⊆ D μ_k (M5), w_k ∈ spt μ_k ∖ R(μ_k). As closedBall 0 1 ⊆ D μ (M5), step 8 gives w ∈ spt μ; |w − z'| ≥ ε for all z' ∈ sing'(μ), so w ∉ sing'(μ), and hence w ∈ R(μ), witnessed by (ρ, Q, s) with s < βρ. Choose ρ' ∈ (0, ρ) with s < βρ', put τ := (s + βρ')/2 ∈ (s, βρ') and choose η ∈ (0, (ρ − ρ')/2). For large k, |w_k − w| < η, and as closedBall w (ρ' + η) ⊆ B_ρ(w) ⊆ D μ is compact, (M6) gives B_{ρ'}(w_k) ⊆ closedBall w (ρ' + η) ⊆ D μ_k. Claim: for large k, |q_Q(y − w_k)| ≤ τ for every y ∈ spt μ_k ∩ B_{ρ'}(w_k). Otherwise, along a further subsequence there are y_k ∈ spt μ_k ∩ B_{ρ'}(w_k) with |q_Q(y_k − w_k)| > τ; a further subsequence has y_k → y' with |y' − w| ≤ ρ' < ρ, so y' ∈ D μ, step 8 gives y' ∈ spt μ ∩ B_ρ(w), and |q_Q(y' − w)| = lim|q_Q(y_k − w_k)| ≥ τ > s, contradicting the choice of (ρ, Q, s). Hence for large k, (ρ', Q, τ) witnesses w_k ∈ R(μ_k) (τ < βρ'), a contradiction. So there is k₀ with B_1(0) ∩ sing(φ_{μ_k}) ⊆ {x : ∃ z' ∈ sing(φ_μ), |x − z'| < ε} for all k ≥ k₀.
13. (Appendix A.4.) By steps 4–12, abstract_dimension_reduction applies to (P, n, Q := 1, F, sing). Hence either (I) B_1(0) ∩ sing'(μ) = ∅ for every μ ∈ 𝓜, or (II) there is d ∈ ℕ with d + 1 ≤ n such that μH[d + α](sing'(μ) ∩ B_1(0)) = 0 for every μ ∈ 𝓜 and α > 0, and there are ν ∈ 𝓜 and a d-dimensional subspace L with sing'(ν) = L and φ_ν(y + tx) = φ_ν(x) for y ∈ L, t > 0 and all x.
14. (Exclusion of d = n − 1.) Suppose (II) holds with d + 1 = n. Then dens ν(y + tx) = dens ν(x) for y ∈ L, t > 0 (e₁ ≠ 0); in particular (y = 0) dens ν is homogeneous, so D ν = ℝ^P by (M9), and (M8) gives an n-dimensional Q with spt ν ⊆ Q. Every w ∈ spt ν lies in R(ν) with (1, Q, 0) (y − w ∈ Q for y, w ∈ Q), so sing'(ν) = ((spt ν ∩ ℝ^P) ∖ R(ν)) ∪ ∅ = ∅ ≠ L (0 ∈ L): a contradiction. Hence in case (II), d + 2 ≤ n.
15. (Conclusion.) Fix μ ∈ 𝓜 and put Z := sing'(μ) ∩ B_1(0). In case (I), Z = ∅, so μH[s](Z) = 0 for every s. In case (II), d + 2 ≤ n, so n ≥ 2 and, for α > 0, n − 2 + α = d + α' with α' := n − 2 − d + α > 0, whence μH[n − 2 + α](Z) = 0. If n = 1, case (II) is impossible (d + 2 ≤ 1 fails), so Z = ∅. Finally let w ∈ B_1(0) ∩ spt μ with w ∉ Z. Then w ∉ sing'(μ), and as w ∈ B_1(0) ⊆ D μ (M5), w ∈ R(μ): there are ρ > 0 with B_ρ(w) ⊆ D μ, an n-dimensional Q and s < βρ with |(y − w) − p_Q(y − w)| = |q_Q(y − w)| ≤ s for all y ∈ spt μ ∩ B_ρ(w). ∎

## Key steps

1. Density functions φ_μ = dens μ·e₁: Borel (lsc suprema), normalized by μHE[n] = c·μH[n], so weak convergence of φ's is vague convergence of μ's; (H0), (H1), A.1, A.2 from (M1)–(M4).
2. β-flat points R(μ) inside the domain D μ; sing'(μ) = ((spt μ ∩ D μ) ∖ R(μ)) ∪ D μᶜ is closed, empty for planes (M9), and dilation-equivariant (M3).
3. Support semicontinuity from (M6), (M7) and vague convergence gives A.3(3).
4. Appendix A.4; an (n−1)-dimensional extremal would be planar by (M8), (M9), so its sing is empty — contradiction; hence d ≤ n − 2 and the non-flat set is μH[n−2+α]-null (empty for n = 1).

## Reference use

### local-project

Queries:
- `python3 -I -c json.load(/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json); cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD`
- `python3 scan of dag.json: status, candidate_commit, depends_on and children of root.dimension_reduction_results-a1.{monotonicity,moving_blowups,cone_splitting,one_dim_cones}-a1, root.density_and_tangent_cones-a1, root.minimizing_implies_stationary-a1, root.compactness_of_minimizing_currents-a1 (three levels)`
- `grep -n '_dependency_problem|_existing_lean_name_problem|_overlay_accepted_children|def _accepted_checkpoint' /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py (lines 3159–3196, 2364–2368, 6512–6575)`
- `grep -l 'not inherited|dependency gap|unregistered|not registered' nodes/*/decomposition-audit-v*.json (precedents: density-gap-a1 audits v2–v8, threshold-reduction-a1 audit v4)`
- `python3 extraction of subproblem.natural_proof, lean_statement and proof_key_steps from the parent-child-handoff.json of the five unaccepted originals and of root.density_and_tangent_cones-a1.blowup_scaling-a1`
- `grep -c <name> dag.json; grep -rl <name> nodes (outside this node's own unactivated attempt-1 files); grep -rl <name> ../.swarm-worktrees/*/gmt-ch07/GMT for the eight fresh idtp_fons_ names (all zero)`
- `grep -n 'theorem GeometricCurrentOn.boundary_affinePushforward|restrictDomain_apply|def GeometricCurrentOn.zeroRegion|def GeometricCurrentOn.support' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/*.lean`
- `grep -rn 'euclideanHausdorffMeasure_smul₀|ext_of_generateFrom_of_iUnion|isPiSystem_isOpen|def borel|withDensity_congr_ae|withDensity_indicator|Filter.Tendsto.limsup_eq|theorem ofReal_toReal|hausdorffMeasure_image_le|measure_biUnion_null_iff|addHaarScalarFactor_volume_hausdorffMeasure_ne_zero' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `lake env lean /tmp/fons_v2/check/Types.lean; lake env lean /tmp/fons_v2/check/Assembly.lean; lake env lean /tmp/fons_v2/check/AssemblyAx.lean (Lean v4.35.0-rc3 toolchain of the run)`
- `python3 replay of Runtime._topological, Runtime._dependency_problem and Runtime._existing_lean_name_problem on /tmp/fons_v2/subs.json against dag.json (updated_at 2026-10-13T10:29:45Z)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-4fcbfb5d62/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-4fcbfb5d62/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-4fcbfb5d62/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-monotonicity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-monotonicity-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-one-dim-cones-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-scaling-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-scaling-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-im-mass-measure-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-cone-measure-homogeneous-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-density-gap-a1/decomposition-v8.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-density-gap-a1/decomposition-audit-v6.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/operator-dependency-edits/20261013T091722Z-revert/receipt.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/tmp/fons_v2/check/Types.lean`
- `/tmp/fons_v2/check/Assembly.lean`
- `/tmp/fons_v2/check/AssemblyAx.lean`

Pins match: the snapshot manifest records project b4d606d (workspace HEAD) and Mathlib 25730c7c; SimonGMT is 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. Dependency status (dag.json 11:00Z): dimred_minimizing_monotonicity rlcr-lean, dimred_blowup_limit_moving_centres, density_and_tangent_cones, dimred_invariant_cone_splitting, dimred_one_dim_minimizing_cone and minimizing_implies_stationary speculative-ready — none accepted, all owned by other parents, so runtime.py (_existing_lean_name_problem; _accepted_checkpoint requires accepted/integrating/merged with a candidate commit, or proved) forbids reusing them here, and _overlay_accepted_children overlays only this node's children and depends_on (the handoff registers weak_limit_mass_bound and density_eq_multiplicity_ae only; the operator's dependency edit on the monotonicity node was reverted because the dependency was not in the frozen handoff). The accepted precedent for this situation is density-gap-a1 (audit v6 accepted fresh-named duplicates of unaccepted cross-branch theorems). Hence the split registers fresh-named obligations with types byte-identical to monotonicity, density_and_tangent_cones, cone_splitting, one_dim_cones and minimizing_implies_stationary, whose proofs are their handoff proofs with re-targeted sibling references, and removes moving_blowups and weak_limit_mass_bound altogether. Reused: abstract_dimension_reduction (9ab8e5d6), dimred_im_mass_measure (01ae2c59), dtc_blowUp_scaling (a94d596c), cone_current_imrep_measure_smul_image (e183b985), all accepted with isolated-comparator passes and identical types. Library: SimonGMT supplies GeometricCurrentOn.boundary_affinePushforward (AffineCurrentPushforward.lean:188), restrictDomain_apply and support = U ∖ zeroRegion (CurrentLocalEquality.lean); the snapshot Mathlib supplies euclideanHausdorffMeasure_smul₀ and addHaarScalarFactor_volume_hausdorffMeasure_ne_zero (Geometry/Euclidean/Volume/Measure.lean), ext_of_generateFrom_of_iUnion (Measure/Restrict.lean:491), isPiSystem_isOpen and def borel = generateFrom {IsOpen} (BorelSpace/Basic.lean), withDensity_congr_ae and withDensity_indicator (WithDensity.lean), Filter.Tendsto.limsup_eq (Topology/Order/LiminfLimsup.lean:190), ENNReal.ofReal_toReal (Basic/ENNReal/Basic.lean:248), LipschitzWith.hausdorffMeasure_image_le (Hausdorff.lean:745), measure_biUnion_null_iff and exists_countable_dense. No library or accepted declaration provides Federer–Fleming compactness, Simon 7.1.2, 7.3.1 or Lemma 7.3.5 for the contract's currents; these enter only as the registered obligations. Lean: all 12 types elaborate; the parent assembly compiles from the 12 children and the registered dependency only, and the axiom-stub variant shows it uses exactly 7 children plus idtp_imrep_measure_density_ae; no fresh name is reserved anywhere.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
