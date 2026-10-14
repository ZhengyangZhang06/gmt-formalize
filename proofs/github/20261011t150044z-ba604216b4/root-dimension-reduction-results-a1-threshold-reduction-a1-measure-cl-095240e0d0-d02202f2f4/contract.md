<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.threshold_reduction-a1.measure_class_reduction-a1 -->

## Theorem `Submission.dimred_tr_measure_class_reduction`

Assume (ADR): the abstract dimension reduction theorem (Simon Appendix A.4 with (H0)), in exactly the form of the frozen Lean type of Submission.abstract_dimension_reduction. That is: for all P′, n′, Q′ ∈ ℕ, every set F of functions ℝ^{P′} → ℝ^{Q′} and every map sing satisfying (H0), local μH[n′]-integrability, A.1, A.2 and A.3 (closedness, emptiness for flat indicators of n′-planes, rescaling, and the ε-neighbourhood semicontinuity), either (I) B_1(0) ∩ sing φ = ∅ for all φ ∈ F, or (II) there is d with d + 1 ≤ n′ such that μH[d + α](sing φ ∩ B_1(0)) = 0 for all φ ∈ F and α > 0, some ψ ∈ F and a d-dimensional subspace L have sing ψ = L and ψ(y + λx) = ψ(x) for y ∈ L and λ > 0, and, if d = 0, sing φ ∩ B_σ(0) is finite for all φ ∈ F and σ < 1. Under (ADR): Let P, n ∈ ℕ with n ≥ 1, c > 0, Λ ∈ ℝ, and let 𝓜 be a set of Borel measures on ℝ^P. For a measure μ and x ∈ ℝ^P let dens μ x := (limsup_{ρ↓0} μ(B_ρ(x))/(ω_nρⁿ)).toReal (limsup in [0, ∞], ω_n = unitBallVolume n; toReal sends ∞ to 0). For y ∈ ℝ^P and λ > 0 put μ^{y,λ} := ofReal(λ⁻¹ⁿ) • μ.map (dilation y λ) (= λ^{−n}(η_{y,λ})_#μ). Assume: (1) every μ ∈ 𝓜 is finite on compact sets; (2) every μ ∈ 𝓜 equals Hⁿ.withDensity (ofReal ∘ dens μ), Hⁿ = μHE[n]; (3) μ^{y,λ} ∈ 𝓜 whenever μ ∈ 𝓜, 0 < λ < 1 and |y| ≤ 1 − λ; (4) for μ ∈ 𝓜, |y| < 1 and every strictly decreasing sequence λ_j > 0 with λ_j → 0, there are a strictly increasing sub : ℕ → ℕ and ν ∈ 𝓜 with ν(λ·s) = λⁿν(s) for all λ > 0 and Borel s, and ∫ f dμ^{y,λ_{sub(j)}} → ∫ f dν for every continuous compactly supported f : ℝ^P → ℝ; (5) for μ ∈ 𝓜 and y, R with B̄_R(y) ⊆ B̄_2(0), ρ ↦ ofReal(e^{Λρ}/ρⁿ)·μ(B_ρ(y)) is nondecreasing on (0, R); (6) there is no μ ∈ 𝓜 with μ(ℝ^P) = ∞ and dens μ = c′·1_Q (pointwise) for some n-dimensional linear subspace Q and some real c′ ≥ c. Then either (I) for every μ ∈ 𝓜 the set {x ∈ B_1(0) : c ≤ dens μ x} is empty; or (II) there is d ∈ ℕ with d + 1 ≤ n such that μH[d + α]({x ∈ B_1(0) : c ≤ dens μ x}) = 0 for all μ ∈ 𝓜 and real α > 0; if d = 0, {x ∈ B_σ(0) : c ≤ dens μ x} is finite for all μ ∈ 𝓜 and σ < 1; and there are ν ∈ 𝓜 with ν(ℝ^P) = ∞ and a linear subspace L with dim L = d, {x : c ≤ dens ν x} = L and dens ν (y + λx) = dens ν x for all y ∈ L, λ > 0 and x. (In the Lean statement dens is a universally quantified function fixed by its defining equation.)

Node: `root.dimension_reduction_results-a1.threshold_reduction-a1.measure_class_reduction-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1030

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6948, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6963, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7551, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6976, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7682, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5266, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8612, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8613, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8615

## Lean problem

Declaration: `Submission.dimred_tr_measure_class_reduction`

```lean
(∀ (P n Q : ℕ) (F : Set (Euclid P → Euclid Q)) (sing : (Euclid P → Euclid Q) → Set (Euclid P)), (∀ φ ∈ F, ∀ ψ ∈ F, (∀ᵐ x ∂μH[(n : ℝ)], φ x = ψ x) → φ = ψ) → (∀ φ ∈ F, LocallyIntegrable φ μH[(n : ℝ)]) → (∀ φ ∈ F, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → (fun x => φ (y + lam • x)) ∈ F) → (∀ φ ∈ F, ∀ y : Euclid P, ‖y‖ < 1 → ∀ lams : ℕ → ℝ, (∀ k, 0 < lams k) → StrictAnti lams → Tendsto lams atTop (𝓝 0) → ∃ (sub : ℕ → ℕ) (ψ : Euclid P → Euclid Q), StrictMono sub ∧ ψ ∈ F ∧ (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φ (y + lams (sub k) • x) ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • ψ x ∂μH[(n : ℝ)]))) ∧ ∀ lam : ℝ, 0 < lam → ∀ x, ψ (lam • x) = ψ x) → (∀ φ ∈ F, IsClosed (sing φ)) → (∀ φ ∈ F, ∀ (L : Submodule ℝ (Euclid P)) (c : Euclid Q), Module.finrank ℝ L = n → φ = Set.indicator (L : Set (Euclid P)) (fun _ => c) → sing φ = ∅) → (∀ φ ∈ F, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → sing (fun x => φ (y + lam • x)) = (fun x => y + lam • x) ⁻¹' sing φ) → (∀ φ ∈ F, ∀ φs : ℕ → Euclid P → Euclid Q, (∀ k, φs k ∈ F) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φs k x ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • φ x ∂μH[(n : ℝ)]))) → ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ball (0 : Euclid P) 1 ∩ sing (φs k) ⊆ {x | ∃ z ∈ sing φ, dist x z < ε}) → (∀ φ ∈ F, ball (0 : Euclid P) 1 ∩ sing φ = ∅) ∨ ∃ d : ℕ, d + 1 ≤ n ∧ (∀ φ ∈ F, ∀ α : ℝ, 0 < α → μH[(d : ℝ) + α] (sing φ ∩ ball (0 : Euclid P) 1) = 0) ∧ (∃ ψ ∈ F, ∃ L : Submodule ℝ (Euclid P), Module.finrank ℝ L = d ∧ sing ψ = (L : Set (Euclid P)) ∧ ∀ y ∈ L, ∀ lam : ℝ, 0 < lam → ∀ x, ψ (y + lam • x) = ψ x) ∧ (d = 0 → ∀ φ ∈ F, ∀ σ : ℝ, σ < 1 → (sing φ ∩ ball (0 : Euclid P) σ).Finite)) → ∀ (P n : ℕ) (c Λ : ℝ) (𝓜 : Set (Measure (Euclid P))) (dens : Measure (Euclid P) → Euclid P → ℝ), 1 ≤ n → 0 < c → (∀ (μ : Measure (Euclid P)) (x : Euclid P), dens μ x = (limsup (fun ρ : ℝ => μ (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0)).toReal) → (∀ μ ∈ 𝓜, ∀ K : Set (Euclid P), IsCompact K → μ K ≠ ∞) → (∀ μ ∈ 𝓜, μ = (μHE[n] : Measure (Euclid P)).withDensity (fun x => ENNReal.ofReal (dens μ x))) → (∀ μ ∈ 𝓜, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → ENNReal.ofReal (lam⁻¹ ^ n) • μ.map (dilation y lam) ∈ 𝓜) → (∀ μ ∈ 𝓜, ∀ y : Euclid P, ‖y‖ < 1 → ∀ lams : ℕ → ℝ, (∀ j, 0 < lams j) → StrictAnti lams → Tendsto lams atTop (𝓝 0) → ∃ (sub : ℕ → ℕ) (ν : Measure (Euclid P)), StrictMono sub ∧ ν ∈ 𝓜 ∧ (∀ lam : ℝ, 0 < lam → ∀ s : Set (Euclid P), MeasurableSet s → ν ((fun x => lam • x) '' s) = ENNReal.ofReal (lam ^ n) * ν s) ∧ ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun j => ∫ x, f x ∂(ENNReal.ofReal ((lams (sub j))⁻¹ ^ n) • μ.map (dilation y (lams (sub j))))) atTop (𝓝 (∫ x, f x ∂ν))) → (∀ μ ∈ 𝓜, ∀ (y : Euclid P) (R : ℝ), closedBall y R ⊆ closedBall 0 2 → MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ n) * μ (ball y ρ)) (Ioo 0 R)) → (∀ μ ∈ 𝓜, μ univ = ∞ → ∀ (Q : Submodule ℝ (Euclid P)) (c' : ℝ), Module.finrank ℝ Q = n → c ≤ c' → (∀ x, dens μ x = Set.indicator (Q : Set (Euclid P)) (fun _ => c') x) → False) → (∀ μ ∈ 𝓜, {x | x ∈ ball (0 : Euclid P) 1 ∧ c ≤ dens μ x} = ∅) ∨ ∃ d : ℕ, d + 1 ≤ n ∧ (∀ μ ∈ 𝓜, ∀ α : ℝ, 0 < α → μH[(d : ℝ) + α] {x | x ∈ ball (0 : Euclid P) 1 ∧ c ≤ dens μ x} = 0) ∧ (d = 0 → ∀ μ ∈ 𝓜, ∀ σ : ℝ, σ < 1 → {x | x ∈ ball (0 : Euclid P) σ ∧ c ≤ dens μ x}.Finite) ∧ ∃ ν ∈ 𝓜, ν univ = ∞ ∧ ∃ L : Submodule ℝ (Euclid P), Module.finrank ℝ L = d ∧ {x | c ≤ dens ν x} = (L : Set (Euclid P)) ∧ ∀ y ∈ L, ∀ lam : ℝ, 0 < lam → ∀ x, dens ν (y + lam • x) = dens ν x
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
- Child DAG node: `root.dimension_reduction_results-a1.threshold_reduction-a1.measure_class_reduction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, steps 3(iv)–(vii), 4, 5, 6 and the measure-theoretic part of step 7, applied to the class of mass measures 𝓜 = {μ_S : (S, U_S) ∈ 𝒯}, with F := {φ_μ : μ ∈ 𝓜}, φ_μ := dens μ·e₁ and the threshold map sing φ := closure{⟨φ, e₁⟩ ≥ c} (departure [D1] of the parent). The semicontinuity statement of parent step 4 is proved first, as Lemma D in Step 0. The leading hypothesis (ADR) of the statement is, verbatim, the frozen Lean type of Submission.abstract_dimension_reduction (Appendix A.4 with (H0), DAG node root.abstract_dimension_reduction-a1). It is used only in step 8, exactly where the parent proof (step 6) cites that node. No other result outside the sibling set is used, and every library fact cited below is reachable from the frozen header.

Step 0 (Lemma D; formerly the separate sibling density_usc_vague of attempt 4, merged here because this child is its only user). Within this step the letters below denote the objects of Lemma D only.
Lemma D (parent step 4, for measures). Let P, n ∈ ℕ, Λ ∈ ℝ, and let μ_j (j ∈ ℕ) and μ be Borel measures on ℝ^P, each finite on compact sets, with ∫ f dμ_j → ∫ f dμ for every continuous compactly supported f : ℝ^P → ℝ. Assume that for every j, every y ∈ ℝ^P and every R with B̄_R(y) ⊆ B̄_2(0), the function ρ ↦ ofReal(e^{Λρ}/ρⁿ)·μ_j(B_ρ(y)) is nondecreasing on (0, R). Let w_j → w in ℝ^P with |w| < 2, and let θ_j, θ, c ∈ ℝ with θ ≥ 0, μ_j(B_ρ(w_j))/(ω_nρⁿ) → ofReal(θ_j) and μ(B_ρ(w))/(ω_nρⁿ) → ofReal(θ) as ρ ↓ 0 (ω_n = unitBallVolume n, in [0, ∞]), and c ≤ θ_j for every j. Then c ≤ θ.
Proof of Lemma D.
Source: parent proof, step 4 ("Semicontinuity along members"): Θ_S(w) ≥ limsup_k Θ_{S_k}(w_k), via the monotonicity bound at w_k, inclusion of balls, upper semicontinuity of vague limits on compact sets, then η ↓ 0 and ρ ↓ 0. It is stated here for measures, with only what the argument uses.
D1. (Radii.) Put R₀ := (2 − |w|)/2 > 0 and choose j₁ with |w_j − w| < R₀/2 for j ≥ j₁. For such j, B̄_{R₀/2}(w_j) ⊆ B̄_2(0), since |w_j| + R₀/2 < |w| + R₀ < 2. So the monotonicity hypothesis applies at centre w_j on (0, R₀/2).
D2. (Lower bound for μ_j.) Fix j ≥ j₁ and set g_j(ρ) := ofReal(e^{Λρ}/ρⁿ)·μ_j(B_ρ(w_j)) for ρ > 0. Then g_j(ρ) = ofReal(e^{Λρ})·ω_n·[μ_j(B_ρ(w_j))/(ω_nρⁿ)], with ω_n ∈ (0, ∞). As ρ ↓ 0, ofReal(e^{Λρ}) → 1, so g_j(ρ) → ω_n·ofReal(θ_j). Since g_j is nondecreasing on (0, R₀/2), for every ρ in that interval ω_n·ofReal(θ_j) = lim_{t↓0} g_j(t) ≤ g_j(ρ). As ofReal(c) ≤ ofReal(θ_j), we get μ_j(B_ρ(w_j)) ≥ ofReal(c)·ω_n·ofReal(ρⁿe^{−Λρ}) for all j ≥ j₁ and ρ ∈ (0, R₀/2).
D3. (Passing to μ.) Fix ρ ∈ (0, R₀/2) and η > 0. For large j, |w_j − w| ≤ η, so B_ρ(w_j) ⊆ K := B̄_{ρ+η}(w), which is compact.
Claim: limsup_j μ_j(K) ≤ μ(K). For ε > 0 let K_ε := {p : dist(p, K) ≤ ε} (compact) and f_ε(p) := max(0, 1 − dist(p, K)/ε). Then f_ε is continuous with compact support and 1_K ≤ f_ε ≤ 1_{K_ε}. Since μ_j is finite on compact sets, f_ε is μ_j-integrable and μ_j(K) ≤ ∫ f_ε dμ_j → ∫ f_ε dμ ≤ μ(K_ε). Finally μ(K_ε) ↓ μ(K) as ε ↓ 0, because K = ⋂_ε K_ε and μ(K_1) < ∞.
By the claim and step D2, μ(B̄_{ρ+η}(w)) ≥ ofReal(c)·ω_n·ofReal(ρⁿe^{−Λρ}) for every η > 0. Letting η ↓ 0 (μ is finite on B̄_{ρ+1}(w) and B̄_ρ(w) = ⋂_η B̄_{ρ+η}(w)) gives μ(B̄_ρ(w)) ≥ ofReal(c)·ω_n·ofReal(ρⁿe^{−Λρ}).
D4. (Back to open balls.) For t ∈ (0, R₀/2) and ε > 0 put ρ := t/(1 + ε) < t. Then μ(B_t(w)) ≥ μ(B̄_ρ(w)) ≥ ofReal(c)·ω_n·ofReal(tⁿ(1 + ε)^{−n}e^{−Λρ}). Since |Λρ| ≤ |Λ|t, this gives μ(B_t(w))/(ω_ntⁿ) ≥ ofReal(c)·ofReal((1 + ε)^{−n}e^{−|Λ|t}). If c ≤ 0 the bound is trivial. Letting t ↓ 0 gives ofReal(θ) ≥ ofReal(c)·ofReal((1 + ε)^{−n}), and letting ε ↓ 0 gives ofReal(θ) ≥ ofReal(c).
D5. (Conclusion.) If c ≤ 0, then c ≤ 0 ≤ θ. If c > 0, then ofReal(θ) ≥ ofReal(c) = c > 0, so θ > 0 and θ = (ofReal θ).toReal ≥ c. ∎

Main argument.
Notation: Hⁿ := μHE[n]. c_n := addHaarScalarFactor(volume, μH[n]) ∈ ℝ≥0, with Hⁿ = c_n·μH[n] (euclideanHausdorffMeasure_def) and c_n ≠ 0 (addHaarScalarFactor_volume_hausdorffMeasure_ne_zero). So μH[n] and Hⁿ have the same null sets, and ∫ g dμH[n] = c_n⁻¹∫ g dHⁿ. q(μ, x, ρ) := μ(B_ρ(x))/(ω_nρⁿ) ∈ [0, ∞], so dens μ x = (limsup_{ρ↓0} q(μ, x, ρ)).toReal ≥ 0. e := EuclideanSpace.single 0 1 ∈ Euclid 1, so ⟨v, e⟩ = v 0 and e 0 = 1. φ_μ(x) := dens μ x • e. F := {φ_μ : μ ∈ 𝓜}. For φ : ℝ^P → Euclid 1, sing φ := closure{x : c ≤ φ(x) 0}. Note c ≤ φ_μ(x) 0 iff c ≤ dens μ x.
1. (Measurability; parent 3(ii).) Let μ be any Borel measure. For fixed ρ > 0, x ↦ μ(B_ρ(x)) is lower semicontinuous: if x_j → x then B_ρ(x) ⊆ ⋃_m ⋂_{j≥m} B_ρ(x_j), so μ(B_ρ(x)) ≤ liminf_j μ(B_ρ(x_j)) by continuity from below. Equivalently, in filter form: if y < μ(B_ρ(x)), pick r < ρ with y < μ(B_r(x)); then B_r(x) ⊆ B_ρ(x′) whenever |x′ − x| < ρ − r. For fixed x, ρ ↦ q(μ, x, ρ) is left-continuous on (0, ∞): B_ρ(x) = ⋃_{ρ′<ρ} B_{ρ′}(x), and ρⁿ is continuous and positive. Hence limsup_{ρ↓0} q(μ, x, ρ) = inf_{δ ∈ ℚ_{>0}} sup_{ρ ∈ ℚ∩(0,δ)} q(μ, x, ρ), a countable infimum of countable suprema of Borel functions of x. So dens μ is Borel. Here "left-continuous" is used through the following elementary fact, proved the same way as for right-continuity: if g : (0, δ) → [0, ∞] is left-continuous at every ρ ∈ (0, δ), then sup_{(0,δ)} g = sup_{ℚ∩(0,δ)} g, because each ρ ∈ (0, δ) is the limit of rationals q_m ↑ ρ with q_m ∈ (0, ρ), so g(ρ) = lim g(q_m) ≤ sup_{ℚ∩(0,δ)} g. Lower semicontinuous functions are Borel (LowerSemicontinuous.measurable), and countable infima and suprema of measurable [0, ∞]-valued functions are measurable; toReal is measurable. (Both facts are proved directly here. SimonGMT's Chapter01/Densities.lean is not imported by the frozen header, and its lemma iSup_rat_Ioo_eq_of_tendsto_right assumes right-continuity in the radius, which fails for open balls, e.g. for a Dirac mass at distance 1 from x.)
2. (Rescaling identity; parent 3(vi).) For any measure μ, y ∈ ℝ^P and λ > 0, dilation y λ ⁻¹' B_ρ(x) = B_{λρ}(y + λx). So μ^{y,λ}(B_ρ(x)) = ofReal(λ^{−n})μ(B_{λρ}(y + λx)) and q(μ^{y,λ}, x, ρ) = q(μ, y + λx, λρ). The map ρ ↦ λρ sends 𝓝[>]0 onto 𝓝[>]0 (Filter.map of 𝓝[>]0 under multiplication by λ > 0 is 𝓝[>]0, a small lemma), so the limsups coincide: dens μ^{y,λ} x = dens μ (y + λx), i.e. φ_{μ^{y,λ}} = φ_μ(y + λ·).
3. (Homogeneity; parent 3(vii).) If ν(λ·s) = λⁿν(s) for all λ > 0 and Borel s, then ν(B_ρ(λx)) = ν(λ·B_{ρ/λ}(x)) = λⁿν(B_{ρ/λ}(x)). So q(ν, λx, ρ) = q(ν, x, ρ/λ), and dens ν (λx) = dens ν x.
4. (Normalized pairings; parent 3(iv),(v).) Let μ ∈ 𝓜 and f be continuous with compact support. By (2), μ = Hⁿ.withDensity(ofReal∘dens μ) = (c_n • μH[n]).withDensity(ofReal∘dens μ), with dens μ Borel (step 1) and finite, and c_n ∈ ℝ≥0. By integral_withDensity_eq_integral_toReal_smul over the measure c_n • μH[n], then integral_smul_nnreal_measure, ∫ f dμ = c_n∫ dens μ·f dμH[n]. This route compiles; withDensity_smul_measure would need an ℝ≥0∞ scalar. Therefore ∫ f(x)•φ_μ(x) dμH[n](x) = (∫ f·dens μ dμH[n])•e = c_n⁻¹(∫ f dμ)•e. This identity needs no integrability hypothesis: it holds for every f : ℝ^P → ℝ (integral_withDensity_eq_integral_toReal_smul, integral_smul_nnreal_measure and integral_smul_const are unconditional, non-integrable integrands having Bochner integral 0 on both sides), so the uses in (A.2) and (A.3)(3) below carry no side conditions. Likewise ∫_K dens μ dμH[n] = c_n⁻¹μ(K) < ∞ for compact K, by (1).
5. (Densities exist on B_2(0).) Let μ ∈ 𝓜 and |x| < 2, and put R := 2 − |x|, so B̄_R(x) ⊆ B̄_2(0). By (5), g(ρ) := ofReal(e^{Λρ}/ρⁿ)μ(B_ρ(x)) is nondecreasing on (0, R), and it is finite by (1). Hence g(ρ) → L := inf_{(0,R)} g < ∞ as ρ ↓ 0 (MonotoneOn.tendsto_nhdsWithin_Ioo_right), and q(μ, x, ρ) = ofReal(e^{−Λρ})·g(ρ)/ω_n → L/ω_n. So the limsup is a finite limit, and q(μ, x, ρ) → ofReal(dens μ x).
6. (Upper semicontinuity on B_2(0); parent 5(γ).) Let μ ∈ 𝓜, x ∈ B_2(0), and x_j → x with c ≤ dens μ x_j for all j; passing to a tail, x_j ∈ B_2(0). Apply Lemma D (Step 0) with μ_j := μ (constant sequence, so vague convergence is trivial), w_j := x_j, w := x, θ_j := dens μ x_j, θ := dens μ x ≥ 0. Its hypotheses hold by (1), (5) and step 5. So c ≤ dens μ x. Consequently, for μ ∈ 𝓜, sing φ_μ ∩ B_2(0) ⊆ {x : c ≤ dens μ x}, since a point of the closure lying in the open set B_2(0) is a limit of such x_j.
7. (Hypotheses of (ADR) for (P, n, Q := 1, F, sing).)
(H0) Let μ, ν ∈ 𝓜 with φ_μ = φ_ν μH[n]-a.e. Taking coordinate 0, dens μ = dens ν μH[n]-a.e., hence Hⁿ-a.e. By (2) and withDensity_congr_ae, μ = Hⁿ.withDensity(ofReal∘dens μ) = Hⁿ.withDensity(ofReal∘dens ν) = ν. Hence dens μ = dens ν everywhere and φ_μ = φ_ν.
(Loc), the second hypothesis of (ADR), local integrability; not the parent's (H1). φ_μ is Borel (step 1) and ∫_K ‖φ_μ‖ dμH[n] = ∫_K dens μ dμH[n] < ∞ for compact K (step 4, ‖e‖ = 1). So φ_μ is locally μH[n]-integrable (each point has the compact neighbourhood B̄_1(x)).
(A.1) For μ ∈ 𝓜, 0 < λ < 1 and |y| ≤ 1 − λ, the function x ↦ φ_μ(y + λx) equals φ_{μ^{y,λ}} (step 2), and μ^{y,λ} ∈ 𝓜 by (3).
(A.2) Let μ ∈ 𝓜, |y| < 1, and λ_k > 0 strictly decreasing to 0. Hypothesis (4) gives sub and a homogeneous ν ∈ 𝓜 with ∫ f dμ^{y,λ_{sub(j)}} → ∫ f dν for all continuous compactly supported f. Put ψ := φ_ν ∈ F; then ψ(λx) = ψ(x) by step 3. For j large, λ_{sub(j)} < 1 − |y| ≤ 1, so μ^{y,λ_{sub(j)}} ∈ 𝓜 by (3). By steps 2 and 4, ∫ f(x)•φ_μ(y + λ_{sub(j)}x) dμH[n] = ∫ f•φ_{μ^{y,λ_{sub(j)}}} dμH[n] = c_n⁻¹(∫ f dμ^{y,λ_{sub(j)}})•e → c_n⁻¹(∫ f dν)•e = ∫ f•ψ dμH[n].
(A.3) Closedness: sing φ is a closure.
(A.3)(1) Let μ ∈ 𝓜, L an n-dimensional subspace and c″ ∈ Euclid 1 with φ_μ = 1_L·c″. Put c′ := c″ 0. Comparing coordinate 0, dens μ x = c′ for x ∈ L and = 0 for x ∉ L.
– If c′ < c, then {x : c ≤ dens μ x} = ∅ (on L the value is c′ < c, off L it is 0 < c), so sing φ_μ = closure ∅ = ∅.
– If c′ ≥ c, then by (2), μ = Hⁿ.withDensity(ofReal(c′)·1_L) and μ(ℝ^P) = ofReal(c′)·Hⁿ(L) = ∞. Here c′ ≥ c > 0, and Hⁿ(L) = ∞ because L with the induced inner product is isometric to ℝⁿ, Hⁿ restricted to L is its volume (Isometry.euclideanHausdorffMeasure_image, InnerProductSpace.euclideanHausdorffMeasure_eq_volume), and volume(ℝⁿ) = ∞ for n ≥ 1 (MeasureTheory.measure_univ_of_isAddLeftInvariant: ℝⁿ is not compact for n ≥ 1). Hypothesis (6) is contradicted.
So sing φ_μ = ∅ in all cases.
(A.3)(2) For λ > 0, w ↦ y + λw is a homeomorphism of ℝ^P. Hence sing(φ(y + λ·)) = closure((y + λ·)⁻¹{c ≤ φ(·) 0}) = (y + λ·)⁻¹(closure{c ≤ φ(·) 0}) = (y + λ·)⁻¹(sing φ) for every φ.
(A.3)(3) (parent 5(ε).) Let μ ∈ 𝓜 and φ_k ∈ F with ∫ f•φ_k dμH[n] → ∫ f•φ_μ dμH[n] for all continuous compactly supported f, and let ε > 0. Choose μ_k ∈ 𝓜 with φ_k = φ_{μ_k}. By step 4 (apply ⟨·, e⟩ and multiply by c_n), ∫ f dμ_k → ∫ f dμ. Suppose the conclusion fails. Then there are k_1 < k_2 < … and w_j ∈ B_1(0) ∩ sing φ_{μ_{k_j}} with dist(w_j, z) ≥ ε for all z ∈ sing φ_μ. By step 6, c ≤ dens μ_{k_j} w_j. After passing to a further subsequence, w_j → w with |w| ≤ 1 < 2. Apply Lemma D (Step 0) to the measures μ_{k_j} and μ: (1) and (5) hold, vague convergence holds along the subsequence, the densities at w_j and at w exist by step 5, and θ := dens μ w ≥ 0. It gives c ≤ dens μ w, so w ∈ {c ≤ dens μ} ⊆ sing φ_μ. Then dist(w_j, w) ≥ ε for all j, contradicting w_j → w. Hence there is k₀ with B_1(0) ∩ sing φ_k ⊆ {x : ∃ z ∈ sing φ_μ, dist(x, z) < ε} for all k ≥ k₀.
8. (Application of A.4; parent steps 6, 7.) Hypothesis (ADR), applied to (P, n, Q := 1, F, sing) with the hypotheses verified in step 7, gives (I) or (II).
(I) B_1(0) ∩ sing φ = ∅ for every φ ∈ F. For μ ∈ 𝓜, {x ∈ B_1(0) : c ≤ dens μ x} ⊆ B_1(0) ∩ sing φ_μ = ∅, which is the first alternative.
(II) There is d with d + 1 ≤ n such that μH[d + α](sing φ ∩ B_1(0)) = 0 for φ ∈ F and α > 0; if d = 0, sing φ ∩ B_σ(0) is finite for φ ∈ F and σ < 1; and there are ψ ∈ F and L with dim L = d, sing ψ = L and ψ(y + λx) = ψ(x) for y ∈ L, λ > 0. For μ ∈ 𝓜, {x ∈ B_1(0) : c ≤ dens μ x} ⊆ sing φ_μ ∩ B_1(0), so it is μH[d + α]-null by monotonicity. If d = 0, {x ∈ B_σ(0) : c ≤ dens μ x} ⊆ sing φ_μ ∩ B_σ(0) is finite. Write ψ = φ_ν with ν ∈ 𝓜; coordinate 0 gives dens ν (y + λx) = dens ν x for y ∈ L, λ > 0.
Let E := {x : c ≤ dens ν x}, so closure E = L.
– E ⊆ L.
– E ≠ ∅, since otherwise closure ∅ = ∅ ≠ L ∋ 0.
– dens ν is constant on L: for y ∈ L, dens ν y = dens ν (y + 1•0) = dens ν 0.
Taking x₀ ∈ E ⊆ L, we get c ≤ dens ν x₀ = dens ν 0 = dens ν y for all y ∈ L. Hence E = L.
Finally ν(ℝ^P) = ∞. First, ν ≠ 0, since otherwise dens ν ≡ 0 < c and E = ∅. With y = 0, dens ν(λx) = dens ν x. By (2) and Hⁿ(λ·s) = λⁿHⁿ(s), the change of variables x = λx′ gives ν(λ·s) = ∫_{λ·s} ofReal(dens ν) dHⁿ = λⁿ∫_s ofReal(dens ν(λ·)) dHⁿ = λⁿν(s). Choose R₁ with ν(B_{R₁}(0)) > 0, which exists because ν(ℝ^P) = sup_R ν(B_R(0)) > 0. Then ν(B_{tR₁}(0)) = tⁿν(B_{R₁}(0)) → ∞ as t → ∞ (n ≥ 1), so ν(ℝ^P) = ∞. This gives the second alternative with this d, ν and L. ∎

## Key steps

1. Lemma D (parent step 4): monotonicity at moving centres, limsup μ_j(K) ≤ μ(K) for compact K under vague convergence, and the closed-to-open ball comparison give c ≤ θ.
2. dens μ is Borel (lower semicontinuity in x, left continuity in ρ, rational radii); dens μ^{y,λ} = dens μ(y + λ·), and homogeneous ν have dilation-invariant dens ν.
3. From μ = Hⁿ.withDensity(dens μ) with Hⁿ = c_nμH[n]: ∫ f·φ_μ dμH[n] = c_n⁻¹(∫ f dμ)e₁, so weak convergence of the φ_μ is vague convergence of the μ, and local integrability and (H0) hold.
4. Monotonicity gives existence of densities on B_2(0); Lemma D gives upper semicontinuity there, so sing φ_μ ∩ B_2(0) ⊆ {dens μ ≥ c}.
5. Verify A.1 (closure (3)), A.2 (hypothesis (4) plus normalized pairings), A.3(1) (c′ < c gives an empty superlevel set; c′ ≥ c gives infinite mass, contradicting (6)), A.3(2) (homeomorphism), and A.3(3) (subsequence argument with Lemma D).
6. Apply hypothesis (ADR); in case (II), the extremal ν has dens ν constant on L, so {dens ν ≥ c} = L, and ν is nonzero and n-homogeneous, hence ν(ℝ^P) = ∞.

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
