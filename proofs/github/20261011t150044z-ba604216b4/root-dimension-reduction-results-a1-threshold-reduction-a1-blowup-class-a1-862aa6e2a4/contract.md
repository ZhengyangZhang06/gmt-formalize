<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.threshold_reduction-a1.blowup_class-a1 -->

## Theorem `Submission.dimred_tr_blowup_class`

Assume (IM), (MON), (MB) and (TAN). (IM), (MON) and (MB) are, in exactly the form of their frozen Lean types, the statements of Submission.dimred_im_mass_measure, Submission.dimred_minimizing_monotonicity and Submission.dimred_blowup_limit_moving_centres (the three registered dependencies of the selected parent). (TAN) is, verbatim, the conclusion of the sibling child tangent_measure_homogeneous (Submission.dimred_tr_tangent_measure_homogeneous: Simon 7.3.1(2) with the homogeneity of cone weights) after its two leading hypotheses (MON) and (MB):
- (IM): an IMRep of a current on an open domain has M_W = weight on open W, support = support of the weight, and a unique weight.
- (MON): monotonicity (i) with e^{Λρ} on compact sets, (ii) without the factor when N = ℝ^P, existence and upper semicontinuity of densities (iii), and density ≥ 1 on the support (iv) for minimizing currents with ∂T = 0 in an embedded C² submanifold.
- (MB): subsequential weak limits of blow-ups with moving centres x_j → x ∈ U and scales → 0 exist, are minimizing in ℝ^P with ∂ = 0, and carry mass-measure convergence.
- (TAN): for n ≥ 1, T minimizing in U ∩ N with spt T ⊆ U ∩ N and ∂T = 0 in U, a point x ∈ spt T and scales λ_j → 0, a subsequence of the blow-ups η_{x,λ_j#}T converges weakly in ℝ^P, with mass-measure convergence, to a current C that is minimizing in ℝ^P and whose IMRep weights are n-homogeneous.
Under these hypotheses: Let n, k, ℓ ∈ ℕ with ℓ ≤ k and n ≥ 1, P := n + k, U ⊆ ℝ^P open, N an embedded C² (n+ℓ)-dimensional submanifold with (closure N ∖ N) ∩ U = ∅, and T ∈ 𝒟_n(U) minimizing in U ∩ N with spt T ⊆ U ∩ N and ∂T = 0 in U. Let z ∈ ℝ^P and r > 0 with B̄_{2r}(z) ⊆ U. For Borel measures μ on ℝ^P let dens μ x := (limsup_{ρ↓0} μ(B_ρ(x))/(ω_nρⁿ)).toReal and μ^{y,λ} := ofReal(λ⁻¹ⁿ) • μ.map (dilation y λ). Then there are a set 𝓜 of Borel measures on ℝ^P and Λ ∈ ℝ such that: (1) each μ ∈ 𝓜 is finite on compact sets; (2) each μ ∈ 𝓜 equals Hⁿ.withDensity (ofReal ∘ dens μ), Hⁿ = μHE[n]; (3) μ^{y,λ} ∈ 𝓜 whenever μ ∈ 𝓜, 0 < λ < 1, |y| ≤ 1 − λ; (4) for μ ∈ 𝓜, |y| < 1 and strictly decreasing λ_j > 0 with λ_j → 0, there are a strictly increasing sub and ν ∈ 𝓜 with ν(λ·s) = λⁿν(s) (λ > 0, s Borel) and ∫ f dμ^{y,λ_{sub(j)}} → ∫ f dν for every continuous compactly supported f; (5) for μ ∈ 𝓜 and B̄_R(y) ⊆ B̄_2(0), ρ ↦ ofReal(e^{Λρ}/ρⁿ)·μ(B_ρ(y)) is nondecreasing on (0, R); (6) some μ₀ ∈ 𝓜 has dens μ₀ w = θ whenever |w| < 1 and HasMassDensity T (z + rw) θ; (7) for every ν ∈ 𝓜 with ν(ℝ^P) = ∞ there are S ∈ 𝒟_n(ℝ^P), points x_i ∈ B_r(z) and scales λ_i > 0 with λ_i → 0 such that η_{x_i,λ_i#}T ⇀ S in ℝ^P (ConvergesWeakly), S is minimizing in ℝ^P, ∂S = 0, and HasMassDensity S y (dens ν y) for every y ∈ ℝ^P. (In the Lean statement dens is a universally quantified function fixed by its defining equation.)

Node: `root.dimension_reduction_results-a1.threshold_reduction-a1.blowup_class-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1030

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7930, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7935, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1240, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7938

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8618, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8623, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8626, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8629, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8634, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8639, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8646, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8647, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6873, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6888, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4717

## Lean problem

Declaration: `Submission.dimred_tr_blowup_class`

```lean
(∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → (∀ W : Set (Euclid P), IsOpen W → W ⊆ U → T.massOn W = R.measure W) ∧ (∀ x ∈ U, (x ∈ T.support ↔ ∀ ε : ℝ, 0 < ε → R.measure (ball x ε) ≠ 0)) ∧ ∀ R' : IMRep U n, R'.Represents T → R'.measure = R.measure) → (∀ (P n d : ℕ) (U N : Set (Euclid P)) (T : GeometricCurrentOn U n), 1 ≤ n → n ≤ d → d ≤ P → IsOpen U → IsEmbeddedSubmanifold 2 d N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ (y : Euclid P) (R : ℝ), closedBall y R ⊆ K → MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ n) * T.massOn (ball y ρ)) (Ioo 0 R)) ∧ (N = univ → ∀ (y : Euclid P) (R : ℝ), ball y R ⊆ U → MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (1 / ρ ^ n) * T.massOn (ball y ρ)) (Ioo 0 R)) ∧ (∃ Θ : Euclid P → ℝ, (∀ y ∈ U, HasMassDensity T y (Θ y)) ∧ UpperSemicontinuousOn Θ U) ∧ ∀ y ∈ T.support, ∀ θ : ℝ, HasMassDensity T y θ → 1 ≤ θ) → (∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n), 1 ≤ n → IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → ∀ (x : Euclid (n + k)) (xs : ℕ → Euclid (n + k)) (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), x ∈ U → Tendsto xs atTop (𝓝 x) → Tendsto lams atTop (𝓝 0) → ∃ (φ : ℕ → ℕ) (C : GeometricCurrentOn (univ : Set (Euclid (n + k))) n), StrictMono φ ∧ ConvergesWeakly (fun j => blowUp T (xs (φ j)) (lams (φ j)) (hlams (φ j)).ne') C ∧ MassMeasuresConverge (fun j => blowUp T (xs (φ j)) (lams (φ j)) (hlams (φ j)).ne') C ∧ IsMinimizingIn C univ ∧ BoundaryVanishes C) → (∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n), 1 ≤ n → IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → ∀ x ∈ T.support, ∀ (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), Tendsto lams atTop (𝓝 0) → ∃ (φ : ℕ → ℕ) (C : GeometricCurrentOn (univ : Set (Euclid (n + k))) n), StrictMono φ ∧ ConvergesWeakly (fun j => blowUp T x (lams (φ j)) (hlams (φ j)).ne') C ∧ MassMeasuresConverge (fun j => blowUp T x (lams (φ j)) (hlams (φ j)).ne') C ∧ IsMinimizingIn C univ ∧ ∀ R : IMRep (univ : Set (Euclid (n + k))) n, R.Represents C → ∀ lam : ℝ, 0 < lam → ∀ A : Set (Euclid (n + k)), MeasurableSet A → R.measure ((fun x => lam • x) '' A) = ENNReal.ofReal (lam ^ n) * R.measure A) → ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n), 1 ≤ n → IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → ∀ (z : Euclid (n + k)) (r : ℝ) (dens : Measure (Euclid (n + k)) → Euclid (n + k) → ℝ), 0 < r → closedBall z (2 * r) ⊆ U → (∀ (μ : Measure (Euclid (n + k))) (x : Euclid (n + k)), dens μ x = (limsup (fun ρ : ℝ => μ (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0)).toReal) → ∃ (𝓜 : Set (Measure (Euclid (n + k)))) (Λ : ℝ), (∀ μ ∈ 𝓜, ∀ K : Set (Euclid (n + k)), IsCompact K → μ K ≠ ∞) ∧ (∀ μ ∈ 𝓜, μ = (μHE[n] : Measure (Euclid (n + k))).withDensity (fun x => ENNReal.ofReal (dens μ x))) ∧ (∀ μ ∈ 𝓜, ∀ (y : Euclid (n + k)) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → ENNReal.ofReal (lam⁻¹ ^ n) • μ.map (dilation y lam) ∈ 𝓜) ∧ (∀ μ ∈ 𝓜, ∀ y : Euclid (n + k), ‖y‖ < 1 → ∀ lams : ℕ → ℝ, (∀ j, 0 < lams j) → StrictAnti lams → Tendsto lams atTop (𝓝 0) → ∃ (sub : ℕ → ℕ) (ν : Measure (Euclid (n + k))), StrictMono sub ∧ ν ∈ 𝓜 ∧ (∀ lam : ℝ, 0 < lam → ∀ s : Set (Euclid (n + k)), MeasurableSet s → ν ((fun x => lam • x) '' s) = ENNReal.ofReal (lam ^ n) * ν s) ∧ ∀ f : Euclid (n + k) → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun j => ∫ x, f x ∂(ENNReal.ofReal ((lams (sub j))⁻¹ ^ n) • μ.map (dilation y (lams (sub j))))) atTop (𝓝 (∫ x, f x ∂ν))) ∧ (∀ μ ∈ 𝓜, ∀ (y : Euclid (n + k)) (R : ℝ), closedBall y R ⊆ closedBall 0 2 → MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ n) * μ (ball y ρ)) (Ioo 0 R)) ∧ (∃ μ₀ ∈ 𝓜, ∀ w ∈ ball (0 : Euclid (n + k)) 1, ∀ θ : ℝ, HasMassDensity T (z + r • w) θ → dens μ₀ w = θ) ∧ ∀ ν ∈ 𝓜, ν univ = ∞ → ∃ (S : GeometricCurrentOn (univ : Set (Euclid (n + k))) n) (xs : ℕ → Euclid (n + k)) (lams : ℕ → ℝ) (hlams : ∀ i, 0 < lams i), (∀ i, xs i ∈ ball z r) ∧ Tendsto lams atTop (𝓝 0) ∧ ConvergesWeakly (fun i => blowUp T (xs i) (lams i) (hlams i).ne') S ∧ IsMinimizingIn S univ ∧ BoundaryVanishes S ∧ ∀ y, HasMassDensity S y (dens ν y)
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
- Child DAG node: `root.dimension_reduction_results-a1.threshold_reduction-a1.blowup_class-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, steps 1, 2(a)–(f), 3(i)–(iii) and 3(vii) (Simon's class 𝒯 of rescalings η_{x,λ#}T′ of T′ = (η_{z,r#}T)⌞B_2(0) and their zero-scale limits), stated for the class 𝓜 := {μ_S : (S, U_S) ∈ 𝒯} of extended mass measures.
Sibling lemmas used: imrep_density_ae (Submission.dimred_tr_imrep_density_ae), blowup_calculus (Submission.dimred_tr_blowup_calculus), the reused accepted blowup_imrep (Submission.dtc_blowUp_imrep: for an IMRep R of A ∈ 𝒟_n(O), a point a and t > 0 there is an IMRep R′ of blowUp A a t in dilation a t '' O with R′.measure s = ofReal(t⁻¹ⁿ)·R.measure(dilation a t ⁻¹' s) for every Borel s; no hypothesis on O or n), and iterated_blowup_limit (Submission.dimred_tr_iterated_blowup_limit). Hypotheses (IM), (MON), (MB), (TAN): the first three leading hypotheses of the statement are, verbatim, the frozen Lean types of Submission.dimred_im_mass_measure, Submission.dimred_minimizing_monotonicity and Submission.dimred_blowup_limit_moving_centres (the registered dependencies of the selected parent), and the fourth is, verbatim, the conclusion of the sibling tangent_measure_homogeneous (Submission.dimred_tr_tangent_measure_homogeneous) after its hypotheses (MON) and (MB); the selected parent obtains it by applying that sibling to its registered dependencies. The proof uses these four results only through the hypotheses, at the places where the parent proof cites them (steps 1, 2(b), 2(e), 3(vii)). (IM)(a) gives M_O(A) = R.measure(O) for every IMRep R of a current A on an open domain and every open O inside that domain. (MON)(i), (ii), (iii) give the monotonicity formulas and the existence of densities. (MB) gives minimality and ∂ = 0 of blow-up limits with moving centres. (TAN) gives tangent limits with mass-measure convergence and n-homogeneous weights (parent 2(e) and 3(vii)). No other result outside the sibling set is used.
Notation: P := n + k; Hⁿ := μHE[n]; ω_n := unitBallVolume n; q(μ, x, ρ) := μ(B_ρ(x))/(ω_nρⁿ); η_{a,t} := dilation a t, η_{a,t}(p) = t⁻¹(p − a); m^{y,t} := ofReal(t⁻¹ⁿ) • m.map η_{y,t} for a measure m.
Step 0 (preliminaries).
(0a) T is integer multiplicity (part of IsMinimizingIn); fix an IMRep R_T of T and put μ_T := R_T.measure. By (IM)(a), M_O(T) = μ_T(O) for open O ⊆ U.
(0b) W := B_{2r}(z), K := B̄_{2r}(z) ⊆ U compact. μ_T(K) < ∞ by the field locallyIntegrable_mult of R_T. μ_W := μ_T.restrict W is a finite measure.
(0c) Apply (MON) to T with d := n + ℓ (1 ≤ n ≤ n + ℓ ≤ n + k; the other hypotheses are those of T). By (i) for K there is Λ_K ≥ 0 such that t ↦ ofReal(e^{Λ_Kt}/tⁿ)·M_{B_t(c′)}(T) is nondecreasing on (0, R′) whenever B̄_{R′}(c′) ⊆ K. Put Λ := rΛ_K.
(0d) ℝ^P is an embedded C² (n+k)-dimensional submanifold: IsEmbeddedSubmanifold 2 (n + k) univ, witnessed at each point by V = W = ℝ^P and ψ = id (open, smooth, injective, ψ(V) = W ∩ ℝ^P, preimages of compact sets compact, Dψ = id injective). Also (closure univ ∖ univ) ∩ univ = ∅. Hence for S ∈ 𝒟_n(ℝ^P) minimizing in ℝ^P with ∂S = 0, (MON) applies with U = N = ℝ^P and d = n + k, and (TAN) applies with ℓ := k and U = N = ℝ^P (univ ∩ univ = univ, IsOpen univ, spt S ⊆ univ).
(0e) (Use of (TAN).) Step 7 applies (TAN) in two ways, always with the standing hypothesis n ≥ 1 of the statement. It applies (TAN) to T itself, with its own U and N; ∂T = 0 in U is a hypothesis. It also applies (TAN) to zero-scale currents S ∈ 𝒯₀, with ℓ := k and U = N = ℝ^P via (0d); ∂S = 0 by step 2. No information about spt ∂ is needed, since (TAN) assumes ∂ = 0 directly.
(0f) Uniqueness of weak limits: if ConvergesWeakly (A_i) S and ConvergesWeakly (A_{φ(j)}) C with S, C ∈ 𝒟_n(ℝ^P) and φ strictly increasing, then S = C, because S(ω) and C(ω) are limits of the same subsequence of currentEval(A_i, ω) (GeometricCurrentOn.ext).
(0g) The IMRep R_∅ of ℝ^P with empty carrier (multiplicity 0, orientation 0) represents the zero current, and R_∅.measure = 0. Every field holds trivially; the a.e. fields refer to Hⁿ⌞∅ = 0.
(0h) Vanishing blow-ups: suppose A ∈ 𝒟_n(O) vanishes on an open set containing B_ε(p) (A.VanishesOn) and t_j > 0, t_j → 0. Then ConvergesWeakly (blowUp A p t_j) 0. Indeed, for ω ∈ 𝒟ⁿ(ℝ^P) with tsupport ω ⊆ B_{R_ω}(0), blowup_calculus (ii) gives currentEval(blowUp A p t_j, ω) = currentEval(A, η_{p,t_j}^#ω), and tsupport η_{p,t_j}^#ω = η_{p,t_j}⁻¹(tsupport ω) ⊆ B_{t_jR_ω}(p) ⊆ B_ε(p) once t_jR_ω < ε. This value is 0 (by VanishesOn if the form lies in 𝒟ⁿ(O), and by definition of currentEval otherwise). If p ∈ O ∖ spt A, such ε exists because p ∈ A.zeroRegion; then M_{B_ε(p)}(A) = 0 and, when A has an IMRep R, R.measure(B_ε(p)) = 0 ((IM)(a)).
(0i) (Homogeneous tangent weights; parent 3(vii).) In step 7, n-homogeneity of the weights of the tangent limits C is part of the conclusion of (TAN). For every IMRep R_C of C, every λ > 0 and every Borel s, R_C.measure(λ·s) = ofReal(λⁿ)·R_C.measure(s), where λ·s = (fun x ↦ λ • x) '' s.
(0j) If R is an IMRep of A ∈ 𝒟_n(O) with O open, p ∈ O and HasMassDensity A p θ, then dens R.measure p = θ. For small ρ, B_ρ(p) ⊆ O and M_{B_ρ(p)}(A) = R.measure(B_ρ(p)), so q(R.measure, p, ρ) → ofReal θ; the limsup equals ofReal θ, and θ ≥ 0.
(0k) Parameter congruence: if a = a′ and t = t′ (t ≠ 0), then currentEval(blowUp A a t h, ω) = currentEval(blowUp A a′ t′ h′, ω) for every form ω. Likewise, ConvergesWeakly and MassMeasuresConverge statements about sequences of blow-ups are unchanged when centres and scales are replaced by pointwise-equal expressions: substitute the equal parameters, the proof arguments being propositions. This is used tacitly below whenever centres and scales are rewritten, e.g. z + r•(x_i + λ_i•y) = (z + r•x_i) + (rλ_i)•y and r(λ_iλ′) = (rλ_i)λ′.
(0l) Measure form of blowup_imrep. Let R be an IMRep of A ∈ 𝒟_n(O), a ∈ ℝ^P and t > 0. blowup_imrep gives an IMRep R′ of blowUp A a t with R′.measure = ofReal(t⁻¹ⁿ) • R.measure.map (dilation a t). Indeed, dilation a t is continuous, hence measurable. For Borel s, (ofReal(t⁻¹ⁿ) • R.measure.map (dilation a t))(s) = ofReal(t⁻¹ⁿ)·R.measure(dilation a t ⁻¹' s) (Measure.smul_apply, Measure.map_apply), and this equals R′.measure(s). Both sides are measures on the Borel σ-algebra, so they are equal (Measure.ext).
Step 1 (the class; parent step 2).
(1a) Positive-scale members (parent 2(a)): for (x, λ) with 0 < λ ≤ 1 and |x| ≤ 1 − λ, put s := rλ, c := z + rx and μ_{x,λ} := ofReal(s⁻¹ⁿ) • μ_W.map η_{c,s}. This is the extended mass measure of η_{x,λ#}T′. For Borel B, μ_{x,λ}(B) = s^{−n}μ_W(η_{c,s}⁻¹B), and η_{c,s}⁻¹(B_ρ(w)) = B_{sρ}(c + sw).
(1b) Zero-scale currents 𝒯₀ (parent 2, parameter λ = 0): S ∈ 𝒟_n(ℝ^P) belongs to 𝒯₀ if there are x_i ∈ ℝ^P, λ_i ∈ (0, 1) and x̄ ∈ ℝ^P with |x_i| < 1 − λ_i, λ_i → 0, x_i → x̄, and blowUp T (z + r x_i) (rλ_i) ⇀ S in ℝ^P (ConvergesWeakly). (The current η_{x_i,λ_i#}T′ of the parent agrees with this blow-up of T on η_{x_i,λ_i}(B_2(0)) ⊇ B_{1/λ_i}(0).) Note |x̄| ≤ 1.
(1c) 𝓜₀ := {R.measure : R an IMRep of ℝ^P representing some S ∈ 𝒯₀}, and 𝓜 := {μ_{x,λ}} ∪ 𝓜₀.
Step 2 (zero-scale members are minimizing; parent 2(b)). Let S ∈ 𝒯₀ with data (x_i, λ_i, x̄). Then z + r x̄ ∈ B̄_r(z) ⊆ U, z + r x_i → z + r x̄, and rλ_i → 0. (MB) gives a strictly increasing φ and C with blowUp T (z + rx_{φ(j)}) (rλ_{φ(j)}) ⇀ C, C minimizing in ℝ^P and ∂C = 0. By (0f), S = C. So S is minimizing in ℝ^P, in particular integer multiplicity with IMReps, and ∂S = 0.
Step 3 (local finiteness; property (1)). μ_{x,λ}(ℝ^P) = s^{−n}μ_T(W) < ∞. For R.measure ∈ 𝓜₀ (R an IMRep of ℝ^P) and compact K, R.measure(K) = ∫_{M∩K} θ dHⁿ < ∞ by locallyIntegrable_mult (K ⊆ ℝ^P).
Step 4 (density representation, property (2); parent 3(iii)).
(4a) Let R.measure ∈ 𝓜₀. Apply imrep_density_ae to R with W := ℝ^P; finiteness holds by step 3. For Hⁿ-a.e. x, q(R.measure, x, ρ) → g(x) := 1_M(x)θ(x) < ∞. So, for Hⁿ-a.e. x, dens R.measure x = g(x).toReal and ofReal(dens R.measure x) = g(x). Hence Hⁿ.withDensity(ofReal∘dens R.measure) = Hⁿ.withDensity(1_Mθ) = (Hⁿ⌞M).withDensity θ = R.measure (withDensity_congr_ae, withDensity_indicator).
(4b) Apply imrep_density_ae to R_T with the open set W. Finiteness: R_T.measure(K′ ∩ W) ≤ μ_T(K) < ∞ for compact K′. For Hⁿ-a.e. p, q(μ_W, p, ρ) = R_T.measure(B_ρ(p) ∩ W)/(ω_nρⁿ) → g_W(p), where g_W := 1_{M_T∩W}·θ_T is a Borel function with finite values; hence ofReal(dens μ_W p) = g_W(p) for Hⁿ-a.e. p. Also μ_W = (Hⁿ⌞(M_T ∩ W)).withDensity θ_T = Hⁿ.withDensity g_W (withDensity_indicator; M_T ∩ W is Borel).
(4c) Let μ_{x,λ}, with s, c as in (1a) and η := η_{c,s}. Since η is a measurable equivalence and g_W is measurable, μ_W.map η = (Hⁿ.withDensity g_W).map η = (Hⁿ.map η).withDensity(g_W∘η⁻¹); evaluate both sides on Borel sets with lintegral_map_equiv. Also Hⁿ.map η = sⁿ·Hⁿ, since Hⁿ(η⁻¹B) = Hⁿ(c + sB) = sⁿHⁿ(B) by translation invariance and homogeneity of μHE[n]. Hence μ_{x,λ} = Hⁿ.withDensity(g_W∘η⁻¹). By (1a), q(μ_{x,λ}, w, ρ) = q(μ_W, c + sw, sρ), so (as ρ ↦ sρ preserves 𝓝[>]0) dens μ_{x,λ} w = dens μ_W (c + sw) = dens μ_W (η⁻¹w) for every w. Since η maps Hⁿ-null sets to Hⁿ-null sets (Hⁿ(η(Z)) = s^{−n}Hⁿ(Z)), (4b) gives ofReal(dens μ_{x,λ} w) = g_W(η⁻¹w) for Hⁿ-a.e. w. By withDensity_congr_ae, μ_{x,λ} = Hⁿ.withDensity(ofReal∘dens μ_{x,λ}), which proves (2) for μ_{x,λ}. No measurability of dens μ_W or dens μ_{x,λ} is needed, since withDensity_congr_ae only uses Hⁿ-a.e. equality.
Step 5 (closure under rescaling, property (3); parent 2(c)). Let 0 < λ′ < 1 and |y| ≤ 1 − λ′.
(5a) For μ_{x,λ}: ofReal(λ′⁻¹ⁿ) • μ_{x,λ}.map η_{y,λ′} = ofReal((sλ′)⁻¹ⁿ) • μ_W.map(η_{y,λ′}∘η_{c,s}) (Measure.map_smul, Measure.map_map). Also η_{y,λ′}∘η_{c,s} = η_{c+sy, sλ′}, since λ′⁻¹(s⁻¹(p − c) − y) = (sλ′)⁻¹(p − c − sy). Here c + sy = z + r(x + λy) and sλ′ = r(λλ′). So the rescaled measure is μ_{x+λy, λλ′}, and the pair is admissible: 0 < λλ′ ≤ 1 and |x + λy| ≤ 1 − λ + λ(1 − λ′) = 1 − λλ′. The same computation shows μ_{x,λ}^{y,t} = ofReal((st)⁻¹ⁿ) • μ_W.map η_{c+sy, st} for every t > 0.
(5b) For ν = R.measure ∈ 𝓜₀, with R representing S ∈ 𝒯₀ with data (x_i, λ_i, x̄):
– (0l) gives an IMRep R′ of blowUp S y λ′, a current on η_{y,λ′}(ℝ^P) = ℝ^P, with R′.measure = ofReal(λ′⁻¹ⁿ) • ν.map η_{y,λ′}.
– Let S′ := (blowUp S y λ′).restrictDomain (ℝ^P ⊆ η_{y,λ′}(ℝ^P)) ∈ 𝒟_n(ℝ^P), and let R″ be the IMRep of ℝ^P with the same carrier, multiplicity and orientation as R′. The IMRep axioms refer to the domain only through "carrier ⊆ domain" and "compact ⊆ domain", and the two domains are equal sets. R″ represents S′, and R″.measure = R′.measure.
– S′ ∈ 𝒯₀ with data x′_i := x_i + λ_iy, λ′_i := λ_iλ′ and x̄: λ′_i ∈ (0, 1), |x′_i| < 1 − λ_i + λ_i(1 − λ′) = 1 − λ′_i, λ′_i → 0 and x′_i → x̄. Put a_i := z + rx_i and t_i := rλ_i; then z + rx′_i = a_i + t_iy and rλ′_i = t_iλ′. For ω ∈ 𝒟ⁿ(ℝ^P), blowup_calculus (iii) then (ii) give currentEval(blowUp T (z + rx′_i) (rλ′_i), ω) = currentEval(blowUp T a_i t_i, η_{y,λ′}^#ω) → S(η_{y,λ′}^#ω) = currentEval(blowUp S y λ′, ω) = S′(ω).
Hence ofReal(λ′⁻¹ⁿ) • ν.map η_{y,λ′} = R″.measure ∈ 𝓜₀.
Step 6 (monotonicity, property (5); parent 2(a), 2(b)). Let B̄_R(y) ⊆ B̄_2(0) and ρ ∈ (0, R); if R ≤ 0 there is nothing to prove. For R > 0 we have |y| + R ≤ 2: since P = n + k ≥ 1, there is a unit vector u with y = |y|u (any unit vector if y = 0), and y + Ru lies in B̄_R(y) ⊆ B̄_2(0) and has norm |y| + R.
(6a) For μ_{x,λ}, put c′ := c + sy = z + r(x + λy). Then |c′ − z| + sR = r(|x + λy| + λR) ≤ r(1 − λ + λ(|y| + R)) ≤ r(1 + λ) ≤ 2r. So B̄_{sR}(c′) ⊆ K and B_{sρ}(c′) ⊆ W, and μ_{x,λ}(B_ρ(y)) = s^{−n}μ_T(B_{sρ}(c′)) = s^{−n}M_{B_{sρ}(c′)}(T) by (0a). By (0c), t ↦ ofReal(e^{Λ_Kt}/tⁿ)M_{B_t(c′)}(T) is nondecreasing on (0, sR). So G(ρ) := ofReal(e^{sΛ_Kρ}/ρⁿ)·μ_{x,λ}(B_ρ(y)), which is that function at t = sρ, is nondecreasing on (0, R). Then ofReal(e^{Λρ}/ρⁿ)·μ_{x,λ}(B_ρ(y)) = ofReal(e^{(r−s)Λ_Kρ})·G(ρ) is a product of two nonnegative nondecreasing functions (r − s = r(1 − λ) ≥ 0 and Λ_K ≥ 0), hence nondecreasing.
(6b) For ν = R.measure ∈ 𝓜₀ with R representing S ∈ 𝒯₀: by step 2 and (0d), (MON)(ii) applies to S with N = ℝ^P. So ρ ↦ ofReal(1/ρⁿ)·M_{B_ρ(y)}(S) = ofReal(1/ρⁿ)·ν(B_ρ(y)) ((IM)(a)) is nondecreasing on (0, R) for every R. Multiplying by the nondecreasing factor ofReal(e^{Λρ}) (Λ ≥ 0) keeps it nondecreasing.
Step 7 (tangent measures, property (4); parent 2(e)). Let μ ∈ 𝓜, |y| < 1, and λ_j > 0 strictly decreasing to 0.
(7a) μ = μ_{x,λ}. By (5a), μ^{y,t} = ofReal((st)⁻¹ⁿ) • μ_W.map η_{p, st} for t > 0, where p := c + sy = z + r(x + λy). Since |x + λy| ≤ 1 − λ + λ|y| < 1, p ∈ B_r(z) ⊆ U and B_r(p) ⊆ W.
Case p ∈ spt T. Apply (TAN) to T at p (∂T = 0 in U; see (0e)) with the sequence t_j := sλ_j. It gives a strictly increasing φ and C ∈ 𝒟_n(ℝ^P) with blowUp T p (sλ_{φ(j)}) ⇀ C, MassMeasuresConverge, C minimizing in ℝ^P, and n-homogeneous weights for every IMRep of C. Let R_C be an IMRep of C (C is integer multiplicity, being minimizing) and ν := R_C.measure.
(i) ν ∈ 𝓜₀. Choose j₀ with λλ_{φ(j)} < 1 − |x + λy| for j ≥ j₀. The data x′_j := x + λy, λ′_j := λλ_{φ(j+j₀)}, x̄ := x + λy satisfy the conditions of 𝒯₀. Moreover blowUp T (z + rx′_j) (rλ′_j) = blowUp T p (sλ_{φ(j+j₀)}) ⇀ C, as a tail of a convergent sequence.
(ii) ν is homogeneous by (TAN); see (0i).
(iii) Vague convergence. Let R_j be the IMRep of blowUp T p (sλ_{φ(j)}) given by (0l) from R_T, with R_j.measure = ofReal((sλ_{φ(j)})⁻¹ⁿ) • μ_T.map η_{p, sλ_{φ(j)}}. MassMeasuresConverge gives ∫ f dR_j.measure → ∫ f dν for continuous compactly supported f. If tsupport f ⊆ B_{R_f}(0) and sλ_{φ(j)}R_f < r, then f∘η_{p,sλ_{φ(j)}} is supported in B_{sλ_{φ(j)}R_f}(p) ⊆ W. Hence ∫ f dμ^{y,λ_{φ(j)}} = ∫ f dR_j.measure: both equal (sλ_{φ(j)})^{−n}∫ f∘η dμ_T, by integral_smul_measure, integral_map, and the agreement of μ_W and μ_T on subsets of W.
So sub := φ and ν satisfy (4).
Case p ∉ spt T. By (0h) there is ε > 0 with μ_T(B_ε(p)) = 0, and T vanishes on B_ε(p). Take ν := 0 = R_∅.measure (0g). 0 ∈ 𝒯₀: choose j₀ with λλ_j < 1 − |x + λy| for all j ≥ j₀ (possible since λ_j → 0), and use the data x′_j := x + λy, λ′_j := λλ_{j+j₀}, x̄ := x + λy; then blowUp T (z + rx′_j) (rλ′_j) = blowUp T p (sλ_{j+j₀}) ⇀ 0 by (0h). ν = 0 is homogeneous. Moreover ∫ f dμ^{y,λ_j} = (sλ_j)^{−n}∫ f∘η_{p,sλ_j} dμ_W = 0 once sλ_jR_f < ε, since the integrand is supported in the μ_T-null set B_ε(p). Take sub := id.
(7b) μ = R.measure ∈ 𝓜₀, with R representing S ∈ 𝒯₀ with data (x_i, λ_i^S, x̄). By step 2, S is minimizing in ℝ^P with ∂S = 0.
Case y ∈ spt S. By (0d), (0e) and step 2 (S is minimizing in ℝ^P with ∂S = 0), (TAN) applies to S at y with ℓ := k, U = N = ℝ^P and the sequence λ_j. It gives φ and C with blowUp S y λ_{φ(j)} ⇀ C, MassMeasuresConverge, C minimizing, and n-homogeneous weights for every IMRep of C. Let ν := R_C.measure for an IMRep R_C of C; ν is homogeneous by (TAN); see (0i).
Vague convergence: by (0l), the IMRep R′_j of blowUp S y λ_{φ(j)} has weight μ^{y,λ_{φ(j)}}. So MassMeasuresConverge gives ∫ f dμ^{y,λ_{φ(j)}} → ∫ f dν.
ν ∈ 𝓜₀: apply iterated_blowup_limit with T, U, x := z + r x̄ ∈ U, x_i := z + rx_i, λ_i := rλ_i^S, S, y, s_k := λ_{φ(k)} and C. Its mass hypothesis holds with δ := r/4. For x′ ∈ B_{r/4}(z + r x̄) we have |x′ − z| < 5r/4, hence B̄_{r/2}(x′) ⊆ K. For 0 < ρ < r/4, (0c) at centre x′ with R′ = r/2 gives ofReal(e^{Λ_Kρ}/ρⁿ)M_{B_ρ(x′)}(T) ≤ ofReal(e^{Λ_Kr/4}(4/r)ⁿ)M_{B_{r/4}(x′)}(T) ≤ ofReal(e^{Λ_Kr/4}(4/r)ⁿ)μ_T(W) =: Γ′ < ∞. Since e^{Λ_Kρ} ≥ 1, M_{B_ρ(x′)}(T) ≤ ofReal(Γρⁿ) with Γ := Γ′.toReal.
iterated_blowup_limit then yields a strictly increasing φ′ with blowUp T ((z + rx_{φ′(k)}) + rλ^S_{φ′(k)}y) (rλ^S_{φ′(k)}λ_{φ(k)}) ⇀ C. Choose k₀ with λ_{φ(k)} ≤ 1 − |y| for k ≥ k₀. Then x″_k := x_{φ′(k+k₀)} + λ^S_{φ′(k+k₀)}y and λ″_k := λ^S_{φ′(k+k₀)}λ_{φ(k+k₀)} satisfy: λ″_k ∈ (0, 1); |x″_k| < 1 − λ^S + λ^S(1 − λ_{φ(k+k₀)}) = 1 − λ″_k (with λ^S := λ^S_{φ′(k+k₀)}); λ″_k → 0; x″_k → x̄; and blowUp T (z + rx″_k) (rλ″_k) ⇀ C. Hence C ∈ 𝒯₀ and ν ∈ 𝓜₀. Take sub := φ.
Case y ∉ spt S. By (0h), S vanishes on some B_ε(y), μ(B_ε(y)) = 0, and blowUp S y λ_j ⇀ 0. The same use of iterated_blowup_limit (with C := 0, s_k := λ_k) and the same tail argument show 0 ∈ 𝒯₀, so 0 = R_∅.measure ∈ 𝓜₀. Take ν := 0, which is homogeneous. Moreover ∫ f dμ^{y,λ_j} = λ_j^{−n}∫ f∘η_{y,λ_j} dμ = 0 once λ_jR_f < ε. Take sub := id.
Step 8 (the anchor member, property (6); parent step 8). Let μ₀ := μ_{0,1} = ofReal(r⁻¹ⁿ) • μ_W.map η_{z,r} ∈ 𝓜. Let |w| < 1 and HasMassDensity T (z + rw) θ. For 0 < ρ < 1 − |w|, B_{rρ}(z + rw) ⊆ W ⊆ U. So q(μ₀, w, ρ) = r^{−n}μ_T(B_{rρ}(z + rw))/(ω_nρⁿ) = M_{B_{rρ}(z+rw)}(T)/(ω_n(rρ)ⁿ) by (0a), and this tends to ofReal θ (compose the density limit with ρ ↦ rρ). Hence the limsup is ofReal θ, and dens μ₀ w = θ since θ ≥ 0.
Step 9 (infinite-mass members are admissible zero-scale limits, property (7); parent 2(f), 2(b)). Let ν ∈ 𝓜 with ν(ℝ^P) = ∞. By step 3, ν is not of the form μ_{x,λ}. So ν = R.measure, with R an IMRep of ℝ^P representing some S ∈ 𝒯₀ with data (x_i, λ_i, x̄). Put xs_i := z + rx_i ∈ B_r(z) (as |x_i| < 1) and lams_i := rλ_i > 0. Then lams_i → 0, and ConvergesWeakly (blowUp T xs_i lams_i) S is the defining property. S is minimizing in ℝ^P with ∂S = 0 by step 2. By (MON)(iii) applied to S (U = N = ℝ^P, via (0d)), there is Θ_S with HasMassDensity S y (Θ_S y) for every y. By (0j) with O = ℝ^P, dens ν y = Θ_S y. Hence HasMassDensity S y (dens ν y) for all y.
Step 10 (conclusion). 𝓜 and Λ satisfy (1) by step 3, (2) by step 4, (3) by step 5, (4) by step 7, (5) by step 6, (6) by step 8 and (7) by step 9. ∎

## Key steps

1. The four leading hypotheses are the frozen statements of dimred_im_mass_measure, monotonicity, moving_blowups and the conclusion of the sibling tangent_measure_homogeneous; the proof uses them only through these hypotheses, so the child is provable without those declarations in its worktree.
2. Fix an IMRep R_T of T and monotonicity data Λ_K on K = B̄_{2r}(z); define the positive-scale members μ_{x,λ} = (rλ)^{−n}(η_{z+rx,rλ})_#(μ_T⌞B_{2r}(z)) and the zero-scale currents 𝒯₀ (ConvergesWeakly limits of blowUp T (z+rx_i)(rλ_i) with |x_i| < 1 − λ_i); 𝓜 := {μ_{x,λ}} ∪ {weights of IMReps of 𝒯₀}.
3. Zero-scale currents are minimizing with ∂ = 0 ((MB) plus uniqueness of weak limits); weights are locally finite; imrep_density_ae and the Hausdorff scaling of μHE[n] give μ = Hⁿ.withDensity(dens μ) for all members.
4. Rescaling closure: μ_{x,λ} ↦ μ_{x+λy,λλ′}; zero-scale members are transported by blowup_imrep (the reused dtc_blowUp_imrep, in measure form) and blowup_calculus (composition); monotonicity follows from (MON)(i) on K and (MON)(ii) on ℝ^P with the common Λ = rΛ_K.
5. Tangent measures: (TAN) at the corresponding point gives tangent limits with MassMeasuresConverge and n-homogeneous weights; positive-scale limits are directly in 𝒯₀; zero-scale limits are in 𝒯₀ by iterated_blowup_limit; vanishing points give the zero member.
6. The anchor μ_{0,1} has density Θ_T(z + rw) on B_1(0); a member of infinite mass is a zero-scale weight, hence the weight of an admissible zero-scale limit S with HasMassDensity S y (dens ν y).

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
