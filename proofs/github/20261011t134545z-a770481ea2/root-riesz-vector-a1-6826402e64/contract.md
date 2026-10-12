<!-- theorem-id: gmt-ch01/root.riesz_vector-a1 -->

## Theorem `Submission.riesz_vector`

For every locally compact Hausdorff space X, finite-dimensional real inner product space H, and linear L : C_c(X; H) → ℝ that is bounded above on {f : |f| ≤ 1, spt f ⊆ K} for each compact K, there are a Radon outer measure μ on X and a μ-measurable ν : X → H with |ν| = 1 μ-a.e. and L(f) = ∫_X ⟨f, ν⟩ dμ for all f ∈ C_c(X; H).

Node: `root.riesz_vector-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/18

Decomposition children: None

## Lean problem

Declaration: `Submission.riesz_vector`

```lean
RieszVector
```

### Frozen project context

`GMT/Ch01/Contract.lean` at `ec1c322fab7585cea8deb6a95d4dae2d97d09d8e` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
import Poincare.SimonGMT.Chapter01.MetricCriterion
import Poincare.SimonGMT.Chapter01.ExactRegularity
import Poincare.SimonGMT.Chapter01.Lusin
import Poincare.SimonGMT.Chapter01.EuclideanNormalization
import Poincare.SimonGMT.Chapter01.DensityComparison
import Poincare.SimonGMT.Chapter01.GeneralDensity
import Poincare.SimonGMT.Chapter01.GeneralDifferentiation
import Poincare.SimonGMT.Chapter01.RadonNikodymTheorem
import Poincare.SimonGMT.Chapter01.InfiniteDensitySet
import Poincare.SimonGMT.Chapter01.HausdorffDensityBounds
import Poincare.SimonGMT.Chapter01.HausdorffContentDensity
import Poincare.SimonGMT.Chapter01.RadonPolarRepresentation
import Poincare.SimonGMT.Chapter01.CompactMetrizableCompactness

/-!
# Simon, *Introduction to GMT*, Chapter 1 "Preliminary Measure Theory" (pp. 1–38): contract

Frozen statements of the headline results of Chapter 1 of Leon Simon's
*Introduction to Geometric Measure Theory* (2014 Tsinghua notes).

## Conventions (all as in the book)

* A "measure" on `X` is an **outer measure** `μ : OuterMeasure X` (Simon §1).
* "`μ`-measurable set" (Def. 1.2) is Carathéodory measurability `μ.IsCaratheodory A`.
* "`μ`-a.e. `x`, `P x`" is Mathlib's filter `∀ᵐ x ∂μ, P x` for the outer measure `μ`,
  i.e. `μ {x | ¬ P x} = 0`.
* Integrals `∫ f dμ` and "`μ`-measurable function" refer to the measure space
  `(X, {μ-measurable sets}, μ)` given by Lemma 1.6 / Remark 1.7, see `caratheodoryMeasure`.
* `B_ρ(x)` is the closed ball `Metric.closedBall x ρ`.

## Definitions reused from `Poincare.SimonGMT.Chapter01` (bodies checked against the book)

* `IsBorelRegularOuterMeasure μ` (p. 5): `borel X ≤ μ.caratheodory ∧
  ∀ A, ∃ B, A ⊆ B ∧ MeasurableSet[borel X] B ∧ μ B = μ A`.
* `IsOpenSigmaFinite μ` (Def. 1.14): `∃ V : ℕ → Set X, (∀ n, IsOpen (V n) ∧ μ (V n) < ∞) ∧
  ⋃ n, V n = univ`.
* `realUnitBallVolume m` (p. 9): `ω_m = ENNReal.ofReal (π ^ (m/2) / Γ (m/2 + 1))`.
* `simonHausdorffContentOuter m δ` / `simonHausdorffContent m δ` (2.2): the size-`δ`
  approximation `H^m_δ(A) = ω_m inf {∑ⱼ (diam Cⱼ / 2)^m : A ⊆ ⋃ⱼ Cⱼ, diam Cⱼ < δ}`
  (`δ : ℝ≥0∞`; `δ = ∞` gives Simon's `H^m_∞`); encoded as `ω_m • boundedBy cost`, where
  `cost C = (ediam C / 2)^m` if `ediam C < δ` and `∞` otherwise, empty sets costing `0`.
* `simonHausdorffOuterMeasureReal m` (2.1): `H^m = ⨆ δ > 0, H^m_δ`.
* `dimensionalUpperDensity μ n A x` (3.1): `Θ^{*n}(μ, A, x) =
  limsup_{ρ ↓ 0} μ(A ∩ B_ρ(x)) / (ω_n ρ^n)` in `[0, ∞]`.
* `outerRelativeUpperDensity μ μ₀ x` (3.9): `limsup_{ρ ↓ 0} μ(B_ρ(x)) / μ₀(B_ρ(x))` in
  `[0, ∞]`; with `ℝ≥0∞` division this realizes exactly Simon's three-case definition 3.9
  (value `0` on `V₀`, `∞` on `U₀ \ V₀`), cf. `outerRelativeUpperDensity_eq_piecewise`.
* `HasSymmetricVitaliProperty μ₀` (Def. 3.10): for every `A` with `μ₀ A < ∞` and every family
  `B` of closed balls (pairs (centre, radius > 0)) with centres in `A` covering `A` finely
  (`∀ x ∈ A, ∀ ε > 0, ∃ r ∈ (0, ε), (x, r) ∈ B`), there is a countable pairwise disjoint
  subfamily `D ⊆ B` with `μ₀ (A \ ⋃_{b ∈ D} B_{b.2}(b.1)) = 0`.
* `IsRadonOuterMeasure μ` (Def. 4.6): (R1) Borel regular and finite on compact sets,
  (R2) `μ A = ⨅ {μ U | U open ⊇ A}` for all `A`, (R3) `μ U = ⨆ {μ K | K compact ⊆ U}`
  for open `U`.

## Erratum
* Theorem 4.16 as printed (locally compact, σ-compact Hausdorff `X`) is false; the corrected
  statement adds second countability (equivalently: `X` is a locally compact separable
  metric space, the standing assumption announced for §4 on p. 1). See `RadonCompactness`.
-/

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal CompactlySupported Topology
open Poincare.SimonGMT.Chapter01

namespace GMT.Ch01

universe u v

/-- The measure space `(X, {μ-measurable sets}, μ)` attached to an outer measure `μ`
(Simon Ch. 1, Lemma 1.6 and Remark 1.7, pp. 3–4): Mathlib's `OuterMeasure.toMeasure` on the
Carathéodory σ-algebra `μ.caratheodory`.  Simon's integrals `∫_X f dμ` and his notion of a
`μ`-measurable function refer to this measure space.  (It is definitionally the measure
`IsRadonOuterMeasure.toCaratheodoryMeasure` of `Poincare.SimonGMT`.) -/
noncomputable abbrev caratheodoryMeasure {X : Type u} (μ : OuterMeasure X) :
    @Measure X μ.caratheodory :=
  @OuterMeasure.toMeasure X μ.caratheodory μ le_rfl

/-! ## §1 Basic notions -/

/-- **Carathéodory's criterion.** Simon Ch. 1, Theorem 1.13 (p. 6).

Let `X` be a metric space and `μ` an outer measure on `X` such that
`μ(A ∪ B) = μ(A) + μ(B)` whenever `dist(A, B) > 0` (here `dist(A, B) = inf {d(a,b)}`, which is
`∞` if `A` or `B` is empty; `dist(A, B) > 0` means some `r > 0` bounds all `d(a, b)` below).
Then every Borel set is `μ`-measurable. -/
def CaratheodoryCriterion : Prop :=
  ∀ (X : Type u) [MetricSpace X] (μ : OuterMeasure X),
    (∀ A B : Set X, (∃ r : ℝ, 0 < r ∧ ∀ a ∈ A, ∀ b ∈ B, r ≤ dist a b) →
      μ (A ∪ B) = μ A + μ B) →
    ∀ E : Set X, MeasurableSet[borel X] E → μ.IsCaratheodory E

/-- **Outer and inner regularity of open σ-finite Borel-regular measures.**
Simon Ch. 1, Theorem 1.15 (p. 7).

Let `X` be a topological space in which every closed set is a countable intersection of open
sets (a `G_δ` set), and let `μ` be an open σ-finite (Def. 1.14) Borel-regular measure on `X`.
Then (1) `μ(A) = inf {μ(U) : U open, U ⊇ A}` for every `A ⊆ X`, and
(2) `μ(A) = sup {μ(C) : C closed, C ⊆ A}` for every `μ`-measurable `A ⊆ X`. -/
def BorelRegularApproximation : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], (∀ C : Set X, IsClosed C → IsGδ C) →
    ∀ μ : OuterMeasure X, IsBorelRegularOuterMeasure μ → IsOpenSigmaFinite μ →
      (∀ A : Set X, μ A = ⨅ (U : Set X) (_ : A ⊆ U) (_ : IsOpen U), μ U) ∧
      (∀ A : Set X, μ.IsCaratheodory A →
        μ A = ⨆ (C : Set X) (_ : C ⊆ A) (_ : IsClosed C), μ C)

/-- **Lusin's theorem.** Simon Ch. 1, Theorem 1.17 (p. 8).

Let `μ` be a Borel-regular outer measure on a topological space `X` in which every closed set is
a countable intersection of open sets, let `A ⊆ X` be `μ`-measurable with `μ(A) < ∞`, and let
`f : A → ℝ` be `μ`-measurable (measurable for the trace on `A` of the σ-algebra of
`μ`-measurable sets).  Then for each `ε > 0` there is a closed set `C ⊆ X` with `C ⊆ A`,
`μ(A \ C) < ε`, and `f|_C` continuous.  (No open σ-finiteness of `μ` is assumed.) -/
def LusinTheorem : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], (∀ C : Set X, IsClosed C → IsGδ C) →
    ∀ μ : OuterMeasure X, IsBorelRegularOuterMeasure μ →
    ∀ A : Set X, μ.IsCaratheodory A → μ A < ∞ →
    ∀ f : A → ℝ, Measurable[MeasurableSpace.comap (Subtype.val : A → X) μ.caratheodory] f →
    ∀ ε : ℝ, 0 < ε →
      ∃ (C : Set X) (hCA : C ⊆ A), IsClosed C ∧ μ (A \ C) < ENNReal.ofReal ε ∧
        Continuous (f ∘ Set.inclusion hCA)

/-! ## §2 Hausdorff measure -/

/-- **Lebesgue measure equals Hausdorff measure on `ℝⁿ`.** Simon Ch. 1, Theorem 2.9 (p. 11).

For every integer `n ≥ 0`, every `δ > 0` and every (not necessarily measurable) set
`A ⊆ ℝⁿ`: `Lⁿ(A) = Hⁿ(A) = Hⁿ_δ(A)`.  Here `Lⁿ` is Lebesgue outer measure (`volume` on
`EuclideanSpace ℝ (Fin n)`), and `Hⁿ`, `Hⁿ_δ` are Simon's normalized Hausdorff measure and
its size-`δ` approximation (2.1), (2.2) for the Euclidean metric. -/
def LebesgueEqHausdorff : Prop :=
  ∀ (n : ℕ) (δ : ℝ), 0 < δ → ∀ A : Set (EuclideanSpace ℝ (Fin n)),
    volume A = simonHausdorffOuterMeasureReal (n : ℝ) A ∧
      simonHausdorffOuterMeasureReal (n : ℝ) A = simonHausdorffContent (n : ℝ) (ENNReal.ofReal δ) A

/-- **Isodiametric inequality.** Simon Ch. 1, Theorem 2.10 (p. 11).

For every `n ≥ 0` and every set `A ⊆ ℝⁿ` (no measurability assumed):
`Lⁿ(A) ≤ ω_n (diam A / 2)ⁿ`, where `ω_n = π^{n/2} / Γ(n/2 + 1)` is the volume of the unit
ball. -/
def IsodiametricInequality : Prop :=
  ∀ (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))),
    volume A ≤ realUnitBallVolume (n : ℝ) * (ediam A / 2) ^ n

/-! ## §3 Densities -/

/-- **Upper density comparison theorem.** Simon Ch. 1, Theorem 3.3 (p. 14).

Let `μ` be a Borel-regular measure on the metric space `X`, `n ≥ 0` real, `t ≥ 0`, and
`A₁ ⊆ A₂ ⊆ X` (not assumed measurable).  If `Θ^{*n}(μ, A₂, x) ≥ t` for all `x ∈ A₁`, then
`t · Hⁿ(A₁) ≤ μ(A₂)`. -/
def UpperDensityComparison : Prop :=
  ∀ (X : Type u) [MetricSpace X] (μ : OuterMeasure X), IsBorelRegularOuterMeasure μ →
    ∀ (n : ℝ), 0 ≤ n → ∀ (t : ℝ), 0 ≤ t → ∀ A₁ A₂ : Set X, A₁ ⊆ A₂ →
      (∀ x ∈ A₁, ENNReal.ofReal t ≤ dimensionalUpperDensity μ n A₂ x) →
      ENNReal.ofReal t * simonHausdorffOuterMeasureReal n A₁ ≤ μ A₂

/-- **Upper density theorem.** Simon Ch. 1, Theorem 3.6 (p. 16).

If `μ` is Borel regular on the metric space `X`, `n ≥ 0`, and `A ⊆ X` is `μ`-measurable with
`μ(A) < ∞`, then `Θ^{*n}(μ, A, x) = 0` for `Hⁿ`-a.e. `x ∈ X \ A`. -/
def UpperDensityTheorem : Prop :=
  ∀ (X : Type u) [MetricSpace X] (μ : OuterMeasure X), IsBorelRegularOuterMeasure μ →
    ∀ (n : ℝ), 0 ≤ n → ∀ A : Set X, μ.IsCaratheodory A → μ A < ∞ →
      ∀ᵐ x ∂simonHausdorffOuterMeasureReal (X := X) n, x ∉ A →
        dimensionalUpperDensity μ n A x = 0

/-- **Besicovitch covering lemma.** Simon Ch. 1, Lemma 3.12 (p. 18).

For each `n` there is `N = N(n)` such that: if `B` is any collection of closed balls in `ℝⁿ`
(a ball being given by its centre and its radius `> 0`) whose set of radii is bounded, and `A`
is the set of centres, then there are subcollections `B₁, …, B_N ⊆ B`, each pairwise disjoint
(or empty), with `A ⊆ ⋃ⱼ ⋃_{β ∈ Bⱼ} β`.  The number `N` depends only on `n`. -/
def BesicovitchCovering : Prop :=
  ∀ n : ℕ, ∃ N : ℕ, ∀ B : Set (EuclideanSpace ℝ (Fin n) × ℝ),
    (∀ b ∈ B, 0 < b.2) → BddAbove (Prod.snd '' B) →
    ∃ D : Fin N → Set (EuclideanSpace ℝ (Fin n) × ℝ),
      (∀ j, D j ⊆ B) ∧ (∀ j, (D j).PairwiseDisjoint (fun b => closedBall b.1 b.2)) ∧
      Prod.fst '' B ⊆ ⋃ j, ⋃ b ∈ D j, closedBall b.1 b.2

/-- **General density theorem.** Simon Ch. 1, Theorem 3.16 (p. 20).

Let `μ` be an open σ-finite Borel-regular measure on the metric space `X` with the Symmetric
Vitali Property, and `A ⊆ X` `μ`-measurable.  Then
`lim_{ρ ↓ 0} μ(A ∩ B_ρ(x)) / μ(B_ρ(x))` equals `1` for `μ`-a.e. `x ∈ A` and `0` for `μ`-a.e.
`x ∈ X \ A`. -/
def GeneralDensityTheorem : Prop :=
  ∀ (X : Type u) [MetricSpace X] (μ : OuterMeasure X),
    IsBorelRegularOuterMeasure μ → IsOpenSigmaFinite μ → HasSymmetricVitaliProperty μ →
    ∀ A : Set X, μ.IsCaratheodory A →
      (∀ᵐ x ∂μ, x ∈ A → Tendsto (fun ρ : ℝ => μ (A ∩ closedBall x ρ) / μ (closedBall x ρ))
        (𝓝[>] 0) (𝓝 1)) ∧
      (∀ᵐ x ∂μ, x ∉ A → Tendsto (fun ρ : ℝ => μ (A ∩ closedBall x ρ) / μ (closedBall x ρ))
        (𝓝[>] 0) (𝓝 0))

/-- **Lebesgue differentiation theorem.** Simon Ch. 1, Corollary 3.17 (p. 20).

Let `X`, `μ` be as in 3.16 (open σ-finite, Borel regular, Symmetric Vitali Property) and let
`f : X → ℝ` be locally `μ`-integrable, i.e. `f` is `μ`-measurable and every `x ∈ X` has some
`ρ > 0` with `∫_{B_ρ(x)} |f| dμ < ∞`.  Then
`lim_{ρ ↓ 0} μ(B_ρ(x))⁻¹ ∫_{B_ρ(x)} f dμ = f(x)` for `μ`-a.e. `x ∈ X`. -/
def LebesgueDifferentiation : Prop :=
  ∀ (X : Type u) [MetricSpace X] (μ : OuterMeasure X),
    IsBorelRegularOuterMeasure μ → IsOpenSigmaFinite μ → HasSymmetricVitaliProperty μ →
    ∀ f : X → ℝ, Measurable[μ.caratheodory] f →
      (∀ x : X, ∃ ρ > 0, ∫⁻ y in closedBall x ρ, ENNReal.ofReal |f y| ∂caratheodoryMeasure μ < ∞) →
      ∀ᵐ x ∂μ, Tendsto
        (fun ρ : ℝ => (μ (closedBall x ρ)).toReal⁻¹ * ∫ y in closedBall x ρ, f y ∂caratheodoryMeasure μ)
        (𝓝[>] 0) (𝓝 (f x))

/-- **Radon–Nikodym theorem via densities.** Simon Ch. 1, Theorem 3.24 (pp. 24–25).

Let `μ, μ₀` be open σ-finite Borel-regular measures on the metric space `X`, `μ₀` with the
Symmetric Vitali Property.  Write `Θ(x) = Θ^{*μ₀}(μ, x)` for the upper density (3.9).
* (preliminary, from 3.22/3.23(ii)) the density `Θ^{μ₀}(μ, x) = lim_{ρ↓0} μ(B_ρ(x))/μ₀(B_ρ(x))`
  exists and equals `Θ(x)` for `μ₀`-a.e. `x`, so `Θ` is the integrand of the book;
* (i) if `μ ≪ μ₀` (`μ₀(E) = 0 ⇒ μ(E) = 0` for all `E ⊆ X`), then `μ(A) = ∫_A Θ dμ₀` for every
  Borel `A`;
* (ii) in general there is a Borel set `Z` with `μ₀(Z) = 0` and
  `μ(A) = ∫_A Θ dμ₀ + (μ ⌞ Z)(A)` for every Borel `A`, where `(μ ⌞ Z)(A) = μ(Z ∩ A)` (1.12);
* (iii) if `μ` also has the Symmetric Vitali Property, then (ii) holds with
  `Z = {x : Θ^{μ₀}(μ, x) = ∞}` (the set where the ratio tends to `∞`), and `μ₀(Z) = 0`. -/
def RadonNikodymTheorem : Prop :=
  ∀ (X : Type u) [MetricSpace X] (μ μ₀ : OuterMeasure X),
    IsBorelRegularOuterMeasure μ → IsOpenSigmaFinite μ →
    IsBorelRegularOuterMeasure μ₀ → IsOpenSigmaFinite μ₀ → HasSymmetricVitaliProperty μ₀ →
    (∀ᵐ x ∂μ₀, Tendsto (fun ρ : ℝ => μ (closedBall x ρ) / μ₀ (closedBall x ρ)) (𝓝[>] 0)
      (𝓝 (outerRelativeUpperDensity μ μ₀ x))) ∧
    ((∀ E : Set X, μ₀ E = 0 → μ E = 0) →
      ∀ A : Set X, MeasurableSet[borel X] A →
        μ A = ∫⁻ x in A, outerRelativeUpperDensity μ μ₀ x ∂caratheodoryMeasure μ₀) ∧
    (∃ Z : Set X, MeasurableSet[borel X] Z ∧ μ₀ Z = 0 ∧
      ∀ A : Set X, MeasurableSet[borel X] A →
        μ A = (∫⁻ x in A, outerRelativeUpperDensity μ μ₀ x ∂caratheodoryMeasure μ₀) + μ (Z ∩ A)) ∧
    (HasSymmetricVitaliProperty μ →
      μ₀ {x | Tendsto (fun ρ : ℝ => μ (closedBall x ρ) / μ₀ (closedBall x ρ)) (𝓝[>] 0) (𝓝 ∞)} = 0 ∧
      ∀ A : Set X, MeasurableSet[borel X] A →
        μ A = (∫⁻ x in A, outerRelativeUpperDensity μ μ₀ x ∂caratheodoryMeasure μ₀) +
          μ ({x | Tendsto (fun ρ : ℝ => μ (closedBall x ρ) / μ₀ (closedBall x ρ)) (𝓝[>] 0)
            (𝓝 ∞)} ∩ A))

/-- **Density bounds for Hausdorff measure.** Simon Ch. 1, Theorem 3.26 (p. 26).

Let `X` be a metric space, `n ≥ 0` real, and `A ⊆ X` an `Hⁿ`-measurable set.
(1) If `Hⁿ(A) < ∞`, then `Θ^{*n}(Hⁿ, A, x) ≤ 1` for `Hⁿ`-a.e. `x ∈ A`.
(2) If `Hⁿ_δ(A) < ∞` for each `δ > 0`, then `Θ^{*n}(Hⁿ_∞, A, x) ≥ 2⁻ⁿ` for `Hⁿ`-a.e.
`x ∈ A`, where `Hⁿ_∞` is the size-`∞` approximation (2.2) with `δ = ∞`. -/
def HausdorffDensityBounds : Prop :=
  ∀ (X : Type u) [MetricSpace X] (n : ℝ), 0 ≤ n → ∀ A : Set X,
    (simonHausdorffOuterMeasureReal n).IsCaratheodory A →
    (simonHausdorffOuterMeasureReal n A < ∞ →
      ∀ᵐ x ∂simonHausdorffOuterMeasureReal (X := X) n, x ∈ A →
        dimensionalUpperDensity (simonHausdorffOuterMeasureReal n) n A x ≤ 1) ∧
    ((∀ δ : ℝ, 0 < δ → simonHausdorffContent n (ENNReal.ofReal δ) A < ∞) →
      ∀ᵐ x ∂simonHausdorffOuterMeasureReal (X := X) n, x ∈ A →
        (2 : ℝ≥0∞) ^ (-n) ≤ dimensionalUpperDensity (simonHausdorffContentOuter n ∞) n A x)

/-! ## §4 Radon measures, representation theorem -/

/-- **Riesz representation for non-negative functionals.** Simon Ch. 1, Theorem 4.12 (p. 33).

Let `X` be a locally compact Hausdorff space and `λ : K₊ → [0, ∞)` additive and positively
homogeneous on the cone `K₊` of non-negative continuous compactly supported functions
(i.e. an `ℝ≥0`-linear map `C_c(X, ℝ≥0) → ℝ≥0`).  Then there is a Radon measure `μ` on `X`
(Def. 4.6) with `λ(f) = ∫_X f dμ` for all `f ∈ K₊`. -/
def RieszPositive : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (Λ : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0),
    ∃ μ : OuterMeasure X, IsRadonOuterMeasure μ ∧
      ∀ f : C_c(X, ℝ≥0), (Λ f : ℝ) = ∫ x, (f x : ℝ) ∂caratheodoryMeasure μ

/-- **Riesz representation theorem (vector-valued).** Simon Ch. 1, Theorem 4.14 (p. 35).

Let `X` be a locally compact Hausdorff space, `H` a finite-dimensional real Hilbert space, and
`L : C_c(X; H) → ℝ` linear with `sup {L(f) : |f| ≤ 1, spt f ⊆ K} < ∞` for every compact
`K ⊆ X`.  Then there are a Radon measure `μ` on `X` and a `μ`-measurable `ν : X → H` with
`|ν| = 1` `μ`-a.e. and `L(f) = ∫_X ⟨f, ν⟩ dμ` for all `f ∈ C_c(X; H)`. -/
def RieszVector : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (L : C_c(X, H) →ₗ[ℝ] ℝ),
    (∀ K : Set X, IsCompact K →
      BddAbove (L '' {f : C_c(X, H) | (∀ x, ‖f x‖ ≤ 1) ∧ tsupport f ⊆ K})) →
    ∃ μ : OuterMeasure X, IsRadonOuterMeasure μ ∧ ∃ ν : X → H,
      Measurable[μ.caratheodory, borel H] ν ∧ (∀ᵐ x ∂μ, ‖ν x‖ = 1) ∧
      ∀ f : C_c(X, H), L f = ∫ x, inner ℝ (f x) (ν x) ∂caratheodoryMeasure μ

/-- **Compactness theorem for Radon measures (corrected).** Simon Ch. 1, Theorem 4.16 (p. 37).

Let `X` be a locally compact Hausdorff space which is **second countable** (equivalently, a
locally compact separable metrizable space; e.g. `ℝᴺ`, an open subset of `ℝᴺ`, or `Gₙ(U)`),
and let `(μ_k)` be a sequence of Radon measures on `X` with `sup_k μ_k(K) < ∞` for each
compact `K ⊆ X`.  Then there are a subsequence `(μ_{k'})` and a Radon measure `μ` on `X` with
`lim_{k'} ∫ f dμ_{k'} = ∫ f dμ` for every continuous compactly supported `f : X → ℝ`.

**Erratum.** The book assumes only that `X` is locally compact, σ-compact and Hausdorff; this
is false (the proof's use of Alaoglu yields a subnet, not a subsequence): on the compact
Hausdorff space `{0,1}^{𝒫(ℕ)}` the Dirac masses at `x_k = (𝟙[k ∈ S])_S` have no vaguely
convergent subsequence (`Poincare.SimonGMT.Chapter01.simon_theorem_4_16_counterexample`).
Second countability (implying σ-compactness) is the standard correction, and matches the
standing assumption "X is a locally compact, separable metric space" announced for §4 on p. 1. -/
def RadonCompactness : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (μ : ℕ → OuterMeasure X),
    (∀ k, IsRadonOuterMeasure (μ k)) →
    (∀ K : Set X, IsCompact K → ⨆ k, μ k K < ∞) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ μlim : OuterMeasure X, IsRadonOuterMeasure μlim ∧
      ∀ f : C_c(X, ℝ), Tendsto (fun k => ∫ x, f x ∂caratheodoryMeasure (μ (φ k))) atTop
        (𝓝 (∫ x, f x ∂caratheodoryMeasure μlim))

/-- The headline results of Simon, *Introduction to GMT*, Chapter 1 (pp. 1–38). -/
theorem main_theorem : CaratheodoryCriterion ∧ BorelRegularApproximation ∧ LusinTheorem ∧ LebesgueEqHausdorff ∧ IsodiametricInequality ∧ UpperDensityComparison ∧ UpperDensityTheorem ∧ BesicovitchCovering ∧ GeneralDensityTheorem ∧ LebesgueDifferentiation ∧ RadonNikodymTheorem ∧ HausdorffDensityBounds ∧ RieszPositive ∧ RieszVector ∧ RadonCompactness := by sorry

end GMT.Ch01
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `accepted`.

# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.riesz_vector-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

PROOF OF `RieszVector` (Simon, Ch. 1, Lemma 4.7, Theorem 4.10, Theorem 4.14; printed proofs, transcribed and completed; the L¹-duality step is localized to compact sets because a Radon measure on a general locally compact Hausdorff space need not be σ-finite).

Statement. Let X be a locally compact Hausdorff space, H a finite-dimensional real inner product space, and L : C_c(X; H) → ℝ linear such that for every compact K ⊆ X the set {L(f) : f ∈ C_c(X; H), |f(x)| ≤ 1 for all x, spt f ⊆ K} is bounded above. Then there are a Radon outer measure μ on X (Def. 4.6) and a μ-measurable ν : X → H (preimages of Borel sets are μ-measurable) with |ν| = 1 μ-a.e. and L(f) = ∫_X ⟨f, ν⟩ dμ for all f ∈ C_c(X; H) (integrals with respect to μ on the μ-measurable sets; Lean `caratheodoryMeasure μ`).

Dependency. Theorem 4.12 = sibling `riesz_positive` (Lean `Submission.riesz_positive : RieszPositive`).
Standard facts: Lemma 1.6 / Remark 1.7 (Carathéodory); Urysohn's lemma for locally compact Hausdorff spaces (Simon 4.4: for K compact ⊆ V open there is f ∈ C_c(X, [0, 1]) with f ≡ 1 near K and spt f ⊆ V); disjoint compact sets have disjoint open neighbourhoods (Simon 4.1); every compact set has an open neighbourhood with compact closure; simple functions are dense in L¹; for a finite measure space, every bounded linear functional on L¹ is given by a bounded measurable function (L¹–L^∞ duality); Zorn's lemma.

STEP 0 (reductions). Let n := dim H. If n = 0 then H = {0}, C_c(X; H) = {0}, L = 0, and μ := 0 (the zero outer measure, which satisfies (R1)–(R3)) with ν := 0 works: L(f) = 0 = ∫⟨f, ν⟩ dμ, ν is measurable, and “|ν| = 1 μ-a.e.” holds because μ = 0. Assume n ≥ 1. An orthonormal basis e₁, …, e_n of H gives a linear isometry H ≅ ℝⁿ preserving inner products; transporting L, the hypothesis and the conclusion along it, we may assume H = ℝⁿ (printed: “By using an orthonormal basis for H, it suffices to prove the theorem with H = ℝⁿ”). |·| is the Euclidean norm. K₊ := C_c(X, [0, ∞)).

STEP 1 (the positive functional; printed). For f ∈ K₊ let λ(f) := sup{L(ω) : ω ∈ C_c(X; ℝⁿ), |ω| ≤ f}.
 • 0 ≤ λ(f) < ∞: ω = 0 is admissible; if |ω| ≤ f then spt ω ⊆ spt f =: K, and if s := sup f > 0 then ω/s is admissible in the hypothesis for K, so L(ω) ≤ s·M_K with M_K an upper bound (if s = 0 then ω = 0).
 • λ(cf) = cλ(f) for c ≥ 0 (c = 0: only ω = 0; c > 0: ω ↦ cω is a bijection between the admissible sets).
 • λ(f + g) ≤ λ(f) + λ(g): given ω with |ω| ≤ f + g let ω₁ := fω/(f + g), ω₂ := gω/(f + g) where f + g > 0, and ω₁ = ω₂ := 0 where f + g = 0. Then ω₁ + ω₂ = ω, |ω₁| ≤ f, |ω₂| ≤ g, and ω₁, ω₂ ∈ C_c(X; ℝⁿ): they are continuous where f + g > 0, and at a point x₀ with f(x₀) + g(x₀) = 0 we have |ω_i(x)| ≤ |ω(x)| ≤ f(x) + g(x) → 0 as x → x₀; their supports lie in spt ω. So L(ω) = L(ω₁) + L(ω₂) ≤ λ(f) + λ(g).
 • λ(f + g) ≥ λ(f) + λ(g): if |ω₁| ≤ f and |ω₂| ≤ g then |ω₁ + ω₂| ≤ f + g, so L(ω₁) + L(ω₂) ≤ λ(f + g).
 Thus λ is an ℝ≥0-linear map K₊ → [0, ∞), and Theorem 4.12 (sibling `riesz_positive`) gives a Radon outer measure μ on X with
  (**) sup{L(ω) : |ω| ≤ f} = λ(f) = ∫_X f dμ for all f ∈ K₊.
 Consequently, for ω ∈ C_c(X; ℝⁿ): |ω| ∈ K₊ and L(ω) ≤ λ(|ω|), L(−ω) ≤ λ(|ω|), i.e.
  (†) |L(ω)| ≤ ∫_X |ω| dμ.

STEP 2 (Lemma 4.7; printed). If A is μ-measurable with μ(A) < ∞ then μ(A) = sup{μ(K) : K ⊆ A compact}. [Given ε > 0 choose open U ⊇ A with μ(U ∖ A) < ε (R2), compact K ⊆ U with μ(U ∖ K) < ε (R3), and open W ⊇ U ∖ A with μ(W) < 2ε (R2). Then K ∖ W is compact, K ∖ W ⊆ U ∖ W ⊆ A, and μ(A ∖ (K ∖ W)) ≤ μ(U ∖ K) + μ(W) < 3ε.]

STEP 3 (Theorem 4.10 for p = 1; printed). C_c(X) is dense in L¹(μ), and hence (componentwise) C_c(X; ℝⁿ) is dense in L¹(μ; ℝⁿ). [Let f ∈ L¹(μ), ε > 0. Choose a simple φ = Σ_{j=1}^N a_j1_{A_j} with distinct a_j ≠ 0 and pairwise disjoint μ-measurable A_j with ‖f − φ‖₁ < ε; then μ(A_j) < ∞. Let M > max|a_j| and η := ε/(2MN). By Step 2 choose compact K_j ⊆ A_j with μ(A_j ∖ K_j) < η and by (R2) open U_j ⊇ K_j with μ(U_j ∖ K_j) < η; replacing U_j by U_j ∩ U'_j with pairwise disjoint open U'_j ⊇ K_j (Simon 4.1), the U_j are pairwise disjoint. By Urysohn choose g_j ∈ C_c(X) with g_j = a_j on K_j, |g_j| ≤ |a_j|, spt g_j ⊆ U_j, and put g := Σ_jg_j. Then g = φ on ⋃K_j, |φ − g| ≤ 2M, and φ − g vanishes off ⋃_j((U_j ∖ K_j) ∪ (A_j ∖ K_j)), so ‖φ − g‖₁ ≤ 2M·Σ_j2η = 2ε and ‖f − g‖₁ < 3ε.]

STEP 4 (extension of L to L¹). Each ω ∈ C_c(X; ℝⁿ) is μ-integrable (bounded, μ(spt ω) < ∞). By (†), L(ω) depends only on the class of ω in L¹(μ; ℝⁿ) and |L(ω) − L(ω')| ≤ ‖ω − ω'‖₁. By Step 3, L extends uniquely to a linear functional L̄ on L¹(μ; ℝⁿ) with |L̄(F)| ≤ ‖F‖₁ (printed: “L_j(f) := L(fe_j) extends to a bounded linear functional on L¹(μ)”).

STEP 5 (local duality; printed “by the Riesz representation theorem for L¹(μ)”, applied on sets of finite measure). Let E be μ-measurable with μ(E) < ∞. For i = 1, …, n the map h ↦ L̄(1_E h e_i) is a linear functional on L¹(μ⌞E) of norm ≤ 1; since μ⌞E is finite, L¹–L^∞ duality gives a bounded μ-measurable ν_{E,i} (zero off E) with L̄(1_E h e_i) = ∫_E h ν_{E,i} dμ. Put ν_E := (ν_{E,1}, …, ν_{E,n}); then L̄(1_E G) = ∫_E ⟨G, ν_E⟩ dμ for all G ∈ L¹(μ; ℝⁿ).
 • |ν_E| ≤ 1 μ-a.e. on E: for η > 0 let S := {x ∈ E : |ν_E(x)| > 1 + η} and G := 1_S ν_E/|ν_E|; then (1 + η)μ(S) ≤ ∫_S|ν_E| dμ = L̄(1_E G) ≤ ‖G‖₁ = μ(S), so μ(S) = 0.
 • Consistency: if E ⊆ E' both have finite measure, then for bounded measurable G vanishing off E, ∫_E⟨G, ν_E⟩ dμ = L̄(1_E G) = L̄(1_{E'}G) = ∫_E⟨G, ν_{E'}⟩ dμ; with G := 1_E(ν_E − ν_{E'}) this gives ν_E = ν_{E'} μ-a.e. on E. Consequently, for any two compact F, F', ν_F = ν_{F∪F'} = ν_{F'} μ-a.e. on F ∩ F'.

STEP 6 (decomposition of a Radon measure into compact pieces).
 6.1 For compact F let S_F := {x ∈ F : μ(F ∩ O) > 0 for every open O ∋ x} (the support of μ⌞F). S_F is closed (if x ∈ F ∖ S_F, some open O ∋ x has μ(F ∩ O) = 0, and then O ∩ S_F = ∅), hence compact, and μ(F ∖ S_F) = 0: F ∖ S_F is μ-measurable with finite measure, every compact C ⊆ F ∖ S_F is covered by finitely many open O with μ(F ∩ O) = 0, so μ(C) = 0, and Step 2 gives μ(F ∖ S_F) = 0.
 6.2 By Zorn's lemma there is a family 𝓕 of compact sets, maximal among families with μ(F) > 0 for F ∈ 𝓕 and μ(F ∩ F') = 0 for distinct F, F' ∈ 𝓕 (the union of a chain of such families is such a family).
 6.3 For compact K, 𝓕_K := {F ∈ 𝓕 : μ(K ∩ F) > 0} is countable: for distinct F₁, …, F_N ∈ 𝓕 the sets F_i' := F_i ∖ ⋃_{l≠i}F_l are disjoint and μ(F_i ∖ F_i') = 0, so Σ_iμ(K ∩ F_i) = μ(K ∩ ⋃F_i') ≤ μ(K) < ∞; hence at most m·μ(K) members have μ(K ∩ F) > 1/m.
 6.4 For compact K, μ(K ∖ ⋃_{F∈𝓕_K}F) = 0: otherwise K' := K ∖ ⋃_{𝓕_K}F (μ-measurable, a countable union being removed) has 0 < μ(K') < ∞, and Step 2 gives a compact C ⊆ K' with μ(C) > 0; C is disjoint from every F ∈ 𝓕_K and μ(C ∩ F) ≤ μ(K ∩ F) = 0 for F ∈ 𝓕 ∖ 𝓕_K; C ∉ 𝓕 (else C ∈ 𝓕_K, but C ∩ C = C ≠ ∅); so 𝓕 ∪ {C} contradicts maximality.
 6.5 For compact K, 𝓕'_K := {F ∈ 𝓕 : S_F ∩ K ≠ ∅} is countable: choose an open O ⊇ K with Ō compact; if x ∈ S_F ∩ K then μ(F ∩ O) > 0, so μ(F ∩ Ō) > 0 and F ∈ 𝓕_{Ō}, which is countable by 6.3.
 6.6 For F ∈ 𝓕 let P_F := S_F ∖ ⋃_{F'∈𝓕, F'≠F}S_{F'}. The P_F are pairwise disjoint; for compact K, P_F ∩ K = ∅ unless F ∈ 𝓕'_K, and P_F ∩ K = (S_F ∩ K) ∖ ⋃_{F'∈𝓕'_K, F'≠F}S_{F'} is a Borel set (6.5). Moreover μ(K ∖ ⋃_{F∈𝓕'_K}P_F) = 0: a point x ∈ K in no P_F either lies outside ⋃_{F∈𝓕_K}F (a null set by 6.4), or lies in some F ∈ 𝓕_K but not in S_F (a subset of the null set F ∖ S_F, 6.1), or lies in S_F ∩ S_{F'} ⊆ F ∩ F' for some distinct F, F' ∈ 𝓕'_K (then F, F' ∈ 𝓕'_K since x ∈ K, and μ(F ∩ F') = 0); these are countably many null sets.

STEP 7 (gluing the local fields). Define ν : X → ℝⁿ by ν := ν_F on P_F (F ∈ 𝓕) and ν := e₁ on X ∖ ⋃_{F∈𝓕}P_F.
 7.1 (Localization principle.) A set T ⊆ X is μ-measurable if T ∩ K is μ-measurable for every compact K. [Let Y ⊆ X with μ(Y) < ∞ and ε > 0; by (R2) take open U ⊇ Y with μ(U) < ∞, and by (R3) (U is μ-measurable) a compact K ⊆ U with μ(U ∖ K) < ε. Since T ∩ K is μ-measurable, μ(Y ∩ T) + μ(Y ∖ T) ≤ μ(Y ∩ K ∩ T) + μ((Y ∩ K) ∖ T) + 2μ(Y ∖ K) ≤ μ(Y ∩ K) + 2ε ≤ μ(Y) + 2ε; conclude by Remark 1.3.]
 7.2 ν is μ-measurable: for a Borel G ⊆ ℝⁿ and compact K, ν^{−1}(G) ∩ K = ⋃_{F∈𝓕'_K}(ν_F^{−1}(G) ∩ P_F ∩ K) ∪ (either K ∖ ⋃_{F∈𝓕'_K}P_F or ∅, according as e₁ ∈ G or not), a countable union of μ-measurable sets; apply 7.1.
 7.3 For compact K, ν = ν_K μ-a.e. on K: on K ∩ P_F (F ∈ 𝓕'_K), ν = ν_F = ν_K μ-a.e. (Step 5, consistency on K ∩ F), and K ∖ ⋃_{F∈𝓕'_K}P_F is null (6.6). In particular |ν| ≤ 1 μ-a.e. on each compact set.

STEP 8 (representation; printed (*)). For ω ∈ C_c(X; ℝⁿ) let K := spt ω. Then ω = 1_Kω and, by Steps 4, 5 and 7.3,
  L(ω) = L̄(1_Kω) = ∫_K⟨ω, ν_K⟩ dμ = ∫_K⟨ω, ν⟩ dμ = ∫_X⟨ω, ν⟩ dμ.

STEP 9 (|ν| = 1 locally a.e.; printed argument). Let f ∈ K₊ and K := spt f.
 (i) For ω with |ω| ≤ f, Cauchy–Schwarz gives L(ω) = ∫⟨ω, ν⟩ dμ ≤ ∫ f|ν| dμ; by (**), ∫f dμ ≤ ∫f|ν| dμ.
 (ii) Let ν̂ := ν/|ν| where ν ≠ 0 and ν̂ := 0 elsewhere. 1_Kν̂ ∈ L¹(μ; ℝⁿ), so by Step 3 there are g_k ∈ C_c(X; ℝⁿ) with ∫|g_k − 1_Kν̂| dμ → 0. Let R be the nearest-point retraction of ℝⁿ onto the closed unit ball (R(y) = y for |y| ≤ 1, y/|y| otherwise); it is continuous, R(0) = 0, and |R(y) − v| ≤ |y − v| whenever |v| ≤ 1. So ĝ_k := R ∘ g_k ∈ C_c(X; ℝⁿ), |fĝ_k| ≤ f, and |ĝ_k − ν̂| ≤ |g_k − ν̂| on K. Hence, using |ν| ≤ 1 a.e. on K,
  |L(fĝ_k) − ∫f|ν| dμ| = |∫_K f⟨ĝ_k − ν̂, ν⟩ dμ| ≤ (sup f)∫|g_k − 1_Kν̂| dμ → 0,
 and L(fĝ_k) ≤ λ(f) = ∫f dμ by (**). So ∫f|ν| dμ ≤ ∫f dμ.
 Thus ∫f(1 − |ν|) dμ = 0 for every f ∈ K₊, with f(1 − |ν|) ≥ 0 a.e. For compact K choose (Urysohn) f ∈ K₊ with f ≡ 1 on K; then 1 − |ν| = 0 μ-a.e. on K. So |ν| = 1 μ-a.e. on every compact set.

STEP 10 (a field of norm exactly one). Let ν' := ν on {|ν| = 1} and ν' := e₁ on {|ν| ≠ 1}. Then ν' is μ-measurable ({|ν| = 1} is μ-measurable by 7.2), |ν'(x)| = 1 for every x ∈ X — so in particular |ν'| = 1 μ-a.e., i.e. μ({|ν'| ≠ 1}) = μ(∅) = 0 — and ν' = ν μ-a.e. on each compact set (Step 9), so Step 8 gives L(ω) = ∫_{spt ω}⟨ω, ν'⟩ dμ = ∫_X⟨ω, ν'⟩ dμ for all ω ∈ C_c(X; ℝⁿ). (Replacing ν by ν' avoids asserting that a set which is null on every compact set is globally null, which may fail for non-σ-finite Radon measures.)

Conclusion. μ (Step 1) is a Radon outer measure and ν' : X → ℝⁿ ≅ H is μ-measurable with |ν'| = 1 μ-a.e. and L(f) = ∫_X⟨f, ν'⟩ dμ for every f ∈ C_c(X; H). ∎

Formalization note (non-binding): `Poincare.SimonGMT.Chapter01.simon_theorem_4_14` (Chapter01/RadonPolarRepresentation.lean) proves exactly this statement: its hypothesis `IsLocallyBoundedCcFunctional L` unfolds to the contract's bounded-above hypothesis, its measure `hμ.toCaratheodoryMeasure` is by definition `@OuterMeasure.toMeasure X μ.caratheodory μ le_rfl` (= `caratheodoryMeasure μ`), and its a.e. statement for `hμ.toCaratheodoryMeasure` transfers to μ because both agree on all sets (`IsRadonOuterMeasure.toCaratheodoryMeasure_apply_all`).

## Key steps

1. Reduce to H = ℝⁿ by an orthonormal basis; n = 0 is handled by μ = 0.
2. λ(f) := sup{L(ω) : |ω| ≤ f} is additive and positively homogeneous; Theorem 4.12 gives a Radon μ with λ(f) = ∫f dμ, hence |L(ω)| ≤ ∫|ω| dμ.
3. Lemma 4.7 and Theorem 4.10 (C_c dense in L¹); extend L to L̄ on L¹(μ; ℝⁿ) with norm ≤ 1.
4. Local L¹–L^∞ duality on each set of finite measure gives consistent fields ν_E with |ν_E| ≤ 1.
5. A maximal almost-disjoint family of compacts, with supports S_F and cores P_F, glues the ν_F into one ν, measurable by the compact localization principle.
6. Representation L(ω) = ∫⟨ω, ν⟩ dμ; |ν| = 1 locally a.e. via Cauchy–Schwarz and approximants composed with the radial retraction.
7. Replace non-unit values by e₁: |ν'| = 1 everywhere, with the same representation and measurability.

## Reference use

### local-project

Queries:
- `cat manifest.json (snapshot root e8e26216f05cbb4e)`
- `rg -n '^def (CaratheodoryCriterion|BorelRegularApproximation|LusinTheorem|LebesgueEqHausdorff|IsodiametricInequality|UpperDensityComparison|UpperDensityTheorem|BesicovitchCovering|GeneralDensityTheorem|LebesgueDifferentiation|RadonNikodymTheorem|HausdorffDensityBounds|RieszPositive|RieszVector|RadonCompactness)|^theorem main_theorem|^universe|^open|^namespace' project/GMT/Ch01/Contract.lean`
- `cmp project/GMT/Ch01/Contract.lean project/GMT/Ch01/Submission.lean`
- `rg -n -c Poincare.SimonGMT project mathlib/Mathlib`
- `rg -n 'theorem simon_theorem' . (no match: SimonGMT is not in the snapshot)`
- `rg -n 'theorem borel_le_caratheodory|def IsMetric' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n '^theorem exist_disjoint_covering_families|^theorem isEmpty_satelliteConfig_multiplicity|def multiplicity' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `rg -n 'theorem integral_rieszMeasure|instance rieszMeasure_regular|instance regular_rieszMeasure' mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/NNReal.lean mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `rg -n 'theorem volume_ball|theorem volume_closedBall' mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `rg -n 'def IsCaratheodory|def caratheodory |theorem isCaratheodory_iff' mathlib/Mathlib/MeasureTheory/OuterMeasure/Caratheodory.lean`
- `rg -n 'theorem toMeasure_apply|theorem le_toMeasure_apply' mathlib/Mathlib/MeasureTheory/Measure/OuterMeasure.lean; rg -n 'theorem ae_iff' mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `rg -n 'theorem setLIntegral_trim_ae|theorem lintegral_trim_ae' mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean; rg -n 'theorem integral_trim_ae|theorem integral_trim ' mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean; rg -n 'theorem restrict_trim' mathlib/Mathlib/MeasureTheory/Measure/Trim.lean`
- `rg -n 'sigmaCompactSpace_of_locallyCompact_secondCountable|noncomputable def choice|theorem exists_superset_of_isCompact' mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `rg -n '^instance|^theorem' mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean; rg -n 'metrizableSpace_of_t3_secondCountable' mathlib/Mathlib/Topology/Metrizable/Urysohn.lean; rg -n 'theorem exists_compact_superset' mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean`
- `rg -n 'theorem exists_continuous_one_zero_of_isCompact' mathlib/Mathlib/Topology/UrysohnsLemma.lean; rg -n 'theorem IsCompact.tendsto_subseq' mathlib/Mathlib/Topology/Sequences.lean`
- `rg -n 'theorem tendsto_iff_forall_integral_tendsto' mathlib/Mathlib/MeasureTheory/Measure/FiniteMeasure.lean; rg -n -F 'CompactSpace (ProbabilityMeasure' mathlib/Mathlib/MeasureTheory/Measure/Prokhorov.lean; rg -n 'theorem measure_iUnion_le|theorem measure_mono_null' mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `test -f on every cited snapshot file (all present); cmp of cited Mathlib files against lake-packages-25730c7c/mathlib (identical)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/GMT/Ch01/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/GMT/Ch01/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/GMT/Ch01/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/PROBLEM.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/lakefile.toml`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/NNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/OuterMeasure/Caratheodory.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Measure/OuterMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Measure/Trim.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/UrysohnsLemma.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/Metrizable/Urysohn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Measure/FiniteMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Measure/Prokhorov.lean`

The manifest pins project ec1c322 and Mathlib 25730c7c. In the snapshot, project/GMT/Ch01/Contract.lean is byte-identical to Submission.lean. It defines exactly the fifteen Props CaratheodoryCriterion … RadonCompactness (lines 88–303), with main_theorem at line 313, inside namespace GMT.Ch01 with `universe u v` (line 69) and the opens at lines 63–65. Each child lean_statement is one of these Props or a conjunction of two of them; the two merged children with universe parameters share the declared universe u, which the comparator replays from that scope. README.md maps the conjuncts to SimonGMT theorems and documents the 4.16 erratum (second countability). That erratum is applied in radon_compactness. The snapshot contains no SimonGMT declarations: rg finds 'Poincare.SimonGMT' only as imports and opens in the project files, and 'theorem simon_theorem' has no match. The package is pinned in project/lake-manifest.json and lives outside the snapshot, so the children cite it only in non-binding formalization notes. The snapshot's Mathlib contains the facts those notes rely on:
- OuterMeasure.IsMetric and borel_le_caratheodory: Measure/Hausdorff.lean:137,161.
- Besicovitch.exist_disjoint_covering_families (Covering/Besicovitch.lean:455), multiplicity and isEmpty_satelliteConfig_multiplicity (BesicovitchVectorSpace.lean:98,488).
- NNRealRMK.integral_rieszMeasure and rieszMeasure_regular (RieszMarkovKakutani/NNReal.lean:47,66); the real RMK (Real.lean:345,357).
- EuclideanSpace.volume_ball and volume_closedBall: Lebesgue/VolumeOfBalls.lean:307,324.
- IsCaratheodory and the caratheodory σ-algebra: OuterMeasure/Caratheodory.lean:55,176,181.
- toMeasure_apply and le_toMeasure_apply (Measure/OuterMeasure.lean:46,50); ae_iff (OuterMeasure/AE.lean:134).
- setLIntegral_trim_ae (Integral/Lebesgue/Add.lean:490); integral_trim and integral_trim_ae (Bochner/Basic.lean:1301,1332); restrict_trim (Measure/Trim.lean:108).
- σ-compactness and compact exhaustions: SigmaCompact.lean:187,376,418.
- Urysohn's lemma: UrysohnsLemma.lean:404.
- Separability of C(X,Y): ContinuousMap/SecondCountableSpace.lean:108. Metrizability: Metrizable/Urysohn.lean:127.
- Compact supersets: LocallyCompact.lean:58. IsCompact.tendsto_subseq: Sequences.lean:298.
- Weak convergence and Prokhorov: FiniteMeasure.lean:727; Prokhorov.lean:176.
The cited Mathlib files are byte-identical to the packages used by the build. The mathematical arguments of the children are the printed proofs of the source and do not depend on these declarations.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: https://github.com/ZhengyangZhang06/gmt-formalize/pull/282

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
