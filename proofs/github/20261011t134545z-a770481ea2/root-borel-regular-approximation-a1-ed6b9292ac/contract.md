<!-- theorem-id: gmt-ch01/root.borel_regular_approximation-a1 -->

## Theorem `Submission.borel_regular_approximation`

For every topological space X in which every closed set is a countable intersection of open sets, and every outer measure μ on X that is Borel regular and open σ-finite (X = ⋃ V_n, V_n open, μ(V_n) < ∞): (1) μ(A) = inf{μ(U) : U ⊇ A open} for every A ⊆ X, and (2) μ(A) = sup{μ(C) : C ⊆ A closed} for every μ-measurable A ⊆ X.

Node: `root.borel_regular_approximation-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.borel_regular_approximation`

```lean
BorelRegularApproximation
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
- Child DAG node: `root.borel_regular_approximation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

PROOF OF `BorelRegularApproximation` (Simon, Ch. 1, Theorem 1.15; printed proof, transcribed and completed).

Statement. Let X be a topological space in which every closed set is a countable intersection of open sets, and let μ be an outer measure on X which is
 • Borel regular: every Borel set is μ-measurable, and every A ⊆ X has a Borel B ⊇ A with μ(B) = μ(A); and
 • open σ-finite (Def. 1.14): X = ⋃_{n} V_n with V_n open and μ(V_n) < ∞.
Then (1) μ(A) = inf{μ(U) : U open, U ⊇ A} for every A ⊆ X, and (2) μ(A) = sup{μ(C) : C closed, C ⊆ A} for every μ-measurable A ⊆ X.

Standard facts used (Carathéodory; Simon Lemma 1.6, Remark 1.7, (1.8), (1.9)): the μ-measurable sets form a σ-algebra M containing every μ-null set; μ is countably additive on M; for an increasing sequence in M, μ(⋃) = lim μ; for a decreasing sequence in M with finite first term, μ(⋂) = lim μ. In particular μ(U ∖ A) = μ(U) − μ(A) when A ⊆ U, A ∈ M, μ(A) < ∞.

Trivial halves. By monotonicity, inf{μ(U) : U ⊇ A open} ≥ μ(A) and sup{μ(C) : C ⊆ A closed} ≤ μ(A). Only the reverse inequalities need proof.

Step 0 (restriction to a Borel set; cf. the remarks after (1.12)). Let Y ⊆ X be Borel and μ⌞Y(A) := μ(Y ∩ A).
 (a) Every μ-measurable E is μ⌞Y-measurable: for S ⊆ X, μ⌞Y(S) = μ(S ∩ Y) = μ(S ∩ Y ∩ E) + μ((S ∩ Y) ∖ E) = μ⌞Y(S ∩ E) + μ⌞Y(S ∖ E).
 (b) μ⌞Y is Borel regular: Borel sets are μ⌞Y-measurable by (a); given A, take a Borel B₃ ⊇ A ∩ Y with μ(B₃) = μ(A ∩ Y); then B := B₃ ∪ (X ∖ Y) is Borel, B ⊇ A, and μ⌞Y(B) = μ(Y ∩ B₃) ≤ μ(B₃) = μ⌞Y(A).

PART I: the case μ(X) < ∞.

I.1 It suffices to prove (1) for Borel A: for arbitrary A choose a Borel B ⊇ A with μ(B) = μ(A); every open U ⊇ B contains A, so inf_{U⊇A} μ(U) ≤ inf_{U⊇B} μ(U) = μ(B) = μ(A).

I.2 For a Borel set A (finite case), (1) holds iff for every ε > 0 there is an open U ⊇ A with μ(U ∖ A) < ε (because μ(U) = μ(A) + μ(U ∖ A)). Let 𝒜 be the family of Borel sets A with this property. Every open set belongs to 𝒜 (take U = A).

I.3 𝒜 is closed under countable unions. Let A_j ∈ 𝒜 (j ≥ 1), ε > 0, and choose open U_j ⊇ A_j with μ(U_j ∖ A_j) < 2^{−j−1}ε. Then U := ⋃_j U_j is open, contains ⋃_k A_k, and U ∖ ⋃_k A_k ⊆ ⋃_j (U_j ∖ A_j), so μ(U ∖ ⋃_k A_k) ≤ ε/2 < ε.

I.4 𝒜 is closed under countable intersections. Let A_k ∈ 𝒜, A := ⋂_k A_k, ε > 0, and U_k as in I.3. Then (⋂_j U_j) ∖ A ⊆ ⋃_k (U_k ∖ A_k) (a point of ⋂_j U_j outside A lies outside some A_k but inside U_k), so μ((⋂_j U_j) ∖ A) ≤ ε/2. The Borel sets W_N := (U₁ ∩ ⋯ ∩ U_N) ∖ A decrease to (⋂_j U_j) ∖ A and μ(W₁) ≤ μ(X) < ∞, so by (1.9) μ(W_N) → μ((⋂_j U_j) ∖ A) ≤ ε/2. Hence for some N, U₁ ∩ ⋯ ∩ U_N is an open set containing A with μ((U₁ ∩ ⋯ ∩ U_N) ∖ A) < ε.

I.5 Every closed C belongs to 𝒜: by hypothesis C = ⋂_j G_j with G_j open, G_j ∈ 𝒜 (I.2), so C ∈ 𝒜 by I.4.

I.6 𝒜 contains every Borel set. Let 𝒜̃ := {A ∈ 𝒜 : X ∖ A ∈ 𝒜}. Then ∅, X ∈ 𝒜̃ (both are open and closed), 𝒜̃ is closed under complements by definition, and if A_j ∈ 𝒜̃ then ⋃_j A_j ∈ 𝒜 (I.3) and X ∖ ⋃_j A_j = ⋂_j (X ∖ A_j) ∈ 𝒜 (I.4), so ⋃_j A_j ∈ 𝒜̃. Thus 𝒜̃ is a σ-algebra. If C is closed then C ∈ 𝒜 (I.5) and X ∖ C ∈ 𝒜 (open), so C ∈ 𝒜̃. Since the Borel σ-algebra is generated by the closed sets, 𝒜̃ contains all Borel sets, hence so does 𝒜. With I.1 and I.2 this proves (1) in the finite case.

I.7 Proof of (2) in the finite case. Let A be μ-measurable and ε > 0. Apply (1) to X ∖ A: there is an open U ⊇ X ∖ A with μ(U) < μ(X ∖ A) + ε; since X ∖ A ∈ M has finite measure, μ(U ∖ (X ∖ A)) = μ(U) − μ(X ∖ A) < ε. Then C := X ∖ U is closed, C ⊆ A, and A ∖ C = A ∩ U = U ∖ (X ∖ A), so μ(A) = μ(C) + μ(A ∖ C) < μ(C) + ε (C is Borel, hence in M). Thus sup_{C⊆A closed} μ(C) ≥ μ(A).

PART II: the general (open σ-finite) case.

For each j put μ_j := μ⌞V_j. V_j is open, hence Borel, so by Step 0 μ_j is Borel regular and every μ-measurable set is μ_j-measurable; moreover μ_j(X) = μ(V_j) < ∞. The topological hypothesis on X is unchanged, so Part I applies to each μ_j.

II.1 Proof of (1). Let A ⊆ X and ε > 0; if μ(A) = ∞ there is nothing to prove (take U = X). Choose a Borel B ⊇ A with μ(B) = μ(A). By Part I (I.6, applied to μ_j and the Borel set B) there are open U_j ⊇ B with μ_j(U_j ∖ B) = μ(V_j ∩ U_j ∖ B) < 2^{−j−1}ε. Then U := ⋃_j (U_j ∩ V_j) is open; it contains B, since each x ∈ B lies in some V_j and in U_j; and U ∖ B ⊆ ⋃_j ((U_j ∩ V_j) ∖ B), so μ(U ∖ B) < ε. Hence μ(U) ≤ μ(B) + μ(U ∖ B) < μ(A) + ε, proving (1).

II.2 Proof of (2). Let A be μ-measurable and ε > 0. A is μ_j-measurable, so by I.7 for μ_j there is a closed C_j ⊆ A with μ_j(A ∖ C_j) = μ(V_j ∩ A ∖ C_j) < 2^{−j−1}ε. Since X = ⋃_j V_j,
  A ∖ ⋃_k C_k = ⋃_j (V_j ∩ A ∖ ⋃_k C_k) ⊆ ⋃_j (V_j ∩ A ∖ C_j), hence μ(A ∖ ⋃_k C_k) < ε.
Let D_N := C₁ ∪ ⋯ ∪ C_N: a closed subset of A; the D_N increase and lie in M.
 • If μ(A) = ∞: μ(A) ≤ μ(⋃_k C_k) + μ(A ∖ ⋃_k C_k) forces μ(⋃_k C_k) = ∞, and by (1.8) μ(D_N) → μ(⋃_k C_k) = ∞; so sup_{C⊆A closed} μ(C) = ∞ = μ(A).
 • If μ(A) < ∞: the sets A ∖ D_N ∈ M decrease to A ∖ ⋃_k C_k and have finite measure, so by (1.9) μ(A ∖ D_N) → μ(A ∖ ⋃_k C_k) < ε; for large N, μ(D_N) = μ(A) − μ(A ∖ D_N) > μ(A) − ε.
In both cases sup_{C⊆A closed} μ(C) ≥ μ(A), proving (2). ∎

Formalization note (non-binding): `Poincare.SimonGMT.Chapter01.IsBorelRegularOuterMeasure.simon_theorem_1_15` (Chapter01/ExactRegularity.lean) proves exactly (1) ∧ (2) under `IsBorelRegularOuterMeasure μ`, `IsOpenSigmaFinite μ` and `ClosedSetsAreGDelta X` (= ∀ ⦃C⦄, IsClosed C → IsGδ C, unfolded by `closedSetsAreGDelta_iff`); `IsCaratheodoryMeasurable μ A` is an abbreviation of `μ.IsCaratheodory A`.

## Key steps

1. Restriction to a Borel set Y: μ⌞Y is Borel regular and every μ-measurable set is μ⌞Y-measurable.
2. Finite case: reduce (1) to Borel A via Borel hulls; let 𝒜 be the Borel sets approximable from outside by open sets up to ε.
3. 𝒜 contains the open sets and is closed under countable unions and (via finite intersections and continuity from above) countable intersections, so it contains the closed (G_δ) sets.
4. 𝒜̃ = {A ∈ 𝒜 : X ∖ A ∈ 𝒜} is a σ-algebra containing the closed sets, so 𝒜 contains all Borel sets: (1) holds in the finite case.
5. (2) in the finite case follows by applying (1) to X ∖ A.
6. General case: apply the finite case to μ⌞V_j with errors 2^{−j−1}ε and recombine; in (2) treat μ(A) = ∞ and μ(A) < ∞ separately via (1.8), (1.9).

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

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
