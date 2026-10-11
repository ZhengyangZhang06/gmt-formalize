<!-- theorem-id: gmt-ch01/root.radon_nikodym_theorem-a1 -->

## Theorem `Submission.radon_nikodym_theorem`

For a metric space X and outer measures μ, μ₀ on X that are Borel regular and open σ-finite, μ₀ with the Symmetric Vitali Property, and Θ(x) := limsup_{ρ↓0} μ(B_ρ(x))/μ₀(B_ρ(x)): (0) for μ₀-a.e. x the quotient converges to Θ(x); (i) if μ₀(E) = 0 ⇒ μ(E) = 0 for all E, then μ(A) = ∫_A Θ dμ₀ for every Borel A; (ii) there is a Borel Z with μ₀(Z) = 0 and μ(A) = ∫_A Θ dμ₀ + μ(Z ∩ A) for every Borel A; (iii) if μ also has the Symmetric Vitali Property, then Z_∞ := {x : the quotient tends to ∞} has μ₀(Z_∞) = 0 and μ(A) = ∫_A Θ dμ₀ + μ(Z_∞ ∩ A) for every Borel A.

Node: `root.radon_nikodym_theorem-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/10

Decomposition children: None

## Lean problem

Declaration: `Submission.radon_nikodym_theorem`

```lean
RadonNikodymTheorem
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
- Child DAG node: `root.radon_nikodym_theorem-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

PROOF OF `RadonNikodymTheorem` (Simon, Ch. 1, 3.9–3.24: Remark 3.11(1), Theorems 3.13, 3.14, 3.15, Lemma 3.19, Theorems 3.21, 3.23, 3.24; printed proofs, transcribed and completed).

Statement. Let (X, d) be a metric space, μ, μ₀ Borel regular, open σ-finite outer measures on X, μ₀ with the Symmetric Vitali Property (SVP, Def. 3.10 as formalized: for every A with μ₀(A) < ∞ and every set 𝓑 of pairs (x, r), x ∈ A, r > 0, fine on A — ∀x ∈ A ∀ε > 0 ∃r ∈ (0, ε) with (x, r) ∈ 𝓑 — there is a countable 𝓑' ⊆ 𝓑 with pairwise disjoint closed balls and μ₀(A ∖ ⋃_{𝓑'} B_r(x)) = 0). Write q_x(ρ) := μ(B_ρ(x))/μ₀(B_ρ(x)) ∈ [0, ∞] (B_ρ(x) closed ball; [0, ∞]-conventions a/0 = ∞ for a > 0, 0/0 = 0, a/∞ = 0 for a < ∞), Θ(x) := limsup_{ρ↓0} q_x(ρ) (Lean `outerRelativeUpperDensity μ μ₀ x`; it realizes Simon's three-case definition 3.9), Θ_*(x) := liminf_{ρ↓0} q_x(ρ) (3.18). Integrals ∫_A g dμ₀ are Lebesgue integrals over A for the measure μ₀ on the σ-algebra of μ₀-measurable sets (Lean `caratheodoryMeasure μ₀`). To prove:
 (0) for μ₀-a.e. x, q_x(ρ) → Θ(x) as ρ ↓ 0 (the density Θ^{μ₀}(μ, x) of 3.22 exists and equals Θ(x));
 (i) if μ₀(E) = 0 ⇒ μ(E) = 0 for all E ⊆ X, then μ(A) = ∫_A Θ dμ₀ for every Borel A;
 (ii) there is a Borel Z with μ₀(Z) = 0 and μ(A) = ∫_A Θ dμ₀ + μ(Z ∩ A) for every Borel A;
 (iii) if μ also has the SVP, then Z_∞ := {x : q_x(ρ) → ∞ as ρ ↓ 0} has μ₀(Z_∞) = 0 and μ(A) = ∫_A Θ dμ₀ + μ(Z_∞ ∩ A) for every Borel A.

Standard facts: for an outer measure σ the σ-measurable sets form a σ-algebra M_σ containing all σ-null sets, σ is countably additive on M_σ (Simon 1.6, 1.7); Borel sets are σ-measurable for Borel regular σ; countable unions of null sets are null.

Dependency. Theorem 1.15 = sibling `borel_regular_approximation` (applied to finite Borel regular measures; closed subsets of a metric space are countable intersections of open sets).

PART I. THE FINITE CASE. Throughout Part I assume in addition μ(X) < ∞ and μ₀(X) < ∞. Let U₀ := {x : μ₀(B_ρ(x)) = 0 for some ρ > 0}.

I.0 (restriction lemma, remarks after (1.12)). If σ is Borel regular and Y is Borel, or σ-measurable with σ(Y) < ∞, then σ⌞Y (S ↦ σ(Y ∩ S)) is Borel regular and every σ-measurable set is σ⌞Y-measurable. [σ⌞Y(S) = σ(S∩Y∩E) + σ((S∩Y)∖E) for E ∈ M_σ. Hulls: Borel B₃ ⊇ S ∩ Y with σ(B₃) = σ(S ∩ Y); if Y is Borel, B := B₃ ∪ (X ∖ Y); otherwise take Borel B₁ ⊇ Y with σ(B₁ ∖ Y) = 0 and Borel B₂ ⊇ B₁ ∖ Y with σ(B₂) = 0 and B := B₃ ∪ (X ∖ B₁) ∪ B₂; in both cases B ⊇ S is Borel and σ⌞Y(B) ≤ σ(B₃) = σ⌞Y(S).]

I.1 (Remark 3.11(1)) μ₀(U₀) = 0: the pairs (x, ρ) with x ∈ U₀, μ₀(B_ρ(x)) = 0 form a fine family on U₀; the SVP gives countably many disjoint such balls covering μ₀-almost all of U₀, and their union is μ₀-null. For x ∉ U₀, 0 < μ₀(B_ρ(x)) < ∞ for all ρ > 0. The same argument shows: if a finite Borel regular σ has the SVP then {x : σ(B_ρ(x)) = 0 for some ρ > 0} is σ-null.

I.2 (Theorem 3.13) Let σ be a Borel regular outer measure with σ(X) < ∞, A ⊆ X, t > 0, and limsup_{ρ↓0} σ(B_ρ(x))/μ₀(B_ρ(x)) ≥ t for all x ∈ A ∖ U₀. Then σ(A) ≥ t·μ₀(A).
 Proof (printed). μ₀(A) = μ₀(A ∖ U₀) (I.1). Let τ ∈ (0, t), U ⊇ A open, and 𝓑 := {(x, ρ) : x ∈ A ∖ U₀, ρ > 0, B_ρ(x) ⊆ U, σ(B_ρ(x)) > τμ₀(B_ρ(x))}; 𝓑 is fine on A ∖ U₀ (the quotient exceeds τ at arbitrarily small ρ, B_ρ(x) ⊆ U for small ρ, μ₀(B_ρ(x)) ∈ (0, ∞)). The SVP of μ₀ gives disjoint B_j ∈ 𝓑 (countably many) with μ₀((A ∖ U₀) ∖ ⋃B_j) = 0, so τμ₀(A) ≤ τΣ_jμ₀(B_j) ≤ Σ_jσ(B_j) = σ(⋃B_j) ≤ σ(U). By Theorem 1.15(1) (sibling) for σ, inf_U σ(U) = σ(A); then let τ ↑ t.

I.3 (Corollary 3.14) μ₀({x : Θ(x) = ∞}) = 0: for t > 0, A_t := {Θ ≥ t} satisfies t·μ₀(A_t) ≤ μ(A_t) ≤ μ(X) by I.2, so μ₀({Θ = ∞}) ≤ μ(X)/t → 0.

I.4 (Theorem 3.15) Let σ be Borel regular with σ(X) < ∞ and E σ-measurable. Then for μ₀-a.e. x ∉ E, σ(E ∩ B_ρ(x))/μ₀(B_ρ(x)) → 0.
 Proof (as in 3.6 with 3.13 in place of 3.3). For t > 0 let S_t := {x ∉ E ∪ U₀ : limsup σ(E ∩ B_ρ(x))/μ₀(B_ρ(x)) ≥ t}. For closed C ⊆ E, σ_C := σ⌞(E ∖ C) is Borel regular and finite (I.0), and for x ∈ S_t (x ∉ C) σ_C(B_ρ(x)) = σ(E ∩ B_ρ(x)) for small ρ; I.2 with σ_C gives t·μ₀(S_t) ≤ σ(E ∖ C). By Theorem 1.15(2) (sibling) for σ⌞E there are closed C_k ⊆ E with σ(E ∖ C_k) → 0, so μ₀(S_t) = 0; outside E ∪ U₀ ∪ ⋃_m S_{1/m} the quotient tends to 0.

I.5 (Lemma 3.19, Case 1) There is a Borel B with μ₀(B) = 0 such that μ(S ∖ B) = 0 whenever μ₀(S) = 0.
 Proof (printed). Let 𝒜 := {Borel A : μ₀(A) = 0}, α := sup{μ(A) : A ∈ 𝒜} ≤ μ(X) < ∞, and A_j ∈ 𝒜 with μ(A_j) → α; B := ⋃_j A_j ∈ 𝒜 and μ(B) = α. If μ₀(S) = 0, Borel regularity of μ₀ gives a Borel A ⊇ S with μ₀(A) = 0; A ∪ B ∈ 𝒜, so μ(S ∖ B) ≤ μ(A ∖ B) = μ(A ∪ B) − μ(B) ≤ α − α = 0.

I.6 μ̃ := μ⌞(X ∖ B) is Borel regular (I.0), finite, absolutely continuous with respect to μ₀ (μ₀(S) = 0 ⇒ μ̃(S) = μ(S ∖ B) = 0), and has the SVP: given A and a fine family on A, the SVP of μ₀ (μ₀(A) < ∞ in the finite case) gives a countable disjoint subfamily 𝓑' with μ₀(A ∖ ⋃𝓑') = 0, hence μ̃(A ∖ ⋃𝓑') = 0. The same argument shows: every finite Borel regular σ which is absolutely continuous with respect to μ₀ has the SVP.

I.7 (Theorem 3.21) Let σ be Borel regular with σ(X) < ∞, absolutely continuous with respect to μ₀, A ⊆ X, t > 0, and liminf_{ρ↓0} σ(B_ρ(x))/μ₀(B_ρ(x)) ≤ t for all x ∈ A ∖ U₀. Then σ(A) ≤ t·μ₀(A).
 Proof (printed proof of 3.21(i), using the SVP of σ from I.6; this is also 3.21(ii) when σ = μ̃). σ(A ∩ U₀) = 0 because μ₀(U₀) = 0 and σ is absolutely continuous with respect to μ₀. Let A' := A ∖ U₀, so σ(A) = σ(A'). Let ϑ > t and ε > 0; by Theorem 1.15(1) (sibling) for μ₀ choose an open U ⊇ A with μ₀(U) < μ₀(A) + ε. The family {(x, ρ) : x ∈ A', ρ > 0, B_ρ(x) ⊆ U, σ(B_ρ(x)) < ϑμ₀(B_ρ(x))} is fine on A' (the quotient is < ϑ at arbitrarily small ρ, μ₀(B_ρ(x)) ∈ (0, ∞)). The SVP of σ gives countably many disjoint such balls B_j with σ(A' ∖ ⋃B_j) = 0, so σ(A') ≤ Σσ(B_j) ≤ ϑΣμ₀(B_j) = ϑμ₀(⋃B_j) ≤ ϑμ₀(U) ≤ ϑ(μ₀(A) + ε). Let ε → 0, ϑ ↓ t.

I.8 (the singular part has density 0) By I.4 with σ := μ⌞B (Borel regular, finite; B is σ-measurable) and E := B: for μ₀-a.e. x ∉ B — hence, as μ₀(B) = 0, for μ₀-a.e. x — s_x(ρ) := μ(B ∩ B_ρ(x))/μ₀(B_ρ(x)) → 0. Since B is μ-measurable, μ(B_ρ(x)) = μ̃(B_ρ(x)) + μ(B ∩ B_ρ(x)), so for x ∉ U₀: q_x(ρ) = q̃_x(ρ) + s_x(ρ) with q̃_x(ρ) := μ̃(B_ρ(x))/μ₀(B_ρ(x)). Hence for μ₀-a.e. x the limsup and liminf of q_x and of q̃_x coincide, q_x converges iff q̃_x does, and then with the same limit.

I.9 (Theorem 3.23(ii): existence and finiteness of the density) For rationals 0 < a < b let E_{a,b} := {x ∉ U₀ : liminf q̃_x < a < b < limsup q̃_x}. By I.2 (σ := μ̃), μ̃(E_{a,b}) ≥ b·μ₀(E_{a,b}); by I.7 (σ := μ̃), μ̃(E_{a,b}) ≤ a·μ₀(E_{a,b}). As μ₀(E_{a,b}) < ∞ and a < b, μ₀(E_{a,b}) = 0. So {x ∉ U₀ : liminf q̃_x < limsup q̃_x} = ⋃_{a<b} E_{a,b} is μ₀-null. Together with I.1, I.8 and I.3 there is a μ₀-null set S₁ such that for every x ∉ S₁: x ∉ U₀, q_x(ρ) converges as ρ ↓ 0, its limit is Θ(x) (a convergent function's limsup is its limit), and Θ(x) < ∞.

I.10 (measurability of Θ; printed measurability argument of 3.23) For ρ > 0, x ↦ μ(B_ρ(x)) is upper semicontinuous (if y_k → x, every point lying in infinitely many B_ρ(y_k) lies in B_ρ(x), so by the reverse Fatou inequality for the finite measure μ on M_μ, limsup_k μ(B_ρ(y_k)) ≤ μ(limsup_k B_ρ(y_k)) ≤ μ(B_ρ(x))), hence Borel; likewise x ↦ μ₀(B_ρ(x)). So g_i(x) := μ(B_{1/i}(x))/μ₀(B_{1/i}(x)) is Borel and G := limsup_i g_i is Borel. For x ∉ S₁, Θ(x) = lim_i g_i(x) = G(x). Choose a Borel S₂ ⊇ S₁ with μ₀(S₂) = 0. Then Θ = G off S₂, so Θ is μ₀-measurable ({Θ > c} differs from the Borel set {G > c} ∖ S₂ by a subset of the null set S₂), and Θ = G μ₀-a.e.
 The same facts I.1–I.10 hold with μ replaced by any finite Borel regular σ (with its own B, σ̃, S₁, Θ_σ).

I.11 (Theorem 3.24(i), finite case; printed proof) Let σ be Borel regular with σ(X) < ∞ and absolutely continuous with respect to μ₀, Θ_σ(x) := limsup_ρ σ(B_ρ(x))/μ₀(B_ρ(x)). Then σ(A) = ∫_A Θ_σ dμ₀ for every Borel A.
 Proof. By I.6 σ has the SVP, so I.7 applies to σ itself, and I.9–I.10 (for σ, where the decomposition set B_σ has σ(B_σ) = 0 by absolute continuity, so σ̃ = σ) give a μ₀-null set S_σ ⊇ U₀ off which the density lim_ρ σ(B_ρ(x))/μ₀(B_ρ(x)) exists, equals Θ_σ(x) and is finite; Θ_σ is μ₀-measurable. Put ν(A) := ∫_A Θ_σ dμ₀ for μ₀-measurable A. Every μ₀-measurable set M differs from a Borel set by a subset of a Borel μ₀-null set (Borel hulls of M and X ∖ M, μ₀ finite), which is σ-null; hence M is σ-measurable. Fix a Borel A and t > 1, and split A into the disjoint μ₀- (hence σ-) measurable pieces A ∩ S_σ, A⁰ := (A ∖ S_σ) ∩ {Θ_σ = 0}, and A_k := (A ∖ S_σ) ∩ {t^k ≤ Θ_σ < t^{k+1}}, k ∈ ℤ (they cover A since Θ_σ < ∞ off S_σ).
  • σ(A ∩ S_σ) = 0 = ν(A ∩ S_σ), since μ₀(S_σ) = 0.
  • On A⁰ the density exists and is 0, so its liminf is ≤ ε for every ε > 0; I.7 gives σ(A⁰) ≤ εμ₀(X) for all ε, so σ(A⁰) = 0 = ν(A⁰).
  • On A_k the density exists with value in [t^k, t^{k+1}), so limsup ≥ t^k and liminf ≤ t^{k+1}; I.2 and I.7 give t^k μ₀(A_k) ≤ σ(A_k) ≤ t^{k+1}μ₀(A_k), while t^kμ₀(A_k) ≤ ν(A_k) ≤ t^{k+1}μ₀(A_k). Hence σ(A_k) ≤ t·ν(A_k) and ν(A_k) ≤ t·σ(A_k).
 Summing over the pieces (countable additivity of σ on M_σ and of ν): σ(A) ≤ t·ν(A) and ν(A) ≤ t·σ(A) < ∞; letting t ↓ 1, σ(A) = ν(A). (Printed: “(a/b)ν(A_{a,b}) ≤ μ(A_{a,b}) ≤ (b/a)ν(A_{a,b}) and it follows that ν(A) = μ(A).”)

I.12 (Theorem 3.24(ii), finite case; printed “apply the previous argument to μ⌞(X ∖ B)”) By I.11 with σ := μ̃ (I.6), μ̃(A) = ∫_A Θ̃ dμ₀ for Borel A, where Θ̃ := limsup q̃. By I.8–I.9, Θ̃ = Θ μ₀-a.e., and both are μ₀-measurable (I.10), so ∫_A Θ̃ dμ₀ = ∫_A Θ dμ₀. As B is Borel, μ(A) = μ(A ∖ B) + μ(A ∩ B) = μ̃(A) + μ(B ∩ A) = ∫_A Θ dμ₀ + μ(B ∩ A). So (ii) holds with Z := B.

PART II. THE GENERAL CASE (printed: “Since μ, μ₀ are open σ-finite, we can assume μ(X) < ∞, μ₀(X) < ∞”; the reduction is made explicit).

II.1 Let (V_j) and (V'_k) be the open covers witnessing open σ-finiteness of μ and μ₀, and let (W_m)_{m≥1} enumerate the open sets V_j ∩ V'_k; then X = ⋃_m W_m and μ(W_m), μ₀(W_m) < ∞. Put μ_m := μ⌞W_m, μ₀_m := μ₀⌞W_m (Borel regular by I.0, finite), and W'_m := W_m ∖ ⋃_{l<m} W_l (Borel, pairwise disjoint, ⋃_m W'_m = X). μ₀_m has the SVP: for A with μ₀(A ∩ W_m) < ∞ and a family fine on A, the pairs centred in A ∩ W_m form a family fine on A ∩ W_m, and the SVP of μ₀ gives a countable disjoint subfamily 𝓑' with μ₀_m(A ∖ ⋃𝓑') = μ₀((A ∩ W_m) ∖ ⋃𝓑') = 0. Likewise μ_m has the SVP if μ has. For x ∈ W_m and ρ small (B_ρ(x) ⊆ W_m), μ_m(B_ρ(x)) = μ(B_ρ(x)) and μ₀_m(B_ρ(x)) = μ₀(B_ρ(x)); so the quotients for (μ_m, μ₀_m) and (μ, μ₀) coincide for small ρ, and at x ∈ W_m the upper and lower densities, the existence of the limit and its value are the same for both pairs; in particular Θ_m = Θ on W_m (Θ_m the upper density of μ_m w.r.t. μ₀_m). A set N ⊆ W_m is μ₀-null iff μ₀_m-null; on μ₀-measurable subsets of W_m the measures μ₀_m and μ₀ agree, so ∫_E g dμ₀_m = ∫_E g dμ₀ for μ₀-measurable g ≥ 0 and μ₀-measurable E ⊆ W_m.

II.2 Clause (0). For each m, I.9 for (μ_m, μ₀_m) gives a μ₀_m-null N_m off which the quotient for (μ_m, μ₀_m) converges to Θ_m. For x ∈ W_m ∖ N_m, q_x(ρ) converges to Θ(x) by II.1. The exceptional set is contained in ⋃_m (N_m ∩ W_m), which is μ₀-null. This is `∀ᵐ x ∂μ₀, Tendsto q_x (𝓝[>] 0) (𝓝 (Θ x))`. Moreover Θ is μ₀-measurable: on each W'_m it equals Θ_m, which is μ₀_m-measurable by I.10, and a subset of W_m which is μ₀_m-measurable is μ₀-measurable (it is a Borel set up to a subset of a μ₀_m-null, hence μ₀-null, subset of W_m).

II.3 Clause (ii). For each m, I.12 for (μ_m, μ₀_m) gives a Borel Z_m with μ₀_m(Z_m) = 0 and μ_m(A) = ∫_A Θ_m dμ₀_m + μ_m(Z_m ∩ A) for all Borel A. Let Z := ⋃_m (Z_m ∩ W'_m), a Borel set with μ₀(Z) ≤ Σ_m μ₀(Z_m ∩ W_m) = Σ_m μ₀_m(Z_m) = 0. For a Borel A let A_m := A ∩ W'_m ⊆ W_m. By II.1 (Θ_m = Θ on W_m, Z_m ∩ A_m = Z ∩ A_m),
  μ(A_m) = μ_m(A_m) = ∫_{A_m} Θ_m dμ₀_m + μ_m(Z_m ∩ A_m) = ∫_{A_m} Θ dμ₀ + μ(Z ∩ A_m).
Summing over m (A and Z ∩ A are the disjoint unions of the Borel sets A_m, resp. Z ∩ A_m; countable additivity of μ on Borel sets and of the integral) gives μ(A) = ∫_A Θ dμ₀ + μ(Z ∩ A).

II.4 Clause (i). If μ₀(E) = 0 ⇒ μ(E) = 0 for all E, then μ(Z ∩ A) = 0 for the Z of II.3 (as μ₀(Z ∩ A) = 0), so μ(A) = ∫_A Θ dμ₀ for every Borel A.

II.5 Clause (iii) (printed proof of (iii): the density of μ is infinite exactly on the singular part). Assume μ also has the SVP; let Z be as in II.3.
 (a) μ₀(Z_∞) = 0: if q_x → ∞ then Θ(x) = ∞; for each m, Z_∞ ∩ W_m ⊆ {x ∈ W_m : Θ_m(x) = ∞}, which is μ₀_m-null by I.3; hence μ₀(Z_∞ ∩ W_m) = 0 for all m.
 (b) μ(Z ∖ Z_∞) = 0: fix m and n ∈ ℕ, and let E := (Z ∩ W_m) ∩ {x : Θ_*(x) < n}. Points x ∈ W_m ∩ U₀ with μ(B_ρ(x)) > 0 for all ρ have q_x(ρ) = ∞ for small ρ, hence Θ_*(x) = ∞ and x ∉ E; the set W_m ∩ {x : μ(B_ρ(x)) = 0 for some ρ} is μ-null (I.1 for μ_m, which has the SVP). Let E' := E ∖ (U₀ ∪ {x : μ(B_ρ(x)) = 0 for some ρ}). For ϑ > n and ε > 0 choose (Theorem 1.15(1) for μ₀_m) an open U ⊇ E' with μ₀_m(U) < μ₀_m(E') + ε = ε (μ₀(E') ≤ μ₀(Z) = 0). The pairs (x, ρ), x ∈ E', B_ρ(x) ⊆ U ∩ W_m, μ(B_ρ(x)) < ϑμ₀(B_ρ(x)), form a family fine on E'; the SVP of μ_m gives disjoint such balls B_j with μ_m(E' ∖ ⋃B_j) = 0, so μ(E') = μ_m(E') ≤ Σμ(B_j) ≤ ϑΣμ₀(B_j) ≤ ϑμ₀_m(U) ≤ ϑε. Hence μ(E') = 0 and μ(E) = 0. Taking the union over m and n: μ-a.e. x ∈ Z has Θ_*(x) = ∞, i.e. q_x(ρ) → ∞, i.e. x ∈ Z_∞.
 (c) μ(Z_∞ ∖ Z) = 0: choose a Borel H ⊇ Z_∞ with μ₀(H) = 0; by (ii) applied to the Borel set H ∖ Z, μ(H ∖ Z) = ∫_{H∖Z} Θ dμ₀ + μ(Z ∩ (H ∖ Z)) = 0 + 0, and Z_∞ ∖ Z ⊆ H ∖ Z.
 (d) For Borel A: μ(Z_∞ ∩ A) ≤ μ(Z ∩ A) + μ(Z_∞ ∖ Z) = μ(Z ∩ A) and μ(Z ∩ A) ≤ μ(Z_∞ ∩ A) + μ(Z ∖ Z_∞) = μ(Z_∞ ∩ A). So μ(A) = ∫_A Θ dμ₀ + μ(Z_∞ ∩ A) by (ii).
This proves (0), (i), (ii), (iii). ∎

Formalization note (non-binding): `Poincare.SimonGMT.Chapter01.simon_theorem_3_23_ii` (Chapter01/RadonNikodymDensity.lean) gives clause (0) outside a Borel μ₀-null set; `simon_theorem_3_24_i`, `simon_theorem_3_24_ii`, `simon_theorem_3_24_iii` (Chapter01/RadonNikodymTheorem.lean, with the local instance `MeasurableSpace X := borel X`) give (i)–(iii) with integrals against `hμ₀.toBorelMeasure` and `OuterMeasure.restrict Z μ` (= μ(A ∩ Z)); `outerInfiniteDensitySet μ μ₀` is literally Z_∞. Transport the lintegrals to `caratheodoryMeasure μ₀` via `setLIntegral_trim_ae` with `(caratheodoryMeasure μ₀).trim _ = hμ₀.toBorelMeasure`, using that Θ is a.e. equal to the Borel `rnDeriv` (`ae_outerRelativeUpperDensity_eq_rnDeriv`, `Measure.measurable_rnDeriv`).

## Key steps

1. Finite case: U₀ is μ₀-null; 3.13 (upper comparison); 3.14 (Θ < ∞ μ₀-a.e.); 3.15 (densities of finite measures vanish off measurable sets).
2. Lemma 3.19: a Borel μ₀-null B with μ⌞(X ∖ B) ≪ μ₀; μ̃ := μ⌞(X ∖ B) and every finite σ ≪ μ₀ inherit the Symmetric Vitali Property.
3. 3.21: lower comparison σ(A) ≤ t·μ₀(A) for such σ.
4. The singular part μ⌞B has density 0 μ₀-a.e., so the quotients of μ and μ̃ have the same limits.
5. 3.23: the sets E_{a,b} are μ₀-null by 3.13 and 3.21, so the density exists, equals Θ and is finite μ₀-a.e.; Θ is μ₀-measurable (upper semicontinuity of ball measures).
6. 3.24(i), finite case: σ ≪ μ₀ ⇒ σ(A) = ∫_A Θ_σ dμ₀ by t-adic slicing with 3.13 and 3.21; (ii), finite case, with Z = B by applying (i) to μ̃.
7. General case: localize to W_m = V_j ∩ V'_k; clause (0) and (ii) glue over the disjoint Borel pieces W'_m; (i) follows from (ii).
8. (iii): μ₀(Z_∞) = 0 by 3.14; μ(Z ∖ Z_∞) = 0 by a 3.21-type argument with the Vitali property of μ; μ(Z_∞ ∖ Z) = 0 by (ii); hence μ(Z_∞ ∩ A) = μ(Z ∩ A).

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
