<!-- theorem-id: gmt-ch01/root.lebesgue_eq_hausdorff_and_isodiametric-a1 -->

## Theorem `Submission.lebesgue_eq_hausdorff_and_isodiametric`

For every n ∈ ℕ, every real δ > 0 and every A ⊆ ℝⁿ = EuclideanSpace ℝ (Fin n): Lⁿ(A) = Hⁿ(A) and Hⁿ(A) = Hⁿ_δ(A), where Lⁿ is Lebesgue outer measure and Hⁿ, Hⁿ_δ are Simon's normalized Hausdorff measure and size-δ approximation (2.1), (2.2); and for every n ∈ ℕ and A ⊆ ℝⁿ: Lⁿ(A) ≤ ω_n (diam A / 2)ⁿ with ω_n = π^{n/2}/Γ(n/2 + 1).

Node: `root.lebesgue_eq_hausdorff_and_isodiametric-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.lebesgue_eq_hausdorff_and_isodiametric`

```lean
LebesgueEqHausdorff ∧ IsodiametricInequality
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
- Child DAG node: `root.lebesgue_eq_hausdorff_and_isodiametric-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

PROOF OF `LebesgueEqHausdorff ∧ IsodiametricInequality` (Simon, Ch. 1, Theorems 2.9 and 2.10; printed proofs, transcribed and completed).

Statements. Let n ∈ ℕ and ℝⁿ := EuclideanSpace ℝ (Fin n) with the Euclidean metric.
 (2.10) For every A ⊆ ℝⁿ: Lⁿ(A) ≤ ω_n (diam A / 2)ⁿ.
 (2.9) For every real δ > 0 and every A ⊆ ℝⁿ: Lⁿ(A) = Hⁿ(A) and Hⁿ(A) = Hⁿ_δ(A).

Notation and conventions.
 • Lⁿ is Lebesgue outer measure on ℝⁿ (Lean: `volume`, Lebesgue measure on EuclideanSpace ℝ (Fin n) evaluated on arbitrary sets, i.e. Lⁿ(A) = inf{Lⁿ(B) : B ⊇ A Borel}); it agrees with Simon's (2.7) (inf of Σ|I_j| over countable covers by open boxes) and satisfies (2.8): Lⁿ(I) = |I| for boxes and Lⁿ(A) = inf{Lⁿ(U) : U ⊇ A open}. Boundaries of boxes/cubes are Lⁿ-null.
 • ω_n := π^{n/2}/Γ(n/2 + 1) ∈ (0, ∞); it is the volume of the unit ball of ℝⁿ, and Lⁿ(B_r(x)) = ω_n rⁿ for open and for closed balls of radius r ≥ 0.
 • diam takes values in [0, ∞] (∞ for unbounded sets); x⁰ = 1 for all x ∈ [0, ∞].
 • For δ ∈ (0, ∞], Hⁿ_δ(∅) = 0 and for A ≠ ∅, Hⁿ_δ(A) = ω_n inf{Σ_j (diam C_j/2)ⁿ : A ⊆ ⋃_j C_j, C_j countably many, diam C_j < δ} (empty C_j contribute 0; inf ∅ = ∞) (2.2); Hⁿ_δ is an outer measure, non-increasing in δ, and Hⁿ := sup_{δ>0} Hⁿ_δ (2.1). Since Hⁿ_∞ ≤ Hⁿ_δ for every real δ > 0, Hⁿ(A) = sup_{real δ>0} Hⁿ_δ(A) = lim_{δ↓0} Hⁿ_δ(A). In the Lean statement δ enters as `ENNReal.ofReal δ`.

PART 0: n = 0. ℝ⁰ = {0} and L⁰ is the unit point mass (L⁰({0}) = 1, L⁰(∅) = 0); ω_0 = π⁰/Γ(1) = 1. For every δ ∈ (0, ∞]: H⁰_δ({0}) = 1, because the one-set cover {0} (diameter 0 < δ) costs ω_0·(0/2)⁰ = 1, while every cover of {0} contains a nonempty set and each nonempty set costs (diam/2)⁰ = 1. Hence L⁰ = H⁰_δ = H⁰ on both subsets of ℝ⁰, and L⁰(A) ≤ 1 = ω_0 (diam A/2)⁰. Both statements hold for n = 0. From now on n ≥ 1.

PART A: the isodiametric inequality (2.10), n ≥ 1.

A.1 Reductions. If A = ∅ the claim is trivial. If diam A = ∞ the right side is ω_n · ∞ = ∞. Otherwise A is bounded and nonempty; its closure Ā is compact (Heine–Borel), diam Ā = diam A, and Lⁿ(A) ≤ Lⁿ(Ā). So it suffices to treat nonempty compact A.

A.2 Steiner symmetrization (printed definition). Fix j ∈ {1, …, n}; let P_j := {x : x^j = 0}. For ξ ∈ P_j let ℓ_j(ξ) := {ξ + t e_j : t ∈ ℝ} and π(ξ + t e_j) := t. For compact A put A_ξ := π(A ∩ ℓ_j(ξ)) ⊆ ℝ (compact), λ(ξ) := L¹(A_ξ), and σ_j(A, ξ) := {ξ + t e_j : |t| ≤ λ(ξ)/2}. Define
  S_j(A) := ⋃{σ_j(A, ξ) : ξ ∈ P_j, A ∩ ℓ_j(ξ) ≠ ∅}.

A.3 (Printed Note: upper semicontinuity.) Let ξ ∈ P_j, η > 0 and ξ_k → ξ in P_j. Choose an open O ⊆ ℝ with A_ξ ⊆ O and L¹(O) ≤ λ(ξ) + η (outer regularity of L¹; O = ∅ if A_ξ = ∅). The set Õ := {x : x^j ∈ O} is open and contains A ∩ ℓ_j(ξ). For all large k, A ∩ ℓ_j(ξ_k) ⊆ Õ: otherwise there are k_m → ∞ and a_m ∈ (A ∩ ℓ_j(ξ_{k_m})) ∖ Õ, a subsequence converges to some a ∈ A ∖ Õ (A compact, ℝⁿ ∖ Õ closed), and a ∈ ℓ_j(ξ) because the projection of a_m onto P_j is ξ_{k_m} → ξ — contradicting A ∩ ℓ_j(ξ) ⊆ Õ. Hence A_{ξ_k} ⊆ O and λ(ξ_k) ≤ λ(ξ) + η for all large k. The same compactness argument shows: if A ∩ ℓ_j(ξ_k) ≠ ∅ for infinitely many k, then A ∩ ℓ_j(ξ) ≠ ∅.

A.4 S_j(A) is compact. If A ⊆ B_R(0) then A ∩ ℓ_j(ξ) ≠ ∅ only for |ξ| ≤ R and λ(ξ) ≤ 2R, so S_j(A) ⊆ {ξ + t e_j : |ξ| ≤ R, |t| ≤ R} is bounded. If x_k = ξ_k + t_k e_j ∈ S_j(A) converge to x = ξ + t e_j, then ξ_k → ξ, t_k → t, A ∩ ℓ_j(ξ) ≠ ∅ (A.3), and |t| = lim |t_k| ≤ limsup λ(ξ_k)/2 ≤ λ(ξ)/2 (A.3); so x ∈ σ_j(A, ξ) ⊆ S_j(A). Thus S_j(A) is closed and bounded, hence compact.

A.5 Lⁿ(S_j(A)) = Lⁿ(A). Both sets are compact, hence Borel. Identify ℝⁿ with P_j × ℝ via ξ + t e_j ↔ (ξ, t), so that Lⁿ = L^{n−1} ⊗ L¹. By Fubini–Tonelli, Lⁿ(A) = ∫_{P_j} L¹(A_ξ) dξ = ∫_{P_j} λ(ξ) dξ and Lⁿ(S_j(A)) = ∫_{P_j} L¹([−λ(ξ)/2, λ(ξ)/2]) dξ = ∫_{P_j} λ(ξ) dξ (both slices are empty/null when A ∩ ℓ_j(ξ) = ∅).

A.6 diam S_j(A) ≤ diam A (asserted in the printed text; proof). Let x = ξ + s e_j and y = η + t e_j be points of S_j(A), so A_ξ, A_η are nonempty compact, |s| ≤ λ(ξ)/2, |t| ≤ λ(η)/2. Let p⁻ := min A_ξ, p⁺ := max A_ξ, q⁻ := min A_η, q⁺ := max A_η. Then λ(ξ) ≤ p⁺ − p⁻ and λ(η) ≤ q⁺ − q⁻, so
  |s − t| ≤ |s| + |t| ≤ ½(p⁺ − p⁻) + ½(q⁺ − q⁻) = ½[(p⁺ − q⁻) + (q⁺ − p⁻)] ≤ m := max(|p⁺ − q⁻|, |q⁺ − p⁻|).
Since ξ − η ⊥ e_j and the points ξ + p^± e_j, η + q^± e_j lie in A,
  |x − y|² = |ξ − η|² + |s − t|² ≤ |ξ − η|² + m² = max(|(ξ + p⁺e_j) − (η + q⁻e_j)|², |(η + q⁺e_j) − (ξ + p⁻e_j)|²) ≤ (diam A)².

A.7 Symmetry. Let R_i(x) := x − 2x^i e_i (reflection in {x^i = 0}). By construction S_j(A) is R_j-invariant. If i ≠ j and R_i(A) = A, then S_j(A) is R_i-invariant: R_i maps P_j onto itself and ℓ_j(ξ) onto ℓ_j(R_i ξ) preserving the coordinate t, so A_{R_iξ} = π(R_i(A ∩ ℓ_j(ξ))) = A_ξ, λ(R_i ξ) = λ(ξ), and R_i(σ_j(A, ξ)) = σ_j(A, R_i ξ).

A.8 Conclusion of (2.10). Let Ã := S_n(S_{n−1}(⋯ S_1(A) ⋯)). By A.4–A.7 (inductively, the k-th set is invariant under R_1, …, R_k), Ã is a nonempty compact set with Lⁿ(Ã) = Lⁿ(A), diam Ã ≤ diam A, invariant under R_1, …, R_n and hence under x ↦ −x = R_1 ∘ ⋯ ∘ R_n. For x ∈ Ã also −x ∈ Ã, so 2|x| = |x − (−x)| ≤ diam Ã; thus Ã ⊆ B_{diam Ã/2}(0) (closed ball) and
  Lⁿ(A) = Lⁿ(Ã) ≤ ω_n (diam Ã/2)ⁿ ≤ ω_n (diam A/2)ⁿ.

PART B: Theorem 2.9, n ≥ 1, δ ∈ (0, ∞) real.

B.1 (printed “Completion of the proof of 2.9”) Lⁿ(A) ≤ Hⁿ_δ(A). If {C_j} is a countable cover of A with diam C_j < δ, then by countable subadditivity and (2.10), Lⁿ(A) ≤ Σ_j Lⁿ(C_j) ≤ Σ_j ω_n (diam C_j/2)ⁿ. Taking the infimum over such covers (if there is none, Hⁿ_δ(A) = ∞) gives Lⁿ(A) ≤ Hⁿ_δ(A).

B.2 (Lⁿ-null sets are Hⁿ_δ-null; “by Definitions 2.2, 2.7”.) Let Lⁿ(Z) = 0 and η > 0. By (2.7) Z ⊆ ⋃_k I_k with open boxes I_k and Σ_k |I_k| < η. A box with side lengths ℓ_1, …, ℓ_n is covered by the closed grid cubes of side s meeting it, whose total volume is ≤ ∏_i(ℓ_i + 2s) → |I| as s ↓ 0; choose s = s_k so small that this total is ≤ |I_k| + 2^{−k}η and s_k√n < δ. This gives countably many closed cubes Q of diameter s√n < δ covering Z with Σ Lⁿ(Q) ≤ 2η, so Hⁿ_δ(Z) ≤ Σ ω_n (s√n/2)ⁿ = ω_n (√n/2)ⁿ Σ Lⁿ(Q) ≤ 2ω_n(√n/2)ⁿ η. As η is arbitrary, Hⁿ_δ(Z) = 0.

B.3 (printed packing lemma) For every bounded open U ⊆ ℝⁿ there are pairwise disjoint closed balls B_1, B_2, … ⊆ U with diam B_j < δ and Lⁿ(U ∖ ⋃_j B_j) = 0.
 Let θ_n := ω_n/4ⁿ ∈ (0, 1). Claim: every nonempty bounded open W contains finitely many pairwise disjoint closed balls of diameter < δ with Lⁿ(W ∖ ⋃ balls) ≤ (1 − θ_n/2) Lⁿ(W). Indeed, write W = ⋃_j Q_j with countably many closed dyadic cubes Q_j with pairwise disjoint interiors and diam Q_j < δ; in Q_j (edge ℓ_j) take the closed ball B'_j concentric with Q_j of radius ℓ_j/3, so B'_j ⊆ int Q_j, diam B'_j < diam Q_j < δ, the B'_j are pairwise disjoint, and Lⁿ(B'_j) = ω_n 3^{−n} ℓ_jⁿ ≥ θ_n Lⁿ(Q_j). As cube boundaries are null, Lⁿ(W ∖ ⋃_j B'_j) = Σ_j Lⁿ(Q_j ∖ B'_j) ≤ (1 − θ_n) Σ_j Lⁿ(Q_j) = (1 − θ_n)Lⁿ(W). Since 0 < Lⁿ(W) < ∞ and Lⁿ(W ∖ ⋃_{j≤N} B'_j) ↓ Lⁿ(W ∖ ⋃_j B'_j), some N gives Lⁿ(W ∖ ⋃_{j≤N} B'_j) ≤ (1 − θ_n/2)Lⁿ(W).
 Now set W_0 := U and, while W_m ≠ ∅, apply the claim to W_m and let W_{m+1} := W_m ∖ (the chosen finitely many balls), which is open and bounded. The balls chosen at all stages are countably many, pairwise disjoint (each stage's balls lie in W_m, which is disjoint from all earlier balls), contained in U, of diameter < δ, and U ∖ ⋃(all balls) ⊆ W_m with Lⁿ(W_m) ≤ (1 − θ_n/2)^m Lⁿ(U) → 0.

B.4 (printed (1)–(3)) Hⁿ_δ(A) ≤ Lⁿ(A). Let {I_k} be any countable cover of A by open boxes. For each k let {B_{kj}}_j be balls as in B.3 for U = I_k, with radii ρ_{kj} (so diam B_{kj} = 2ρ_{kj} < δ). Using the subadditivity of Hⁿ_δ, B.2, and the one-set covers {B_{kj}}:
  Hⁿ_δ(I_k) ≤ Hⁿ_δ(⋃_j B_{kj}) + Hⁿ_δ(I_k ∖ ⋃_j B_{kj}) ≤ Σ_j ω_n ρ_{kj}ⁿ + 0 = Σ_j Lⁿ(B_{kj}) = Lⁿ(⋃_j B_{kj}) ≤ Lⁿ(I_k) = |I_k|.
Hence Hⁿ_δ(A) ≤ Σ_k Hⁿ_δ(I_k) ≤ Σ_k |I_k|, and taking the infimum over box covers (2.7) gives Hⁿ_δ(A) ≤ Lⁿ(A).

B.5 Conclusion of (2.9). By B.1 and B.4, Hⁿ_δ(A) = Lⁿ(A) for every real δ > 0. Hence Hⁿ(A) = sup_{real δ>0} Hⁿ_δ(A) = Lⁿ(A) (the value δ = ∞ in Lean's supremum over δ ∈ (0, ∞] does not change it, since Hⁿ_∞(A) ≤ Hⁿ_1(A) = Lⁿ(A)). Therefore Lⁿ(A) = Hⁿ(A) = Hⁿ_δ(A) for every real δ > 0, which is `LebesgueEqHausdorff`; together with Part A (and Part 0) this proves the conjunction. ∎

Formalization note (non-binding): `Poincare.SimonGMT.Chapter01.simon_theorem_2_9 n (hδ : 0 < ENNReal.ofReal δ) A` gives `volume A = simonHausdorffOuterValue n A ∧ simonHausdorffOuterValue n A = simonHausdorffContent n (ENNReal.ofReal δ) A`, where `simonHausdorffOuterValue m A` is by definition `simonHausdorffOuterMeasureReal m A`; `simon_theorem_2_10 n A` gives the isodiametric inequality with the real power `(n : ℝ)`, converted by `ENNReal.rpow_natCast` (both in Chapter01/EuclideanNormalization.lean).

## Key steps

1. n = 0: L⁰ and every H⁰_δ are the unit point mass on ℝ⁰, so both statements hold.
2. Isodiametric inequality: reduce to nonempty compact A and use Steiner symmetrization S_j.
3. S_j(A) is compact (upper semicontinuity of slice length), has the same measure (Fubini), no larger diameter, and preserves the reflection symmetries already present.
4. Ã = S_n ⋯ S_1(A) is symmetric under x ↦ −x, so Ã ⊆ B_{diam Ã/2}(0) and Lⁿ(A) ≤ ω_n(diam A/2)ⁿ.
5. Lⁿ(A) ≤ Hⁿ_δ(A) by subadditivity and the isodiametric inequality on each covering set.
6. Hⁿ_δ(A) ≤ Lⁿ(A): Lⁿ-null sets are Hⁿ_δ-null, and each open box is packed up to a null set by disjoint closed balls of diameter < δ.
7. Hence Lⁿ = Hⁿ_δ for every real δ > 0, and Lⁿ = Hⁿ (the δ = ∞ term of the supremum is harmless).

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

Solution PR: https://github.com/ZhengyangZhang06/gmt-formalize/pull/89

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
