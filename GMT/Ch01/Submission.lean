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

/-- Simon Ch. 1, Theorem 1.13, from Mathlib's `OuterMeasure.IsMetric.borel_le_caratheodory`:
sets that are `Metric.AreSeparated` with constant `r ≠ 0` are separated by the real number
`(min r 1).toReal > 0`, so the hypothesis makes `μ` a metric outer measure. -/
theorem Submission.caratheodory_criterion : CaratheodoryCriterion := by
  intro X _ μ hμ E hE
  have hm : μ.IsMetric := by
    rintro A B ⟨r, hr, hAB⟩
    refine hμ A B ⟨(min r 1).toReal, ENNReal.toReal_pos (by simp [hr])
      (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right r 1)), fun a ha b hb => ?_⟩
    exact ENNReal.toReal_le_of_le_ofReal dist_nonneg
      ((min_le_left r 1).trans ((hAB a ha b hb).trans_eq (edist_dist a b)))
  exact hm.borel_le_caratheodory E hE

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

/-- Simon Ch. 1, Theorem 1.15, from the pinned `Poincare.SimonGMT` library:
`IsBorelRegularOuterMeasure.simon_theorem_1_15`, whose topological hypothesis
`ClosedSetsAreGDelta X` is the contract's `G_δ` hypothesis by `closedSetsAreGDelta_iff`. -/
theorem Submission.borel_regular_approximation : BorelRegularApproximation :=
  fun _ _ hX _ hμ hopen => hμ.simon_theorem_1_15 hopen (closedSetsAreGDelta_iff.mpr hX)

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

/-- Simon Ch. 1, Theorem 1.17, by the printed proof.  The restriction `μ ⌞ A` is Borel regular
(the remark after (1.12): pinned `Poincare.SimonGMT` lemma `IsBorelRegularOuterMeasure.restrict`)
and finite, so Theorem 1.15(2) (`Submission.borel_regular_approximation`) gives closed inner
approximations of the `μ`-measurable subsets of `A`.  For each mesh `1 / (i + 1)`, closed
subsets of the level sets `{⌊(i + 1) f⌋ = j}`, truncated to finitely many `j`, form a closed
`D i ⊆ A` with `μ (A \ D i) < δ i`, where `∑ δ i < ε`; on `⋂ i, D i` the locally constant step
functions `⌊(i + 1) f⌋ / (i + 1)` converge uniformly to `f`. -/
theorem Submission.lusin_theorem : LusinTheorem := by
  intro X _ hX μ hμ A hA hAfin f hf ε hε
  classical
  -- The `μ`-measurable sets (Simon 1.6, 1.7) as the ambient σ-algebra; Borel sets belong to it.
  let _ : MeasurableSpace X := μ.caratheodory
  have : OpensMeasurableSpace X := ⟨hμ.borel_le_caratheodory⟩
  have hAm : MeasurableSet A := hA
  have hf' : Measurable f := hf
  -- Step 0: the level sets `L i j = f⁻¹[j / (i + 1), (j + 1) / (i + 1))`, i.e.
  -- `{x ∈ A : ⌊(i + 1) f x⌋ = j}`, are `μ`-measurable.
  obtain ⟨L, hLm, hLA, hmemL⟩ : ∃ L : ℕ → ℤ → Set X, (∀ i j, MeasurableSet (L i j)) ∧
      (∀ i j, L i j ⊆ A) ∧ ∀ i j (a : A), (a : X) ∈ L i j ↔ ⌊f a * ((i : ℝ) + 1)⌋ = j :=
    ⟨fun i j => Subtype.val '' ((fun a : A => f a * ((i : ℝ) + 1)) ⁻¹' Ico (j : ℝ) (j + 1)),
      fun i j => hAm.subtype_image ((hf'.mul_const _) measurableSet_Ico),
      fun i j => Subtype.coe_image_subset A _,
      fun i j a => Subtype.val_injective.mem_set_image.trans Int.floor_eq_iff.symm⟩
  -- Steps 1–2: `μ ⌞ A` is Borel regular and finite, hence open σ-finite, and Theorem 1.15(2)
  -- for it gives closed inner approximations of the `μ`-measurable subsets of `A`.
  have hreg : ∀ E : Set X, MeasurableSet E → E ⊆ A → ∀ η : ℝ≥0∞, η ≠ 0 →
      ∃ F : Set X, F ⊆ E ∧ IsClosed F ∧ μ (E \ F) < η := by
    intro E hE hEA η hη
    have hμA : IsBorelRegularOuterMeasure (OuterMeasure.restrict A μ) := hμ.restrict hA hAfin
    have hμAσ : IsOpenSigmaFinite (OuterMeasure.restrict A μ) :=
      (isOpenSigmaFinite_iff _).2 ⟨fun _ => univ, fun _ => ⟨isOpen_univ, by
        rw [OuterMeasure.restrict_apply, univ_inter]; exact hAfin⟩, iUnion_const univ⟩
    have hres : ∀ S ⊆ A, OuterMeasure.restrict A μ S = μ S := fun S hS => by
      rw [OuterMeasure.restrict_apply, inter_eq_left.2 hS]
    have hsup : μ E = ⨆ (F : Set X) (_ : F ⊆ E) (_ : IsClosed F), OuterMeasure.restrict A μ F := by
      rw [← hres E hEA]
      exact (Submission.borel_regular_approximation X hX _ hμA hμAσ).2 E
        (isCaratheodoryMeasurable_restrict hE)
    have hEfin : μ E ≠ ∞ := ne_top_of_le_ne_top hAfin.ne (measure_mono hEA)
    by_cases hsmall : μ E < η
    · exact ⟨∅, empty_subset E, isClosed_empty, by rwa [Set.sdiff_empty]⟩
    have hE0 : μ E ≠ 0 := fun h => hsmall (by rw [h]; exact pos_iff_ne_zero.2 hη)
    obtain ⟨F, hF⟩ := lt_iSup_iff.1 ((ENNReal.sub_lt_self hEfin hE0 hη).trans_eq hsup)
    obtain ⟨hFE, hF⟩ := lt_iSup_iff.1 hF
    obtain ⟨hFc, hF⟩ := lt_iSup_iff.1 hF
    rw [hres F (hFE.trans hEA)] at hF
    refine ⟨F, hFE, hFc, ?_⟩
    -- `F` is Borel, hence `μ`-measurable, so `μ E = μ F + μ (E \ F)`.
    have hsplit : μ E = μ F + μ (E \ F) := by
      rw [(OuterMeasure.isCaratheodory_iff μ).1 hFc.measurableSet E, inter_eq_right.2 hFE]
    have h1 : μ E < μ F + η := ENNReal.lt_add_of_sub_lt_right (Or.inl hEfin) hF
    rw [hsplit] at h1
    exact (ENNReal.add_lt_add_iff_left (ne_top_of_le_ne_top hEfin (measure_mono hFE))).1 h1
  -- Weights `δ i > 0` with `∑ δ i < ε`.
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable' (ENNReal.ofReal_pos.2 hε).ne' ℕ
  -- Step 3: for each `i`, closed `C j ⊆ L i j` with `∑ μ (L i j \ C j) < δ i`, truncated to
  -- `|j| ≤ J` by continuity from above; `⌊(i + 1) f⌋` is locally constant on the union `D`.
  have hstep : ∀ i : ℕ, ∃ D : Set X, IsClosed D ∧ D ⊆ A ∧ μ (A \ D) < δ i ∧
      ∀ a : A, (a : X) ∈ D → ∃ U : Set X, IsOpen U ∧ (a : X) ∈ U ∧
        ∀ b : A, (b : X) ∈ D ∩ U → ⌊f b * ((i : ℝ) + 1)⌋ = ⌊f a * ((i : ℝ) + 1)⌋ := by
    intro i
    obtain ⟨η, hηpos, hηsum⟩ := ENNReal.exists_pos_sum_of_countable' (hδpos i).ne' ℤ
    choose C hCL hCc hCμ using fun j : ℤ => hreg (L i j) (hLm i j) (hLA i j) (η j) (hηpos j).ne'
    obtain ⟨J, hJ⟩ : ∃ J : ℕ, μ (A \ ⋃ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), C j) < δ i := by
      have hEm : ∀ J : ℕ, MeasurableSet (A \ ⋃ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), C j) :=
        fun J => hAm.diff (Finset.measurableSet_biUnion _ fun j _ => (hCc j).measurableSet)
      have hanti : Antitone fun J : ℕ => A \ ⋃ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), C j := by
        intro J K hJK
        refine sdiff_subset_sdiff_right
          (iUnion₂_subset fun j hj => subset_iUnion₂_of_subset j ?_ subset_rfl)
        rw [Finset.mem_Icc] at hj ⊢
        omega
      -- Every point of `A` outside all `C j` lies in some `L i j \ C j`.
      have hinter : (⋂ J : ℕ, A \ ⋃ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), C j) ⊆
          ⋃ j, (L i j \ C j) := by
        intro x hx
        rw [mem_iInter] at hx
        have hxA : x ∈ A := (hx 0).1
        refine mem_iUnion.2 ⟨⌊f ⟨x, hxA⟩ * ((i : ℝ) + 1)⌋, (hmemL i _ ⟨x, hxA⟩).2 rfl,
          fun hxC => (hx (⌊f ⟨x, hxA⟩ * ((i : ℝ) + 1)⌋).natAbs).2 (mem_iUnion₂.2 ⟨_, ?_, hxC⟩)⟩
        rw [Finset.mem_Icc]
        omega
      have hlt : μ.toMeasure le_rfl (⋂ J : ℕ, A \ ⋃ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), C j) <
          δ i := by
        rw [toMeasure_apply _ _ (MeasurableSet.iInter hEm)]
        calc μ (⋂ J : ℕ, A \ ⋃ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), C j)
            ≤ μ (⋃ j, (L i j \ C j)) := measure_mono hinter
          _ ≤ ∑' j, μ (L i j \ C j) := measure_iUnion_le _
          _ ≤ ∑' j, η j := ENNReal.tsum_le_tsum fun j => (hCμ j).le
          _ < δ i := hηsum
      have hlim := tendsto_measure_iInter_atTop (μ := μ.toMeasure le_rfl)
        (fun J => (hEm J).nullMeasurableSet) hanti
        ⟨0, ne_top_of_le_ne_top (by rw [toMeasure_apply _ _ hAm]; exact hAfin.ne)
          (measure_mono sdiff_subset)⟩
      obtain ⟨J, hJ⟩ := (hlim.eventually_lt_const hlt).exists
      exact ⟨J, (toMeasure_apply _ _ (hEm J)).symm.trans_lt hJ⟩
    refine ⟨⋃ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), C j, isClosed_biUnion_finset fun j _ => hCc j,
      iUnion₂_subset fun j _ => (hCL j).trans (hLA i j), hJ, fun a ha => ?_⟩
    -- Near a point of `C j₀`, the closed sets `C j` (`j ≠ j₀`, `|j| ≤ J`) are avoided.
    obtain ⟨j₀, hj₀, haj₀⟩ := mem_iUnion₂.1 ha
    have hfa : ⌊f a * ((i : ℝ) + 1)⌋ = j₀ := (hmemL i j₀ a).1 (hCL j₀ haj₀)
    refine ⟨(⋃ j ∈ (Finset.Icc (-(J : ℤ)) (J : ℤ)).erase j₀, C j)ᶜ,
      (isClosed_biUnion_finset fun j _ => hCc j).isOpen_compl, ?_, ?_⟩
    · rw [mem_compl_iff, mem_iUnion₂]
      rintro ⟨j, hj, haj⟩
      exact (Finset.mem_erase.1 hj).1 (((hmemL i j a).1 (hCL j haj)).symm.trans hfa)
    · rintro b ⟨hbD, hbU⟩
      obtain ⟨j, hj, hbj⟩ := mem_iUnion₂.1 hbD
      have hjj₀ : j = j₀ := by
        by_contra hne
        exact hbU (mem_iUnion₂.2 ⟨j, Finset.mem_erase.2 ⟨hne, hj⟩, hbj⟩)
      exact ((hmemL i j b).1 (hCL j hbj)).trans (hjj₀.trans hfa.symm)
  -- Step 4: `C := ⋂ i, D i` is closed, `C ⊆ A`, and `μ (A \ C) ≤ ∑ μ (A \ D i) < ε`.
  choose D hDc hDA hDμ hDloc using hstep
  have hKA : (⋂ i, D i) ⊆ A := (iInter_subset D 0).trans (hDA 0)
  refine ⟨⋂ i, D i, hKA, isClosed_iInter hDc, ?_, ?_⟩
  · calc μ (A \ ⋂ i, D i) = μ (⋃ i, A \ D i) := by rw [sdiff_iInter]
      _ ≤ ∑' i, μ (A \ D i) := measure_iUnion_le _
      _ ≤ ∑' i, δ i := ENNReal.tsum_le_tsum fun i => (hDμ i).le
      _ < ENNReal.ofReal ε := hδsum
  -- Step 5: on `⋂ i, D i` the step functions `⌊(i + 1) f⌋ / (i + 1)` are locally constant,
  -- hence continuous, and converge uniformly to `f`; so `f` restricted there is continuous.
  have hloc : ∀ (i : ℕ) (x : ↥(⋂ i, D i)), ∀ᶠ y in 𝓝 x,
      ⌊f (Set.inclusion hKA y) * ((i : ℝ) + 1)⌋ = ⌊f (Set.inclusion hKA x) * ((i : ℝ) + 1)⌋ := by
    intro i x
    obtain ⟨U, hU, hxU, hconst⟩ := hDloc i (Set.inclusion hKA x) (mem_iInter.1 x.2 i)
    filter_upwards [(hU.preimage continuous_subtype_val).mem_nhds hxU] with y hy
    exact hconst (Set.inclusion hKA y) ⟨mem_iInter.1 y.2 i, hy⟩
  have hunif : TendstoUniformly
      (fun (i : ℕ) (y : ↥(⋂ i, D i)) =>
        (⌊f (Set.inclusion hKA y) * ((i : ℝ) + 1)⌋ : ℝ) / ((i : ℝ) + 1))
      (f ∘ Set.inclusion hKA) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro r hr
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hr
    filter_upwards [eventually_ge_atTop N] with i hi y
    have hpos : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hNi : 1 / ((i : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hi)
    have hlow : (⌊f (Set.inclusion hKA y) * ((i : ℝ) + 1)⌋ : ℝ) / ((i : ℝ) + 1) ≤
        f (Set.inclusion hKA y) := by
      rw [div_le_iff₀ hpos]
      exact Int.floor_le _
    have hupp : f (Set.inclusion hKA y) <
        (⌊f (Set.inclusion hKA y) * ((i : ℝ) + 1)⌋ : ℝ) / ((i : ℝ) + 1) + 1 / ((i : ℝ) + 1) := by
      rw [← add_div, lt_div_iff₀ hpos]
      exact Int.lt_floor_add_one _
    show dist (f (Set.inclusion hKA y))
      ((⌊f (Set.inclusion hKA y) * ((i : ℝ) + 1)⌋ : ℝ) / ((i : ℝ) + 1)) < r
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  refine hunif.continuous (Frequently.of_forall fun i => continuous_iff_continuousAt.2 fun x => ?_)
  have h : (fun y : ↥(⋂ i, D i) => (⌊f (Set.inclusion hKA y) * ((i : ℝ) + 1)⌋ : ℝ) / ((i : ℝ) + 1))
      =ᶠ[𝓝 x] fun _ => (⌊f (Set.inclusion hKA x) * ((i : ℝ) + 1)⌋ : ℝ) / ((i : ℝ) + 1) := by
    filter_upwards [hloc i x] with y hy
    rw [hy]
  exact (continuousAt_congr h).2 continuousAt_const

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

/-- Simon Ch. 1, Theorems 2.9 and 2.10, from the pinned `Poincare.SimonGMT` library:
`simon_theorem_2_9` at the positive scale `ENNReal.ofReal δ`, and `simon_theorem_2_10`, whose
real exponent `(n : ℝ)` becomes the natural power `n` by `ENNReal.rpow_natCast`. -/
theorem Submission.lebesgue_eq_hausdorff_and_isodiametric :
    LebesgueEqHausdorff ∧ IsodiametricInequality := by
  refine ⟨fun n δ hδ A => ?_, fun n A => ?_⟩
  · exact simon_theorem_2_9 n (ENNReal.ofReal_pos.mpr hδ) A
  · simpa only [ENNReal.rpow_natCast] using simon_theorem_2_10 n A

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

/-- Simon Ch. 1, Theorems 3.3 and 3.6.  Theorem 3.3 (with Lemma 3.4 and Corollary 3.5) is
`simon_theorem_3_3` from the pinned `Poincare.SimonGMT` library, whose statement is identical.
Theorem 3.6 follows the printed proof: `μ ⌞ A` is Borel regular and finite, so Theorem 1.15(2)
(`Submission.borel_regular_approximation`) gives closed `C ⊆ A` with `μ (A \ C)` arbitrarily
small, and Theorem 3.3 for `μ ⌞ A`, `S_t = {x ∉ A : Θ^{*n}(μ, A, x) ≥ t}` and `X \ C` gives
`t · Hⁿ(S_t) ≤ μ (A \ C)`.  The exceptional set is the union of the `S_{1/(k+1)}`. -/
theorem Submission.upper_density_comparison_and_theorem :
    UpperDensityComparison.{u} ∧ UpperDensityTheorem.{u} := by
  have h33 : UpperDensityComparison.{u} := by
    intro X _ μ hμ n hn t ht A₁ A₂ hA hden
    exact simon_theorem_3_3 μ hμ hn A₁ A₂ hA ht hden
  refine ⟨h33, ?_⟩
  intro X _ μ hμ n hn A hA hAfin
  -- `μ ⌞ A` is Borel regular and finite (the remarks after (1.12)).
  let μA : OuterMeasure X := OuterMeasure.restrict A μ
  have hμA : IsBorelRegularOuterMeasure μA := hμ.restrict hA hAfin
  have hμA_apply : ∀ S, μA S = μ (S ∩ A) := fun S => OuterMeasure.restrict_apply A S μ
  -- Theorem 1.15(2) for `μ ⌞ A`, which is open σ-finite with `V_j = X`.
  have hsup := (Submission.borel_regular_approximation X (fun _ hC => hC.isGδ) μA hμA
    ⟨fun _ => univ, fun _ => ⟨isOpen_univ, by rwa [hμA_apply, univ_inter]⟩,
      iUnion_const univ⟩).2 A (isCaratheodoryMeasurable_restrict hA)
  have happrox : ∀ ε : ℝ≥0∞, 0 < ε → ∃ C, C ⊆ A ∧ IsClosed C ∧ μ (A \ C) < ε := by
    intro ε hε
    by_cases hsmall : μ A < ε
    · exact ⟨∅, empty_subset A, isClosed_empty, by rwa [sdiff_empty]⟩
    have hlt : μ A - ε < μA A := by
      rw [hμA_apply, inter_self]
      exact ENNReal.sub_lt_self hAfin.ne (fun h0 => hsmall (by rwa [h0])) hε.ne'
    rw [hsup] at hlt
    obtain ⟨C, hC⟩ := lt_iSup_iff.mp hlt
    obtain ⟨hCA, hC⟩ := lt_iSup_iff.mp hC
    obtain ⟨hCcl, hC⟩ := lt_iSup_iff.mp hC
    rw [hμA_apply, inter_eq_left.mpr hCA] at hC
    refine ⟨C, hCA, hCcl, ?_⟩
    have hCborel : MeasurableSet[borel X] C := by
      let : MeasurableSpace X := borel X
      have : OpensMeasurableSpace X := ⟨le_rfl⟩
      exact hCcl.measurableSet
    have hCcar : μ.IsCaratheodory C := hμ.borel_le_caratheodory C hCborel
    have hsplit : μ A = μ C + μ (A \ C) := by
      simpa only [inter_eq_right.mpr hCA] using hCcar A
    refine (ENNReal.add_lt_add_iff_left (ne_top_of_le_ne_top hAfin.ne (measure_mono hCA))).mp ?_
    rw [← hsplit]
    exact ENNReal.lt_add_of_sub_lt_right (Or.inl hAfin.ne) hC
  -- Theorem 3.3 for `μ ⌞ A`, `S_t ⊆ X \ C`: every level set `S_t`, `t > 0`, is `Hⁿ`-null.
  have hlevel : ∀ t : ℝ, 0 < t → simonHausdorffOuterMeasureReal n
      {x | x ∉ A ∧ ENNReal.ofReal t ≤ dimensionalUpperDensity μ n A x} = 0 := by
    intro t ht
    have hmul : ENNReal.ofReal t * simonHausdorffOuterMeasureReal n
        {x | x ∉ A ∧ ENNReal.ofReal t ≤ dimensionalUpperDensity μ n A x} = 0 := by
      refine le_antisymm (le_of_forall_gt_imp_ge_of_dense fun ε hε => ?_) bot_le
      obtain ⟨C, hCA, hCcl, hCε⟩ := happrox ε hε
      have hSC : {x | x ∉ A ∧ ENNReal.ofReal t ≤ dimensionalUpperDensity μ n A x} ⊆ Cᶜ :=
        fun x hx hxC => hx.1 (hCA hxC)
      refine (h33 X μA hμA n hn t ht.le _ Cᶜ hSC fun x hx => ?_).trans ?_
      · calc ENNReal.ofReal t ≤ dimensionalUpperDensity μ n A x := hx.2
          _ = dimensionalUpperDensity μ n (A \ C) x :=
            (dimensionalUpperDensity_sdiff_of_isClosed μ n A hCcl (hSC hx)).symm
          _ = dimensionalUpperDensity μA n Cᶜ x := by
            unfold dimensionalUpperDensity
            congr 1
            funext r
            rw [dimensionalDensityQuotient, dimensionalDensityQuotient, hμA_apply,
              inter_right_comm, ← Set.sdiff_eq_compl_inter]
      · rw [hμA_apply, ← Set.sdiff_eq_compl_inter]
        exact hCε.le
    exact (mul_eq_zero.mp hmul).resolve_left (ENNReal.ofReal_pos.mpr ht).ne'
  -- `{x ∉ A : Θ^{*n}(μ, A, x) ≠ 0} = ⋃ₖ S_{1/(k+1)}`.
  rw [ae_iff]
  apply measure_mono_null _ (measure_iUnion_null fun k : ℕ =>
    hlevel (1 / ((k : ℝ) + 1)) Nat.one_div_pos_of_nat)
  intro x hx
  obtain ⟨hxA, hx0⟩ := not_imp.mp hx
  obtain ⟨r, -, hr0, hrx⟩ := ENNReal.lt_iff_exists_real_btwn.mp (pos_iff_ne_zero.mpr hx0)
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (ENNReal.ofReal_pos.mp hr0)
  exact mem_iUnion.mpr ⟨k, hxA, (ENNReal.ofReal_le_ofReal hk.le).trans hrx.le⟩

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

/-- Simon Ch. 1, Lemma 3.12, from the pinned `Poincare.SimonGMT` library:
`exists_besicovitchCovering_families` (Mathlib's `Besicovitch.exist_disjoint_covering_families`
with closed balls, `N = Besicovitch.multiplicity ℝⁿ`) for the index type `↥B`; each family is
pushed forward along the injective `Subtype.val`. -/
theorem Submission.besicovitch_covering : BesicovitchCovering := by
  intro n
  refine ⟨Besicovitch.multiplicity (EuclideanSpace ℝ (Fin n)), fun B hpos ⟨R, hR⟩ => ?_⟩
  obtain ⟨D, hdisj, hcover⟩ := exists_besicovitchCovering_families n
    (fun b : B => (b : EuclideanSpace ℝ (Fin n) × ℝ).1)
    (fun b : B => (b : EuclideanSpace ℝ (Fin n) × ℝ).2) (fun b => hpos b b.2) R
    (fun b => hR (mem_image_of_mem Prod.snd b.2))
  refine ⟨fun j => Subtype.val '' D j, fun j => image_subset_iff.2 fun b _ => b.2,
    fun j => Subtype.val_injective.injOn.pairwiseDisjoint_image.2 (hdisj j), ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  obtain ⟨j, hj⟩ := mem_iUnion.1 (hcover ⟨⟨b, hb⟩, rfl⟩)
  obtain ⟨i, hi, hbi⟩ := mem_iUnion₂.1 hj
  exact mem_iUnion.2 ⟨j, mem_iUnion₂.2 ⟨i, mem_image_of_mem Subtype.val hi, hbi⟩⟩

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

/-- Simon Ch. 1, Theorem 3.16 and Corollary 3.17, from the pinned `Poincare.SimonGMT` library
(`simon_theorem_3_16`, `simon_corollary_3_17_of_caratheodory`).  Both hold almost everywhere for
`hμ.toBorelMeasure`, which has the same null sets as `μ` (`toBorelMeasure_apply_all`) and is the
trim of `caratheodoryMeasure μ` to the Borel σ-algebra, so integrals over closed balls agree. -/
theorem Submission.general_density_and_differentiation :
    GeneralDensityTheorem.{u} ∧ LebesgueDifferentiation.{u} := by
  refine ⟨fun X _ μ hμ hopen hV A hA => ?_, fun X _ μ hμ hopen hV f hf hloc => ?_⟩
  · have h : ∀ᵐ x ∂μ, Tendsto (fun ρ : ℝ => μ (A ∩ closedBall x ρ) / μ (closedBall x ρ))
        (𝓝[>] 0) (𝓝 (A.indicator (fun _ => (1 : ℝ≥0∞)) x)) := by
      have h := simon_theorem_3_16 μ hμ hopen hV hA
      rw [ae_iff] at h ⊢
      rwa [hμ.toBorelMeasure_apply_all] at h
    refine ⟨?_, ?_⟩
    · filter_upwards [h] with x hx hxA
      simpa only [indicator_of_mem hxA] using hx
    · filter_upwards [h] with x hx hxA
      simpa only [indicator_of_notMem hxA] using hx
  · have hm : borel X ≤ μ.caratheodory := hμ.borel_le_caratheodory
    have hball : ∀ (x : X) (ρ : ℝ), MeasurableSet[borel X] (closedBall x ρ) := fun _ _ =>
      (MeasurableSpace.measurableSet_generateFrom isClosed_closedBall.isOpen_compl).of_compl
    have htrim : (caratheodoryMeasure μ).trim hm = hμ.toBorelMeasure := by
      refine @Measure.ext X (borel X) _ _ fun s hs => ?_
      rw [trim_measurableSet_eq hm hs, hμ.toBorelMeasure_apply_all]
      exact toMeasure_apply (ms := μ.caratheodory) μ le_rfl (hm s hs)
    have hfae : AEMeasurable f hμ.toBorelMeasure := hμ.aemeasurable_of_caratheodory hopen hf
    have hlint : ∀ x ρ, ∫⁻ y in closedBall x ρ, ENNReal.ofReal |f y| ∂hμ.toBorelMeasure =
        ∫⁻ y in closedBall x ρ, ENNReal.ofReal |f y| ∂caratheodoryMeasure μ := by
      intro x ρ
      rw [← htrim]
      refine setLIntegral_trim_ae hm ?_ (hball x ρ)
      rw [htrim]
      exact (continuous_abs.measurable.comp_aemeasurable hfae).ennreal_ofReal
    have hint : ∀ x ρ, ∫ y in closedBall x ρ, f y ∂hμ.toBorelMeasure =
        ∫ y in closedBall x ρ, f y ∂caratheodoryMeasure μ := by
      intro x ρ
      rw [← htrim, restrict_trim hm _ (hball x ρ), ← integral_trim_ae hm]
      rw [← restrict_trim hm _ (hball x ρ), htrim]
      exact hfae.aestronglyMeasurable.restrict
    have h := simon_corollary_3_17_of_caratheodory μ hμ hopen hV hf fun x => by
      obtain ⟨ρ, hρ, hfin⟩ := hloc x
      exact ⟨ρ, hρ, (hlint x ρ).trans_lt hfin⟩
    rw [ae_iff] at h ⊢
    rw [hμ.toBorelMeasure_apply_all] at h
    simpa only [hint] using h

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

/-- Simon Ch. 1, Theorem 3.24 with clause (0) from 3.23(ii), from the pinned `Poincare.SimonGMT`
library: `simon_theorem_3_23_ii` and `simon_theorem_3_24_i`/`_ii`/`_iii`, whose integrals are
taken against the Borel measure `hμ₀.toBorelMeasure`.  That measure is the trim of
`caratheodoryMeasure μ₀` to `borel X`, and the upper density is a.e. equal to the Borel function
`rnDeriv` (`ae_outerRelativeUpperDensity_eq_rnDeriv`), so `setLIntegral_trim_ae` identifies the
two set integrals over every Borel set. -/
theorem Submission.radon_nikodym_theorem : RadonNikodymTheorem := by
  intro X _ μ μ₀ hμ hopenμ hμ₀ hopenμ₀ hV₀
  have hle : borel X ≤ μ₀.caratheodory := hμ₀.borel_le_caratheodory
  have htrim : (caratheodoryMeasure μ₀).trim hle = hμ₀.toBorelMeasure := by
    refine @Measure.ext X (borel X) _ _ fun s hs => ?_
    rw [trim_measurableSet_eq hle hs, hμ₀.toBorelMeasure_apply hs]
    exact toMeasure_apply (ms := μ₀.caratheodory) μ₀ le_rfl (hle s hs)
  have hmeas : AEMeasurable (outerRelativeUpperDensity μ μ₀)
      ((caratheodoryMeasure μ₀).trim hle) := by
    rw [htrim]
    exact (Measure.measurable_rnDeriv _ _).aemeasurable.congr
      (ae_outerRelativeUpperDensity_eq_rnDeriv μ μ₀ hμ hμ₀ hopenμ hopenμ₀ hV₀).symm
  have hint : ∀ A : Set X, MeasurableSet[borel X] A →
      ∫⁻ x in A, outerRelativeUpperDensity μ μ₀ x ∂hμ₀.toBorelMeasure =
        ∫⁻ x in A, outerRelativeUpperDensity μ μ₀ x ∂caratheodoryMeasure μ₀ := by
    intro A hA
    rw [← htrim]
    exact setLIntegral_trim_ae hle hmeas hA
  refine ⟨?_, fun hAC A hA => ?_, ?_, fun hV => ?_⟩
  · obtain ⟨S, -, hS, hconv, -⟩ := simon_theorem_3_23_ii μ μ₀ hμ hμ₀ hopenμ hopenμ₀ hV₀
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) hS
    by_contra hxS
    exact hx (hconv x hxS).1
  · rw [← hint A hA]
    exact simon_theorem_3_24_i μ μ₀ hμ hμ₀ hopenμ hopenμ₀ hV₀ hAC hA
  · obtain ⟨Z, hZ, hμ₀Z, hdec⟩ := simon_theorem_3_24_ii μ μ₀ hμ hμ₀ hopenμ hopenμ₀ hV₀
    refine ⟨Z, hZ, hμ₀Z, fun A hA => ?_⟩
    have h := hdec A hA
    rw [OuterMeasure.restrict_apply, inter_comm, hint A hA] at h
    exact h
  · obtain ⟨hnull, hdec⟩ := simon_theorem_3_24_iii μ μ₀ hμ hμ₀ hopenμ hopenμ₀ hV₀ hV
    refine ⟨hnull, fun A hA => ?_⟩
    have h := hdec A hA
    rw [OuterMeasure.restrict_apply, inter_comm, hint A hA] at h
    exact h

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

/-- Simon Ch. 1, Theorem 4.12, from the pinned libraries: for the Borel σ-algebra, Mathlib's
`NNRealRMK.rieszMeasure Λ` is regular (`NNRealRMK.rieszMeasure_regular`), so its outer measure is
Radon (`isRadonOuterMeasure_toOuterMeasure`); its Carathéodory integral equals the Borel one
(`integral_radonCaratheodoryMeasure`), which is `Λ f` by `NNRealRMK.integral_rieszMeasure`. -/
theorem Submission.riesz_positive : RieszPositive := by
  intro X _ _ _ Λ
  let : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  refine ⟨(NNRealRMK.rieszMeasure Λ).toOuterMeasure,
    isRadonOuterMeasure_toOuterMeasure _, fun f => ?_⟩
  have hf : StronglyMeasurable (fun x => (f x : ℝ)) :=
    (NNReal.continuous_coe.comp f.continuous).stronglyMeasurable
  change (Λ f : ℝ) =
    ∫ x, (f x : ℝ) ∂radonCaratheodoryMeasure (NNRealRMK.rieszMeasure Λ)
  rw [integral_radonCaratheodoryMeasure _ hf, NNRealRMK.integral_rieszMeasure]

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

/-- Simon Ch. 1, Theorem 4.14, from the pinned `Poincare.SimonGMT` library: `simon_theorem_4_14`
has the same hypotheses (`IsLocallyBoundedCcFunctional L` unfolds to the bounded-above
condition) and integrates against `hμ.toCaratheodoryMeasure`, which is `caratheodoryMeasure μ`.
Its unit-norm clause holds a.e. for that measure, which agrees with `μ` on all sets
(`IsRadonOuterMeasure.toCaratheodoryMeasure_apply_all`), hence `μ`-a.e. -/
theorem Submission.riesz_vector : RieszVector := by
  intro X _ _ _ H _ _ _ L hL
  obtain ⟨μ, hμ, ν, hν, hunit, hrep⟩ := simon_theorem_4_14 L hL
  refine ⟨μ, hμ, ν, hν, ?_, hrep⟩
  rw [ae_iff] at hunit ⊢
  rwa [hμ.toCaratheodoryMeasure_apply_all] at hunit
/-- A countable family of test functions supported in a compact `K` that is uniformly dense among
all test functions supported in `K` (Step 1 of the proof of Simon Ch. 1, Theorem 4.16). The
coordinates of an embedding of `K` into `ℓ^∞` (Urysohn metrization) separate points, so `C(K, ℝ)`
is separable by Stone–Weierstrass; a countable dense subset of the restrictions to `K` of the test
functions supported in `K` lifts to `D`, and off `K` both functions vanish. -/
theorem Submission.rc_cc_countable_dense : ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] (K : Set X), IsCompact K → ∃ D : Set C_c(X, ℝ), D.Countable ∧ (∀ g ∈ D, tsupport g ⊆ K) ∧ ∀ f : C_c(X, ℝ), tsupport f ⊆ K → ∀ ε : ℝ, 0 < ε → ∃ g ∈ D, ∀ x, |f x - g x| ≤ ε := by
  intro X _ _ _ K hK
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  -- `K` embeds into `ℓ^∞`; the coordinates form a countable separating family `h`.
  obtain ⟨e, he⟩ := TopologicalSpace.exists_embedding_l_infty K
  let h : ℕ → C(K, ℝ) := fun n => ⟨fun y => e y n, (continuous_eval_const n).comp he.continuous⟩
  -- `C(K, ℝ)` is separable: by Stone–Weierstrass it is the closure of the algebra generated by
  -- `h`, which is the `ℝ`-span of the countable monoid generated by `h`.
  have hsep : TopologicalSpace.IsSeparable (univ : Set C(K, ℝ)) := by
    have hA : (Algebra.adjoin ℝ (range h)).SeparatesPoints := by
      intro x y hxy
      obtain ⟨n, hn⟩ := DFunLike.ne_iff.mp (he.injective.ne hxy)
      exact ⟨h n, ⟨h n, Algebra.subset_adjoin ⟨n, rfl⟩, rfl⟩, hn⟩
    have htop := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _ hA
    have hcount : (Submonoid.closure (range h) : Set C(K, ℝ)).Countable := by
      have : _root_.Countable (range h) := (Set.countable_range h).to_subtype
      refine (Set.countable_range (fun l : List (range h) => (l.map Subtype.val).prod)).mono ?_
      intro x hx
      obtain ⟨l, hl, rfl⟩ := Submonoid.exists_list_of_mem_closure hx
      lift l to List (range h) using hl
      exact ⟨l, rfl⟩
    have hAsep : TopologicalSpace.IsSeparable (Algebra.adjoin ℝ (range h) : Set C(K, ℝ)) := by
      have hspan : (Algebra.adjoin ℝ (range h) : Set C(K, ℝ)) =
          (Submodule.span ℝ (Submonoid.closure (range h) : Set C(K, ℝ)) : Set C(K, ℝ)) := by
        rw [← Algebra.adjoin_eq_span]; rfl
      rw [hspan]
      exact hcount.isSeparable.span
    have := hAsep.closure
    rwa [← Subalgebra.topologicalClosure_coe, htop, Algebra.coe_top] at this
  -- A countable `T` dense in the restrictions `r f` of the test functions supported in `K`.
  let r : C_c(X, ℝ) → C(K, ℝ) := fun f => (f : C(X, ℝ)).restrict K
  obtain ⟨T, hTsub, hTc, hTdense⟩ :=
    (hsep.mono (subset_univ (r '' {f : C_c(X, ℝ) | tsupport f ⊆ K}))).exists_countable_dense_subset
  -- Lift each element of `T` to a test function supported in `K`.
  have hlift : ∀ t : T, ∃ g : C_c(X, ℝ), tsupport g ⊆ K ∧ r g = t := fun t => hTsub t.2
  choose g hgK hgr using hlift
  have : _root_.Countable T := hTc.to_subtype
  refine ⟨range g, Set.countable_range g, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact hgK t
  -- Within `ε` on `K` by the sup distance; off `K` both functions vanish.
  · intro f hf ε hε
    obtain ⟨t, htT, hft⟩ := Metric.mem_closure_iff.mp (hTdense ⟨f, hf, rfl⟩) ε hε
    refine ⟨g ⟨t, htT⟩, ⟨⟨t, htT⟩, rfl⟩, fun x => ?_⟩
    by_cases hx : x ∈ K
    · have h1 : dist (r f ⟨x, hx⟩) (r (g ⟨t, htT⟩) ⟨x, hx⟩) ≤ dist (r f) t := by
        rw [hgr ⟨t, htT⟩]
        exact ContinuousMap.dist_apply_le_dist _
      have h2 : dist (f x) (g ⟨t, htT⟩ x) ≤ ε := h1.trans hft.le
      rwa [Real.dist_eq] at h2
    · have h1 : f x = 0 := image_eq_zero_of_notMem_tsupport fun h' => hx (hf h')
      have h2 : g ⟨t, htT⟩ x = 0 := image_eq_zero_of_notMem_tsupport fun h' => hx (hgK _ h')
      rw [h1, h2, sub_zero, abs_zero]
      exact hε.le

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

/-- Simon Ch. 1, Theorem 4.16 (corrected), proof Step 3: every `f ∈ C_c(X, ℝ)` is integrable
for the Carathéodory measure of a Radon outer measure `μ`.  Borel regularity (R1) makes open sets
`μ`-measurable, and finiteness on compacts passes to `caratheodoryMeasure μ` by the pinned
`IsRadonOuterMeasure.toCaratheodoryMeasure_apply_all`; Mathlib's
`Continuous.integrable_of_hasCompactSupport` concludes. -/
theorem Submission.rc_cc_integrable : ∀ (X : Type u) [TopologicalSpace X] (μ : OuterMeasure X),
    IsRadonOuterMeasure μ → ∀ f : C_c(X, ℝ), Integrable (fun x => f x) (caratheodoryMeasure μ) := by
  intro X _ μ hμ f
  let : MeasurableSpace X := μ.caratheodory
  have : OpensMeasurableSpace X := ⟨hμ.borel_regular.borel_le_caratheodory⟩
  have : IsFiniteMeasureOnCompacts (caratheodoryMeasure μ) := ⟨fun K hK => by
    rw [show caratheodoryMeasure μ K = μ K from hμ.toCaratheodoryMeasure_apply_all K]
    exact hμ.finite_compacts hK⟩
  exact (map_continuous f).integrable_of_hasCompactSupport f.hasCompactSupport
/-- Simon Ch. 1, Theorem 4.16, the estimate of Steps 2–3 of its proof, for one Radon outer
measure: `f` vanishes off the compact set `tsupport f` (`setIntegral_tsupport`), which has
`caratheodoryMeasure μ`-measure `μ (tsupport f) < ∞` by
`IsRadonOuterMeasure.toCaratheodoryMeasure_apply_all` and (R1), so
`norm_setIntegral_le_of_norm_le_const` bounds the integral over it. -/
theorem Submission.rc_cc_integral_abs_le :
    ∀ (X : Type u) [TopologicalSpace X] (μ : OuterMeasure X), IsRadonOuterMeasure μ →
      ∀ (f : C_c(X, ℝ)) (C : ℝ), (∀ x, |f x| ≤ C) →
        |∫ x, f x ∂caratheodoryMeasure μ| ≤ (μ (tsupport f)).toReal * C := by
  intro X _ μ hμ f C hC
  have hS : caratheodoryMeasure μ (tsupport f) = μ (tsupport f) :=
    hμ.toCaratheodoryMeasure_apply_all (tsupport f)
  rw [← setIntegral_tsupport, mul_comm _ C, ← hS, ← measureReal_def, ← Real.norm_eq_abs]
  exact norm_setIntegral_le_of_norm_le_const
    (hS.trans_lt (hμ.finite_compacts f.hasCompactSupport.isCompact))
    fun x _ => (Real.norm_eq_abs (f x)).trans_le (hC x)
/-- Simon Ch. 1, Theorem 4.16 (corrected), proof Step 4: countably many bounded real sequences
`k ↦ a k i` have a common convergent subsequence (the diagonal argument).  This is the sequential
compactness of a countable product of compact intervals: every `a k` lies in the box
`∏ᵢ [-Cᵢ, Cᵢ]`, compact by Tychonoff (`isCompact_univ_pi`), and `ι → ℝ` is first countable as
`ι` is countable, so Mathlib's `IsCompact.tendsto_subseq` extracts a subsequence converging in the
product topology, i.e. coordinatewise (`tendsto_pi_nhds`). -/
theorem Submission.rc_diagonal_subseq : ∀ (ι : Type u) [Countable ι] (a : ℕ → ι → ℝ),
    (∀ i, ∃ C : ℝ, ∀ k, |a k i| ≤ C) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, ∃ l : ℝ, Tendsto (fun k => a (φ k) i) atTop (𝓝 l) := by
  intro ι _ a ha
  choose C hC using ha
  have hK : IsCompact (Set.pi univ fun i => Icc (-C i) (C i)) :=
    isCompact_univ_pi fun i => isCompact_Icc
  obtain ⟨b, -, φ, hφ, hlim⟩ :=
    hK.tendsto_subseq (x := a) fun k => Set.mem_univ_pi.mpr fun i => abs_le.mp (hC i k)
  exact ⟨φ, hφ, fun i => ⟨b i, tendsto_pi_nhds.mp hlim i⟩⟩

/-- Simon Ch. 1, Theorem 4.16 (corrected), proof Steps 1–4 and the convergence in Step 5: one
subsequence `φ` along which `∫ f dμ_{φ(k)}` converges for every `f ∈ C_c(X, ℝ)`.  `X` is
σ-compact, so it has a compact exhaustion `K j` (`CompactExhaustion.choice`), and
`M j = sup_k μ_k(K j) < ∞`.  `rc_cc_countable_dense` gives countable families `D j`, uniformly
dense among the test functions supported in `K j`; their integrals are bounded by
`M j · sup |g|` (`rc_cc_integral_abs_le`), so `rc_diagonal_subseq` makes them all converge along
one `φ`.  If `tsupport f ⊆ K j` and `|f - g| ≤ η` with `g ∈ D j`, then
`|∫ f dμ_k - ∫ g dμ_k| ≤ M j · η` (`rc_cc_integrable`, `rc_cc_integral_abs_le`), hence
`∫ f dμ_{φ(k)}` is Cauchy. -/
theorem Submission.rc_subseq_integrals_converge : ∀ (X : Type u) [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X] (μ : ℕ → OuterMeasure X),
    (∀ k, IsRadonOuterMeasure (μ k)) → (∀ K : Set X, IsCompact K → ⨆ k, μ k K < ∞) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ f : C_c(X, ℝ), ∃ l : ℝ,
      Tendsto (fun k => ∫ x, f x ∂caratheodoryMeasure (μ (φ k))) atTop (𝓝 l) := by
  intro X _ _ _ _ μ hμ hbdd
  -- Step 1: a compact exhaustion `K j` of the σ-compact space `X`.
  let K := CompactExhaustion.choice X
  -- Step 2: `M j = sup_k μ_k(K j) < ∞` bounds `μ_k(A)` for all `k` and `A ⊆ K j`.
  let M : ℕ → ℝ := fun j => (⨆ k, μ k (K j)).toReal
  have hM : ∀ j k (A : Set X), A ⊆ K j → (μ k A).toReal ≤ M j := fun j k A hA =>
    ENNReal.toReal_mono (hbdd _ (K.isCompact j)).ne
      ((measure_mono (μ := μ k) hA).trans (le_iSup (fun k => μ k (K j)) k))
  -- Step 1: countable families `D j` of test functions in `K j`, uniformly dense among them.
  choose D hDc hDK hDdense using fun j =>
    Submission.rc_cc_countable_dense X (K j) (K.isCompact j)
  let DD := ⋃ j, D j
  have : Countable DD := (countable_iUnion hDc).to_subtype
  -- Steps 2–3: for `g ∈ D j` and every `k`, `|∫ g dμ_k| ≤ M j · sup |g|`.
  have hbound : ∀ g : DD, ∃ C : ℝ, ∀ k,
      |∫ x, (g : C_c(X, ℝ)) x ∂caratheodoryMeasure (μ k)| ≤ C := by
    intro g
    obtain ⟨j, hj⟩ := mem_iUnion.1 g.2
    obtain ⟨C, hC⟩ := (map_continuous (g : C_c(X, ℝ))).bounded_above_of_compact_support
      (g : C_c(X, ℝ)).hasCompactSupport
    refine ⟨M j * |C|, fun k => ?_⟩
    calc |∫ x, (g : C_c(X, ℝ)) x ∂caratheodoryMeasure (μ k)|
        ≤ (μ k (tsupport (g : C_c(X, ℝ)))).toReal * |C| :=
          Submission.rc_cc_integral_abs_le X (μ k) (hμ k) g |C| fun x =>
            ((Real.norm_eq_abs _).symm.trans_le (hC x)).trans (le_abs_self C)
      _ ≤ M j * |C| := mul_le_mul_of_nonneg_right (hM j k _ (hDK j g hj)) (abs_nonneg C)
  -- Step 4: a diagonal subsequence along which `∫ g dμ_{φ(k)}` converges for every `g ∈ D`.
  obtain ⟨φ, hφ, hconv⟩ := Submission.rc_diagonal_subseq DD
    (fun k g => ∫ x, (g : C_c(X, ℝ)) x ∂caratheodoryMeasure (μ k)) hbound
  refine ⟨φ, hφ, fun f => ?_⟩
  -- Step 5: if `tsupport f ⊆ K j`, approximate `f` uniformly within `D j`; the sequence
  -- `∫ f dμ_{φ(k)}` is Cauchy, hence convergent.
  obtain ⟨j, hfK⟩ := K.exists_superset_of_isCompact f.hasCompactSupport.isCompact
  refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.2 fun ε hε => ?_)
  obtain ⟨η, hη, hMη⟩ := exists_pos_mul_lt (div_pos hε three_pos) (M j)
  obtain ⟨g, hgD, hfg⟩ := hDdense j f hfK η hη
  have hfgK : tsupport (f - g : C_c(X, ℝ)) ⊆ K j :=
    (tsupport_sub f g).trans (union_subset hfK (hDK j g hgD))
  have hclose : ∀ k, |∫ x, f x ∂caratheodoryMeasure (μ k) -
      ∫ x, g x ∂caratheodoryMeasure (μ k)| < ε / 3 := fun k => by
    rw [← integral_sub (Submission.rc_cc_integrable X (μ k) (hμ k) f)
      (Submission.rc_cc_integrable X (μ k) (hμ k) g)]
    calc |∫ x, f x - g x ∂caratheodoryMeasure (μ k)|
        ≤ (μ k (tsupport (f - g : C_c(X, ℝ)))).toReal * η :=
          Submission.rc_cc_integral_abs_le X (μ k) (hμ k) (f - g) η hfg
      _ ≤ M j * η := mul_le_mul_of_nonneg_right (hM j k _ hfgK) hη.le
      _ < ε / 3 := hMη
  obtain ⟨lg, hlg⟩ := hconv ⟨g, mem_iUnion.2 ⟨j, hgD⟩⟩
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hlg.cauchySeq (ε / 3) (div_pos hε three_pos)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hg : |∫ x, g x ∂caratheodoryMeasure (μ (φ m)) -
      ∫ x, g x ∂caratheodoryMeasure (μ (φ n))| < ε / 3 := by
    simpa only [Real.dist_eq] using hN m hm n hn
  have h₁ := abs_lt.1 (hclose (φ m))
  have h₂ := abs_lt.1 (hclose (φ n))
  have h₃ := abs_lt.1 hg
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2, h₃.1, h₃.2]

/-- Step 6 of the proof of Simon Ch. 1, Theorem 4.16 (corrected): given Theorem 4.12
(`RieszPositive`), a positive `ℝ`-linear `Λ : C_c(X, ℝ) → ℝ` is integration against a Radon
outer measure. On `C_c(X, ℝ≥0)`, `Λ` is the `ℝ≥0`-linear map
`toNNRealLinear (PositiveLinearMap.mk₀ Λ hΛ)`, which Theorem 4.12 represents by a Radon `μ`.
For `f ∈ C_c(X, ℝ)` write `f = f⁺ - f⁻` (`nnrealPart_sub_nnrealPart_neg`); both parts are
integrable (`rc_cc_integrable`), so `Λ f = ∫ f⁺ - ∫ f⁻ = ∫ f`. -/
theorem Submission.rc_riesz_real : RieszPositive.{u} → ∀ (X : Type u) [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ),
    (∀ f : C_c(X, ℝ), 0 ≤ f → 0 ≤ Λ f) → ∃ μ : OuterMeasure X, IsRadonOuterMeasure μ ∧
      ∀ f : C_c(X, ℝ), Λ f = ∫ x, f x ∂caratheodoryMeasure μ := by
  intro hRiesz X _ _ _ Λ hΛ
  -- Steps 1–3: `λ h := Λ h̃` is `ℝ≥0`-linear on `C_c(X, ℝ≥0)`; Theorem 4.12 represents it.
  obtain ⟨μ, hμ, hint⟩ := hRiesz X
    (CompactlySupportedContinuousMap.toNNRealLinear (PositiveLinearMap.mk₀ Λ hΛ))
  have hrep (g : C_c(X, ℝ≥0)) : Λ g.toReal = ∫ x, g.toReal x ∂caratheodoryMeasure μ := by
    simp only [CompactlySupportedContinuousMap.toReal_apply]
    exact hint g
  refine ⟨μ, hμ, fun f => ?_⟩
  -- Steps 4–6: `f = f⁺ - f⁻`, where both parts are integrable by `rc_cc_integrable`.
  rw [← CompactlySupportedContinuousMap.nnrealPart_sub_nnrealPart_neg f, map_sub]
  simp only [CompactlySupportedContinuousMap.sub_apply]
  rw [integral_sub (Submission.rc_cc_integrable X μ hμ _) (Submission.rc_cc_integrable X μ hμ _),
    hrep, hrep]

/-- Simon Ch. 1, Theorem 4.16 (corrected), from its child nodes, following Steps 1–7 of the proof.
`rc_subseq_integrals_converge` (Steps 1–4 and the convergence in Step 5) gives one subsequence
`φ` along which every `∫ f dμ_{φ(k)}` converges. The limit functional `F` is `ℝ`-linear
(`rc_cc_integrable` for additivity of the integral; limits are unique) and positive (Step 5).
`rc_riesz_real`, applied to Theorem 4.12 (`riesz_positive`), represents `F` by a Radon outer
measure (Steps 6–7). -/
theorem Submission.radon_compactness : RadonCompactness := by
  intro X _ _ _ _ μ hμ hbdd
  -- Steps 1–4 and the convergence in Step 5: one subsequence for all test functions.
  obtain ⟨φ, hφ, hconv⟩ := Submission.rc_subseq_integrals_converge X μ hμ hbdd
  choose l hl using hconv
  -- Step 5: `F f := lim_k ∫ f dμ_{φ(k)}` is `ℝ`-linear and positive.
  let F : C_c(X, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := l
      map_add' := fun f g => by
        refine tendsto_nhds_unique (hl (f + g)) (((hl f).add (hl g)).congr fun k => ?_)
        simp only [CompactlySupportedContinuousMap.add_apply]
        exact (integral_add (Submission.rc_cc_integrable X _ (hμ _) f)
          (Submission.rc_cc_integrable X _ (hμ _) g)).symm
      map_smul' := fun c f => by
        rw [RingHom.id_apply, smul_eq_mul]
        refine tendsto_nhds_unique (hl (c • f)) (((hl f).const_mul c).congr fun k => ?_)
        simp only [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul]
        exact (integral_const_mul c _).symm }
  have hF : ∀ f : C_c(X, ℝ), 0 ≤ f → 0 ≤ F f := fun f hf =>
    ge_of_tendsto' (hl f) fun k => integral_nonneg fun x => hf x
  -- Step 6: Theorem 4.12 (`riesz_positive`) represents `F` by a Radon outer measure.
  obtain ⟨μlim, hμlim, hrep⟩ := Submission.rc_riesz_real Submission.riesz_positive X F hF
  -- Step 7: `∫ f dμ_{φ(k)} → F f = ∫ f dμlim`.
  refine ⟨φ, hφ, μlim, hμlim, fun f => ?_⟩
  rw [← hrep f]
  exact hl f

/-- The headline results of Simon, *Introduction to GMT*, Chapter 1 (pp. 1–38). -/
theorem main_theorem : CaratheodoryCriterion ∧ BorelRegularApproximation ∧ LusinTheorem ∧ LebesgueEqHausdorff ∧ IsodiametricInequality ∧ UpperDensityComparison ∧ UpperDensityTheorem ∧ BesicovitchCovering ∧ GeneralDensityTheorem ∧ LebesgueDifferentiation ∧ RadonNikodymTheorem ∧ HausdorffDensityBounds ∧ RieszPositive ∧ RieszVector ∧ RadonCompactness := by
  -- Each conjunct is supplied by its child node.  The paired children
  -- `upper_density_comparison_and_theorem` and `general_density_and_differentiation` use one
  -- universe `u` for both halves, while the statement gives those conjuncts independent universe
  -- parameters, so each half is projected from its own occurrence of the child.
  exact ⟨Submission.caratheodory_criterion,
    Submission.borel_regular_approximation,
    Submission.lusin_theorem,
    Submission.lebesgue_eq_hausdorff_and_isodiametric.1,
    Submission.lebesgue_eq_hausdorff_and_isodiametric.2,
    Submission.upper_density_comparison_and_theorem.1,
    Submission.upper_density_comparison_and_theorem.2,
    Submission.besicovitch_covering,
    Submission.general_density_and_differentiation.1,
    Submission.general_density_and_differentiation.2,
    Submission.radon_nikodym_theorem,
    Submission.hausdorff_density_bounds,
    Submission.riesz_positive,
    Submission.riesz_vector,
    Submission.radon_compactness⟩

/-- Simon Ch. 1, Theorem 3.26, with (2.4)–(2.6).  (1) `Hⁿ` is additive on positively
separated sets (`simonHausdorffOuterMeasureReal_isMetric`), so Theorem 1.13 makes every Borel
set `Hⁿ`-measurable; with the Borel hulls of (2.6), `Hⁿ` and `σ = Hⁿ ⌞ A` are Borel regular, and
`σ` is finite.  For `t > 1` and `E ⊆ A` on which `Θ^{*n}(Hⁿ, A, ·) ≥ t`, Theorem 3.3 applied to
`σ` on `A ∩ U` for open `U ⊇ E`, followed by outer regularity of `σ` (Theorem 1.15(1)), gives
`t · Hⁿ(E) ≤ Hⁿ(E) < ∞`, so `Hⁿ(E) = 0`; take a countable union over rational `t > 1`.
(2) is the `Hⁿ_∞` covering argument `simon_theorem_3_26_ii`, which does not use measurability. -/
theorem Submission.hausdorff_density_bounds : HausdorffDensityBounds := by
  intro X _ n hn A hA
  refine ⟨fun hAfin => ?_, fun hfin => ?_⟩
  · have hsep : ∀ E F : Set X, (∃ r : ℝ, 0 < r ∧ ∀ a ∈ E, ∀ b ∈ F, r ≤ dist a b) →
        simonHausdorffOuterMeasureReal n (E ∪ F) =
          simonHausdorffOuterMeasureReal n E + simonHausdorffOuterMeasureReal n F := by
      rintro E F ⟨r, hr, hEF⟩
      refine simonHausdorffOuterMeasureReal_isMetric n E F
        ⟨ENNReal.ofReal r, (ENNReal.ofReal_pos.mpr hr).ne', fun a ha b hb => ?_⟩
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (hEF a ha b hb)
    have hH : IsBorelRegularOuterMeasure (simonHausdorffOuterMeasureReal (X := X) n) :=
      ⟨fun E hE => Submission.caratheodory_criterion X _ hsep E hE,
        (simonHausdorffOuterMeasureReal_isBorelRegular hn).exists_borel_superset⟩
    obtain ⟨σ, hσ_def⟩ : ∃ σ : OuterMeasure X,
        σ = OuterMeasure.restrict A (simonHausdorffOuterMeasureReal n) := ⟨_, rfl⟩
    have hσapp : ∀ S, σ S = simonHausdorffOuterMeasureReal n (S ∩ A) := fun S => by
      rw [hσ_def, OuterMeasure.restrict_apply]
    have hσ : IsBorelRegularOuterMeasure σ := by
      rw [hσ_def]
      exact hH.restrict hA hAfin
    have hσopen : IsOpenSigmaFinite σ :=
      ⟨fun _ => univ, fun _ => ⟨isOpen_univ, by rw [hσapp, univ_inter]; exact hAfin⟩,
        iUnion_const univ⟩
    have hσden : ∀ S ⊆ A, ∀ x, dimensionalUpperDensity σ n S x =
        dimensionalUpperDensity (simonHausdorffOuterMeasureReal n) n S x := by
      intro S hS x
      unfold dimensionalUpperDensity dimensionalDensityQuotient
      congr 1
      funext r
      rw [hσapp, inter_eq_left.mpr (inter_subset_left.trans hS)]
    have hlevel : ∀ t : ℝ, 1 < t → ∀ E ⊆ A, (∀ x ∈ E, ENNReal.ofReal t ≤
        dimensionalUpperDensity (simonHausdorffOuterMeasureReal n) n A x) →
        simonHausdorffOuterMeasureReal n E = 0 := by
      intro t ht E hEA hEt
      have hbound : ENNReal.ofReal t * simonHausdorffOuterMeasureReal n E ≤
          simonHausdorffOuterMeasureReal n E := calc
        ENNReal.ofReal t * simonHausdorffOuterMeasureReal n E ≤
            ⨅ (U : Set X) (_ : E ⊆ U) (_ : IsOpen U), σ U := by
          refine le_iInf fun U => le_iInf fun hEU => le_iInf fun hU => ?_
          refine (Submission.upper_density_comparison_and_theorem.1 X σ hσ n hn t
            (zero_le_one.trans ht.le) E (A ∩ U) (fun x hx => ⟨hEA hx, hEU hx⟩)
            (fun x hx => ?_)).trans (measure_mono inter_subset_right)
          rw [hσden (A ∩ U) inter_subset_left x, dimensionalUpperDensity_inter_of_mem_nhds
            (simonHausdorffOuterMeasureReal n) n A U x (hU.mem_nhds (hEU hx))]
          exact hEt x hx
        _ = σ E := ((Submission.borel_regular_approximation X (fun C hC => hC.isGδ) σ hσ
          hσopen).1 E).symm
        _ = simonHausdorffOuterMeasureReal n E := by rw [hσapp, inter_eq_left.mpr hEA]
      by_contra hne
      have hfin : simonHausdorffOuterMeasureReal n E ≠ ∞ :=
        ((measure_mono hEA).trans_lt hAfin).ne
      have hlt := ENNReal.mul_lt_mul_left hne hfin (ENNReal.one_lt_ofReal.mpr ht)
      rw [one_mul] at hlt
      exact hlt.not_ge hbound
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) (measure_iUnion_null fun q : ℚ =>
      measure_iUnion_null fun hq : (1 : ℝ) < q => hlevel q hq
        {x | x ∈ A ∧ ENNReal.ofReal q ≤
          dimensionalUpperDensity (simonHausdorffOuterMeasureReal n) n A x}
        (fun x hx => hx.1) (fun x hx => hx.2))
    simp only [mem_ofPred_eq, not_imp, not_le] at hx
    obtain ⟨q, -, hq1, hqx⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hx.2
    exact mem_iUnion₂.mpr ⟨q, ENNReal.one_lt_ofReal.mp hq1, hx.1, hqx.le⟩
  · rw [ae_iff]
    simpa only [not_imp, not_le] using simon_theorem_3_26_ii hn hA hfin

end GMT.Ch01
