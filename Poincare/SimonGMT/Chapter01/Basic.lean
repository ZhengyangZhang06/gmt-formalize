module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.MeasureTheory.Measure.OuterMeasure
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Topology.UniformSpace.Cauchy

public section

/-!
# Simon GMT, Chapter 1, §1: basic notions

This module restates and connects the first measure-theoretic results in Leon
Simon's *Introduction to Geometric Measure Theory* to Mathlib's genuine
`ℝ≥0∞`-valued outer measures.  Source numbers refer to the printed text.
-/

open Filter Function Set
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter01

universe u

variable {X : Type u}

/-- Simon (1.1): countable subadditivity for a set covered by a sequence. -/
theorem outerMeasure_countable_subadditive (μ : MeasureTheory.OuterMeasure X)
    (A : Set X) (C : ℕ → Set X) (hA : A ⊆ ⋃ n, C n) :
    μ A ≤ ∑' n, μ (C n) :=
  (μ.mono hA).trans (MeasureTheory.measure_iUnion_le (μ := μ) C)

/-- Simon Definition 1.2: his measurable sets are precisely Mathlib's
Carathéodory-measurable sets for the outer measure. -/
abbrev IsCaratheodoryMeasurable (μ : MeasureTheory.OuterMeasure X) (A : Set X) : Prop :=
  μ.IsCaratheodory A

/-- The observation after Simon (1.12): every `μ`-Carathéodory set remains
Carathéodory measurable after restriction to an arbitrary set `Y`. -/
theorem isCaratheodoryMeasurable_restrict
    {μ : MeasureTheory.OuterMeasure X} {A Y : Set X}
    (hA : IsCaratheodoryMeasurable μ A) :
    IsCaratheodoryMeasurable (MeasureTheory.OuterMeasure.restrict Y μ) A := by
  change (MeasureTheory.OuterMeasure.restrict Y μ).IsCaratheodory A
  apply (MeasureTheory.OuterMeasure.isCaratheodory_iff_le'
    (MeasureTheory.OuterMeasure.restrict Y μ)).mpr
  intro S
  simp only [MeasureTheory.OuterMeasure.restrict_apply]
  have h := (MeasureTheory.OuterMeasure.isCaratheodory_iff_le' μ).mp hA (S ∩ Y)
  simpa only [sdiff_eq, inter_assoc, inter_left_comm, inter_comm] using h

/-- The cutting identity in Simon Definition 1.2. -/
theorem isCaratheodoryMeasurable_iff (μ : MeasureTheory.OuterMeasure X) (A : Set X) :
    IsCaratheodoryMeasurable μ A ↔
      ∀ S, μ S = μ (S \ A) + μ (S ∩ A) := by
  change (∀ S, μ S = μ (S ∩ A) + μ (S \ A)) ↔ _
  constructor <;> intro h S
  · simpa [add_comm] using h S
  · simpa [add_comm] using h S

/-- Simon Remark 1.3: it suffices to verify the difficult inequality on test
sets of finite outer measure. -/
theorem isCaratheodoryMeasurable_iff_split_le_finite
    (μ : MeasureTheory.OuterMeasure X) (A : Set X) :
    IsCaratheodoryMeasurable μ A ↔
      ∀ S, μ S < ∞ → μ (S \ A) + μ (S ∩ A) ≤ μ S := by
  constructor
  · intro h S _
    rw [(isCaratheodoryMeasurable_iff μ A).mp h S]
  · intro h
    change μ.IsCaratheodory A
    apply (MeasureTheory.OuterMeasure.isCaratheodory_iff_le' μ).mpr
    intro S
    by_cases htop : μ S = ∞
    · simp [htop]
    · simpa [add_comm] using h S (lt_top_iff_ne_top.mpr htop)

/-- The empty set is Carathéodory measurable, part of Simon Lemma 1.6. -/
theorem isCaratheodoryMeasurable_empty (μ : MeasureTheory.OuterMeasure X) :
    IsCaratheodoryMeasurable μ (∅ : Set X) :=
  μ.isCaratheodory_empty

/-- Complements preserve Carathéodory measurability, part of Simon Lemma 1.6. -/
theorem IsCaratheodoryMeasurable.compl {μ : MeasureTheory.OuterMeasure X}
    {A : Set X} (hA : IsCaratheodoryMeasurable μ A) :
    IsCaratheodoryMeasurable μ Aᶜ :=
  μ.isCaratheodory_compl hA

/-- Countable unions preserve Carathéodory measurability, completing the
σ-algebra assertion in Simon Lemma 1.6. -/
theorem isCaratheodoryMeasurable_iUnion (μ : MeasureTheory.OuterMeasure X)
    (A : ℕ → Set X) (hA : ∀ n, IsCaratheodoryMeasurable μ (A n)) :
    IsCaratheodoryMeasurable μ (⋃ n, A n) :=
  μ.isCaratheodory_iUnion hA

/-- Every subset of outer measure zero is Carathéodory measurable, the null-set
assertion in Simon Lemma 1.6. -/
theorem isCaratheodoryMeasurable_of_outerMeasure_eq_zero
    (μ : MeasureTheory.OuterMeasure X) {A : Set X} (hA : μ A = 0) :
    IsCaratheodoryMeasurable μ A := by
  change μ.IsCaratheodory A
  apply (MeasureTheory.OuterMeasure.isCaratheodory_iff_le' μ).mpr
  intro S
  have hzero : μ (S ∩ A) = 0 := by
    apply le_antisymm
    · exact (μ.mono inter_subset_right).trans_eq hA
    · exact bot_le
  rw [hzero, zero_add]
  exact μ.mono sdiff_subset

/-- Simon Remark 1.5(1): a countable intersection of measurable sets is
measurable.  This is the intersection closure derived in the source from
complements and countable unions. -/
theorem measurableSet_iInter_countable [MeasurableSpace X]
    {ι : Type*} [Countable ι] (A : ι → Set X)
    (hA : ∀ i, MeasurableSet (A i)) : MeasurableSet (⋂ i, A i) :=
  MeasurableSet.iInter hA

/-- Simon Remark 1.5(2): intersections of collections of `σ`-algebras are
again `σ`-algebras.  In Mathlib the intersection is the complete-lattice
infimum, and this theorem records its sets explicitly. -/
theorem measurableSet_iInf_iff {ι : Type*} (m : ι → MeasurableSpace X)
    (A : Set X) :
    @MeasurableSet X (⨅ i, m i) A ↔ ∀ i, @MeasurableSet X (m i) A :=
  MeasurableSpace.measurableSet_iInf

/-- Simon Remark 1.5(2): the Borel `σ`-algebra is equivalently generated by
the open sets or by the closed sets. -/
theorem borel_eq_generateFrom_open_closed [TopologicalSpace X] :
    borel X = MeasurableSpace.generateFrom {A : Set X | IsOpen A} ∧
      borel X = MeasurableSpace.generateFrom {A : Set X | IsClosed A} :=
  ⟨rfl, borel_eq_generateFrom_isClosed⟩

/-- Simon Remark 1.7 in its full form: intersecting an arbitrary test set with
a countable disjoint union of Carathéodory-measurable sets is additive. -/
theorem outerMeasure_inter_iUnion_eq_tsum_of_pairwise_disjoint
    (μ : MeasureTheory.OuterMeasure X) (A : ℕ → Set X)
    (hA : ∀ n, IsCaratheodoryMeasurable μ (A n))
    (hdisjoint : Pairwise (Disjoint on A)) (S : Set X) :
    μ (S ∩ ⋃ n, A n) = ∑' n, μ (S ∩ A n) := by
  have hA' : ∀ n,
      IsCaratheodoryMeasurable (MeasureTheory.OuterMeasure.restrict S μ) (A n) :=
    fun n ↦ isCaratheodoryMeasurable_restrict (hA n)
  simpa only [MeasureTheory.OuterMeasure.restrict_apply, inter_comm] using
    (MeasureTheory.OuterMeasure.f_iUnion
      (MeasureTheory.OuterMeasure.restrict S μ) hA' hdisjoint)

/-- The `S = univ` specialization of Simon Remark 1.7. -/
theorem outerMeasure_iUnion_eq_tsum_of_pairwise_disjoint
    (μ : MeasureTheory.OuterMeasure X) (A : ℕ → Set X)
    (hA : ∀ n, IsCaratheodoryMeasurable μ (A n))
    (hdisjoint : Pairwise (Disjoint on A)) :
    μ (⋃ n, A n) = ∑' n, μ (A n) := by
  simpa using
    outerMeasure_inter_iUnion_eq_tsum_of_pairwise_disjoint
      μ A hA hdisjoint Set.univ

/-- Simon (1.8): continuity from below for an increasing sequence of
Carathéodory-measurable sets. -/
theorem tendsto_outerMeasure_iUnion_atTop
    (μ : MeasureTheory.OuterMeasure X) (A : ℕ → Set X)
    (hA : ∀ n, IsCaratheodoryMeasurable μ (A n)) (hmono : Monotone A) :
    Tendsto (fun n ↦ μ (A n)) atTop (𝓝 (μ (⋃ n, A n))) := by
  let _ : MeasurableSpace X := μ.caratheodory
  let ν : MeasureTheory.Measure X := μ.toMeasure le_rfl
  have hA' : ∀ n, MeasurableSet (A n) := hA
  have hν := MeasureTheory.tendsto_measure_iUnion_atTop (μ := ν) hmono
  have hUnion : MeasurableSet (⋃ n, A n) := MeasurableSet.iUnion hA'
  have hνA : ∀ n, ν (A n) = μ (A n) := fun n ↦
    MeasureTheory.toMeasure_apply μ le_rfl (hA' n)
  have hνUnion : ν (⋃ n, A n) = μ (⋃ n, A n) :=
    MeasureTheory.toMeasure_apply μ le_rfl hUnion
  have hfun : ν ∘ A = fun n ↦ μ (A n) := funext hνA
  rw [hfun, hνUnion] at hν
  exact hν

/-- Simon (1.9): continuity from above for a decreasing sequence, assuming one
member has finite outer measure. -/
theorem tendsto_outerMeasure_iInter_atTop
    (μ : MeasureTheory.OuterMeasure X) (A : ℕ → Set X)
    (hA : ∀ n, IsCaratheodoryMeasurable μ (A n)) (hanti : Antitone A)
    (hfinite : ∃ n, μ (A n) < ∞) :
    Tendsto (fun n ↦ μ (A n)) atTop (𝓝 (μ (⋂ n, A n))) := by
  let _ : MeasurableSpace X := μ.caratheodory
  let ν : MeasureTheory.Measure X := μ.toMeasure le_rfl
  have hA' : ∀ n, MeasurableSet (A n) := hA
  have hfiniteν : ∃ n, ν (A n) ≠ ∞ := by
    obtain ⟨n, hn⟩ := hfinite
    refine ⟨n, ?_⟩
    rw [MeasureTheory.toMeasure_apply μ le_rfl (hA' n)]
    exact ne_of_lt hn
  have hν := MeasureTheory.tendsto_measure_iInter_atTop
    (μ := ν) (fun n ↦ (hA' n).nullMeasurableSet) hanti hfiniteν
  have hInter : MeasurableSet (⋂ n, A n) := MeasurableSet.iInter hA'
  have hνA : ∀ n, ν (A n) = μ (A n) := fun n ↦
    MeasureTheory.toMeasure_apply μ le_rfl (hA' n)
  have hνInter : ν (⋂ n, A n) = μ (⋂ n, A n) :=
    MeasureTheory.toMeasure_apply μ le_rfl hInter
  have hfun : ν ∘ A = fun n ↦ μ (A n) := funext hνA
  rw [hfun, hνInter] at hν
  exact hν

/-- Simon's regularity notion preceding Remark 1.10: every set has a
Carathéodory-measurable hull of equal outer measure. -/
def IsRegularOuterMeasure (μ : MeasureTheory.OuterMeasure X) : Prop :=
  ∀ A : Set X, ∃ B : Set X,
    A ⊆ B ∧ IsCaratheodoryMeasurable μ B ∧ μ B = μ A

/-- Simon Remark 1.10: a regular outer measure is continuous from below even
when the increasing sets are not assumed measurable. -/
theorem IsRegularOuterMeasure.tendsto_iUnion_atTop
    {μ : MeasureTheory.OuterMeasure X} (hμ : IsRegularOuterMeasure μ)
    (A : ℕ → Set X) (hmono : Monotone A) :
    Tendsto (fun n ↦ μ (A n)) atTop (𝓝 (μ (⋃ n, A n))) := by
  let _ : MeasurableSpace X := μ.caratheodory
  let ν : MeasureTheory.Measure X := μ.toMeasure le_rfl
  have hνeq : ∀ S : Set X, ν S = μ S := by
    intro S
    obtain ⟨B, hSB, hB, hμB⟩ := hμ S
    apply le_antisymm
    · calc
        ν S ≤ ν B := MeasureTheory.measure_mono hSB
        _ = μ B := MeasureTheory.toMeasure_apply μ le_rfl hB
        _ = μ S := hμB
    · exact MeasureTheory.le_toMeasure_apply μ le_rfl S
  have hν := MeasureTheory.tendsto_measure_iUnion_atTop (μ := ν) hmono
  have hfun : ν ∘ A = fun n ↦ μ (A n) := funext fun n ↦ hνeq (A n)
  rw [hfun, hνeq (⋃ n, A n)] at hν
  exact hν

/-- Simon's Borel-regularity notion preceding Remark 1.11. -/
def IsBorelRegularOuterMeasure [TopologicalSpace X]
    (μ : MeasureTheory.OuterMeasure X) : Prop :=
  borel X ≤ μ.caratheodory ∧
    ∀ A : Set X, ∃ B : Set X,
      A ⊆ B ∧ @MeasurableSet X (borel X) B ∧ μ B = μ A

/-- The Borel-measurability component of Simon's Borel-regularity
condition.  This public eliminator lets downstream modules use the bundled
definition without reproving its unfolding. -/
theorem IsBorelRegularOuterMeasure.borel_le_caratheodory
    [TopologicalSpace X] {μ : MeasureTheory.OuterMeasure X}
    (hμ : IsBorelRegularOuterMeasure μ) : borel X ≤ μ.caratheodory :=
  hμ.1

/-- The equal-measure Borel-hull component of Simon's Borel-regularity
condition. -/
theorem IsBorelRegularOuterMeasure.exists_borel_superset
    [TopologicalSpace X] {μ : MeasureTheory.OuterMeasure X}
    (hμ : IsBorelRegularOuterMeasure μ) (A : Set X) :
    ∃ B : Set X, A ⊆ B ∧ @MeasurableSet X (borel X) B ∧ μ B = μ A :=
  hμ.2 A

/-- Borel regularity implies Simon regularity. -/
theorem IsBorelRegularOuterMeasure.isRegular [TopologicalSpace X]
    {μ : MeasureTheory.OuterMeasure X} (hμ : IsBorelRegularOuterMeasure μ) :
    IsRegularOuterMeasure μ := by
  intro A
  obtain ⟨B, hAB, hB, hμB⟩ := hμ.2 A
  exact ⟨B, hAB, hμ.1 B hB, hμB⟩

/-- The converse construction in Simon Remark 1.11: a Borel-regular outer
measure restricts to a countably additive measure on the Borel σ-algebra. -/
noncomputable def IsBorelRegularOuterMeasure.toBorelMeasure
    [TopologicalSpace X] {μ : MeasureTheory.OuterMeasure X}
    (hμ : IsBorelRegularOuterMeasure μ) :
    @MeasureTheory.Measure X (borel X) :=
  @MeasureTheory.OuterMeasure.toMeasure X (borel X) μ hμ.1

/-- The Borel measure reconstructed in Remark 1.11 agrees with the original
outer measure on every Borel set. -/
@[simp] theorem IsBorelRegularOuterMeasure.toBorelMeasure_apply
    [TopologicalSpace X] {μ : MeasureTheory.OuterMeasure X}
    (hμ : IsBorelRegularOuterMeasure μ) {B : Set X}
    (hB : @MeasurableSet X (borel X) B) :
    hμ.toBorelMeasure B = μ B :=
  @MeasureTheory.toMeasure_apply X (borel X) μ hμ.1 B hB

/-- The full agreement assertion in Simon Remark 1.11: Borel regularity
upgrades agreement from Borel sets to every set, when a measure is evaluated
through its canonical outer measure. -/
@[simp] theorem IsBorelRegularOuterMeasure.toBorelMeasure_apply_all
    [TopologicalSpace X] {μ : MeasureTheory.OuterMeasure X}
    (hμ : IsBorelRegularOuterMeasure μ) (A : Set X) :
    hμ.toBorelMeasure A = μ A := by
  obtain ⟨B, hAB, hB, hBA⟩ := hμ.2 A
  apply le_antisymm
  · calc
      hμ.toBorelMeasure A ≤ hμ.toBorelMeasure B :=
        MeasureTheory.measure_mono hAB
      _ = μ B := hμ.toBorelMeasure_apply hB
      _ = μ A := hBA
  · exact @MeasureTheory.le_toMeasure_apply X (borel X) μ hμ.1 A

/-- Equivalent outer-measure formulation of the full agreement in Simon
Remark 1.11. -/
@[simp] theorem IsBorelRegularOuterMeasure.toOuterMeasure_toBorelMeasure
    [TopologicalSpace X] {μ : MeasureTheory.OuterMeasure X}
    (hμ : IsBorelRegularOuterMeasure μ) :
    @MeasureTheory.Measure.toOuterMeasure X (borel X) hμ.toBorelMeasure = μ := by
  ext A
  exact hμ.toBorelMeasure_apply_all A

/-- One direction of Simon Remark 1.11: the outer measure induced by a Borel
measure is Borel regular and agrees with it on Borel sets. -/
theorem measure_toOuterMeasure_isBorelRegular
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (ν : MeasureTheory.Measure X) :
    IsBorelRegularOuterMeasure ν.toOuterMeasure := by
  constructor
  · rw [← BorelSpace.measurable_eq]
    exact MeasureTheory.le_toOuterMeasure_caratheodory ν
  · intro A
    obtain ⟨B, hAB, hB, hνB⟩ := MeasureTheory.exists_measurable_superset ν A
    refine ⟨B, hAB, ?_, hνB⟩
    rw [← BorelSpace.measurable_eq (α := X)]
    exact hB

/-- The Borel-regularity assertion following Simon (1.12): restricting to a
Carathéodory-measurable set of finite measure preserves Borel regularity. -/
theorem IsBorelRegularOuterMeasure.restrict
    [TopologicalSpace X] {μ : MeasureTheory.OuterMeasure X}
    (hμ : IsBorelRegularOuterMeasure μ) {Y : Set X}
    (hY : IsCaratheodoryMeasurable μ Y) (hYfinite : μ Y < ∞) :
    IsBorelRegularOuterMeasure (MeasureTheory.OuterMeasure.restrict Y μ) := by
  constructor
  · intro B hB
    have hcar : IsCaratheodoryMeasurable μ B := hμ.1 B hB
    exact isCaratheodoryMeasurable_restrict hcar
  · intro A
    obtain ⟨B₁, hYB₁, hB₁, hμB₁⟩ := hμ.2 Y
    have hB₁Yzero : μ (B₁ \ Y) = 0 := by
      have hsplit := hY B₁
      have hinter : B₁ ∩ Y = Y := inter_eq_right.mpr hYB₁
      rw [hinter, hμB₁] at hsplit
      apply (ENNReal.add_right_inj (ne_of_lt hYfinite)).mp
      simpa using hsplit.symm
    obtain ⟨B₂, hB₁YB₂, hB₂, hμB₂⟩ := hμ.2 (B₁ \ Y)
    have hB₂zero : μ B₂ = 0 := hμB₂.trans hB₁Yzero
    obtain ⟨B₃, hAYB₃, hB₃, hμB₃⟩ := hμ.2 (A ∩ Y)
    let B : Set X := B₁ᶜ ∪ B₂ ∪ B₃
    have hAB : A ⊆ B := by
      intro x hxA
      by_cases hxY : x ∈ Y
      · exact Or.inr (hAYB₃ ⟨hxA, hxY⟩)
      · by_cases hxB₁ : x ∈ B₁
        · exact Or.inl (Or.inr (hB₁YB₂ ⟨hxB₁, hxY⟩))
        · exact Or.inl (Or.inl hxB₁)
    have hB : @MeasurableSet X (borel X) B :=
      (hB₁.compl.union hB₂).union hB₃
    refine ⟨B, hAB, hB, ?_⟩
    simp only [MeasureTheory.OuterMeasure.restrict_apply]
    apply le_antisymm
    · calc
        μ (B ∩ Y) ≤ μ (B₂ ∪ B₃) := by
          apply μ.mono
          intro x hx
          rcases hx.1 with hx₁₂ | hxB₃
          · rcases hx₁₂ with hxB₁c | hxB₂
            · exact False.elim (hxB₁c (hYB₁ hx.2))
            · exact Or.inl hxB₂
          · exact Or.inr hxB₃
        _ ≤ μ B₂ + μ B₃ := MeasureTheory.measure_union_le B₂ B₃
        _ = μ (A ∩ Y) := by rw [hB₂zero, zero_add, hμB₃]
    · exact μ.mono fun x hx ↦ ⟨Or.inr (hAYB₃ hx), hx.2⟩

/-- The covering component of Simon Definition 1.14: the space is covered by
countably many open sets of finite outer measure.  Simon applies this only to
Borel-regular outer measures; see the bundled predicate below. -/
def IsOpenSigmaFinite [TopologicalSpace X] (μ : MeasureTheory.OuterMeasure X) : Prop :=
  ∃ V : ℕ → Set X,
    (∀ n, IsOpen (V n) ∧ μ (V n) < ∞) ∧ ⋃ n, V n = (Set.univ : Set X)

/-- Unfolding theorem for Simon's open `σ`-finiteness condition. -/
theorem isOpenSigmaFinite_iff [TopologicalSpace X]
    (μ : MeasureTheory.OuterMeasure X) :
    IsOpenSigmaFinite μ ↔
      ∃ V : ℕ → Set X,
        (∀ n, IsOpen (V n) ∧ μ (V n) < ∞) ∧
          ⋃ n, V n = (Set.univ : Set X) :=
  Iff.rfl

/-- Simon Definition 1.14 with both of its requirements bundled. -/
def IsOpenSigmaFiniteBorelRegularOuterMeasure [TopologicalSpace X]
    (μ : MeasureTheory.OuterMeasure X) : Prop :=
  IsBorelRegularOuterMeasure μ ∧ IsOpenSigmaFinite μ

/-- Local finiteness for an outer measure, in the open-neighborhood form used
immediately after Simon Definition 1.14. -/
def IsLocallyFiniteOuterMeasure [TopologicalSpace X]
    (μ : MeasureTheory.OuterMeasure X) : Prop :=
  ∀ x : X, ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ μ U < ∞

/-- The observation after Simon Definition 1.14: on a second-countable space,
local finiteness supplies a countable open cover by finite-measure sets. -/
theorem IsBorelRegularOuterMeasure.isOpenSigmaFinite_of_secondCountable
    [TopologicalSpace X] [SecondCountableTopology X]
    {μ : MeasureTheory.OuterMeasure X} (hμ : IsBorelRegularOuterMeasure μ)
    (hloc : IsLocallyFiniteOuterMeasure μ) : IsOpenSigmaFinite μ := by
  let ν : @MeasureTheory.Measure X (borel X) := hμ.toBorelMeasure
  letI : MeasureTheory.IsLocallyFiniteMeasure ν := by
    constructor
    intro x
    obtain ⟨U, hxU, hU, hμU⟩ := hloc x
    refine ⟨U, hU.mem_nhds hxU, ?_⟩
    simpa [ν] using hμU
  let S := MeasureTheory.Measure.finiteSpanningSetsInOpen' ν
  refine ⟨S.set, ⟨?_, S.spanning⟩⟩
  intro n
  refine ⟨S.set_mem n, ?_⟩
  simpa [ν] using S.finite n

/-- In particular, Simon's separable-metric hypothesis implies the
second-countability used by the preceding theorem. -/
theorem IsBorelRegularOuterMeasure.isOpenSigmaFinite_of_separableSpace
    [PseudoMetricSpace X]
    (hsep : TopologicalSpace.IsSeparable (Set.univ : Set X))
    {μ : MeasureTheory.OuterMeasure X} (hμ : IsBorelRegularOuterMeasure μ)
    (hloc : IsLocallyFiniteOuterMeasure μ) : IsOpenSigmaFinite μ := by
  letI : TopologicalSpace.SeparableSpace X :=
    TopologicalSpace.isSeparable_univ_iff.mp hsep
  letI : SecondCountableTopology X := inferInstance
  exact hμ.isOpenSigmaFinite_of_secondCountable hloc

/-- Simon (1.12): evaluation of the outer-measure restriction. -/
theorem outerMeasure_restrict_apply (μ : MeasureTheory.OuterMeasure X)
    (Y Z : Set X) :
    MeasureTheory.OuterMeasure.restrict Y μ Z = μ (Z ∩ Y) :=
  MeasureTheory.OuterMeasure.restrict_apply Y Z μ

end Poincare.SimonGMT.Chapter01
