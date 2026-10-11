module

public import Poincare.SimonGMT.Chapter01.Regularity

public section

/-!
# Simon GMT, Chapter 1, completion of the regularity argument

The Borel inner-regularity statement in `Regularity` is not by itself Simon
Theorem 1.15(2), because Simon allows every Carathéodory-measurable set.  This
module supplies the missing completion argument.  The key point is that open
`sigma`-finiteness lets us replace an arbitrary Carathéodory-measurable set by
a Borel subset modulo an outer-null set.
-/

open Filter Set
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter01

universe u

variable {X : Type u} [TopologicalSpace X]

/-- A finite Carathéodory-measurable set contains a Borel subset with null
complement.  This is the finite-measure completion step used implicitly in
Simon Theorem 1.15(2). -/
theorem IsBorelRegularOuterMeasure.exists_borel_subset_mod_null_of_lt_top
    {mu : MeasureTheory.OuterMeasure X} (hmu : IsBorelRegularOuterMeasure mu)
    {A : Set X} (hA : IsCaratheodoryMeasurable mu A) (hAfin : mu A < ∞) :
    ∃ B : Set X, B ⊆ A ∧ @MeasurableSet X (borel X) B ∧
      mu (A \ B) = 0 ∧ mu B = mu A := by
  obtain ⟨S, hAS, hS, hmuS⟩ := hmu.exists_borel_superset A
  have hSdiffA : mu (S \ A) = 0 := by
    have hsplit := hA S
    have hinter : S ∩ A = A := inter_eq_right.mpr hAS
    rw [hinter, hmuS] at hsplit
    apply (ENNReal.add_right_inj (ne_of_lt hAfin)).mp
    simpa using hsplit.symm
  obtain ⟨N, hSdiffAN, hN, hmuN⟩ :=
    hmu.exists_borel_superset (S \ A)
  have hNzero : mu N = 0 := hmuN.trans hSdiffA
  refine ⟨S \ N, ?_, hS.diff hN, ?_, ?_⟩
  · intro x hx
    rcases hx with ⟨hxS, hxN⟩
    by_contra hxA
    exact hxN (hSdiffAN ⟨hxS, hxA⟩)
  · apply MeasureTheory.measure_mono_null _ hNzero
    intro x hx
    by_contra hxN
    exact hx.2 ⟨hAS hx.1, hxN⟩
  · rw [MeasureTheory.measure_sdiff_null hNzero, hmuS]

/-- Under Simon's open `sigma`-finiteness hypothesis, every
Carathéodory-measurable set contains a Borel subset modulo an outer-null set,
without a global finiteness assumption. -/
theorem IsBorelRegularOuterMeasure.exists_borel_subset_mod_null
    {mu : MeasureTheory.OuterMeasure X} (hmu : IsBorelRegularOuterMeasure mu)
    (hopen : IsOpenSigmaFinite mu) {A : Set X}
    (hA : IsCaratheodoryMeasurable mu A) :
    ∃ B : Set X, B ⊆ A ∧ @MeasurableSet X (borel X) B ∧
      mu (A \ B) = 0 ∧ mu B = mu A := by
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  rcases (isOpenSigmaFinite_iff mu).mp hopen with ⟨V, hV, hcover⟩
  have hAV : ∀ n, IsCaratheodoryMeasurable mu (A ∩ V n) := fun n =>
    mu.isCaratheodory_inter hA
      (hmu.borel_le_caratheodory _ (hV n).1.measurableSet)
  have hAVfinite : ∀ n, mu (A ∩ V n) < ∞ := fun n =>
    (mu.mono inter_subset_right).trans_lt (hV n).2
  choose B hBsub hBmeas hBnull hBmeasure using fun n =>
    hmu.exists_borel_subset_mod_null_of_lt_top (hAV n) (hAVfinite n)
  let D : Set X := ⋃ n, B n
  have hDsub : D ⊆ A := by
    intro x hx
    obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
    exact (hBsub n hxn).1
  have hDmeas : @MeasurableSet X (borel X) D := MeasurableSet.iUnion hBmeas
  have hADsub : A \ D ⊆ ⋃ n, (A ∩ V n) \ B n := by
    intro x hx
    have hxcover : x ∈ ⋃ n, V n := by simpa [hcover]
    obtain ⟨n, hxn⟩ := mem_iUnion.mp hxcover
    refine mem_iUnion.mpr ⟨n, ⟨⟨hx.1, hxn⟩, ?_⟩⟩
    intro hxB
    exact hx.2 (mem_iUnion.mpr ⟨n, hxB⟩)
  have hUnionNull : mu (⋃ n, (A ∩ V n) \ B n) = 0 :=
    MeasureTheory.measure_iUnion_null hBnull
  have hDnull : mu (A \ D) = 0 :=
    MeasureTheory.measure_mono_null hADsub hUnionNull
  refine ⟨D, hDsub, hDmeas, hDnull, ?_⟩
  have hremove := MeasureTheory.measure_sdiff_null (μ := mu) (s := A) hDnull
  have hset : A \ (A \ D) = D := by
    ext x
    simp only [Set.mem_sdiff]
    tauto
  rwa [hset] at hremove

section Metrizable

variable [TopologicalSpace.PseudoMetrizableSpace X] [SecondCountableTopology X]

/-- Simon Theorem 1.15(2) for every Carathéodory-measurable set, completing
the Borel-only theorem in `Regularity`. -/
theorem IsBorelRegularOuterMeasure.measure_eq_iSup_isClosed
    {mu : MeasureTheory.OuterMeasure X} (hmu : IsBorelRegularOuterMeasure mu)
    (hopen : IsOpenSigmaFinite mu) {A : Set X}
    (hA : IsCaratheodoryMeasurable mu A) :
    mu A = ⨆ (C : Set X) (_ : C ⊆ A) (_ : IsClosed C), mu C := by
  obtain ⟨B, hBA, hB, _, hmuB⟩ :=
    hmu.exists_borel_subset_mod_null hopen hA
  have hinnerB := hmu.borel_measure_eq_iSup_isClosed hopen hB
  apply le_antisymm
  · rw [← hmuB, hinnerB]
    refine iSup_le fun C => iSup_le fun hCB => iSup_le fun hCclosed => ?_
    exact le_iSup_of_le C <|
      le_iSup_of_le (hCB.trans hBA) <| le_iSup_of_le hCclosed le_rfl
  · refine iSup_le fun C => iSup_le fun hCA => iSup_le fun _ => ?_
    exact mu.mono hCA

/-- Simon Remark 1.16 for every Carathéodory-measurable set: in the
sigma-compact metrizable setting, compact subsets give the same inner
approximation as closed subsets. -/
theorem IsBorelRegularOuterMeasure.measure_eq_iSup_isCompact
    [SigmaCompactSpace X]
    {mu : MeasureTheory.OuterMeasure X} (hmu : IsBorelRegularOuterMeasure mu)
    (hopen : IsOpenSigmaFinite mu) {A : Set X}
    (hA : IsCaratheodoryMeasurable mu A) :
    mu A = ⨆ (K : Set X) (_ : K ⊆ A) (_ : IsCompact K), mu K := by
  obtain ⟨B, hBA, hB, _, hmuB⟩ :=
    hmu.exists_borel_subset_mod_null hopen hA
  have hinnerB := hmu.borel_measure_eq_iSup_isCompact hopen hB
  apply le_antisymm
  · rw [← hmuB, hinnerB]
    refine iSup_le fun K => iSup_le fun hKB => iSup_le fun hKcompact => ?_
    exact le_iSup_of_le K <|
      le_iSup_of_le (hKB.trans hBA) <| le_iSup_of_le hKcompact le_rfl
  · refine iSup_le fun K => iSup_le fun hKA => iSup_le fun _ => ?_
    exact mu.mono hKA

/-- The closed-set approximation form of Simon Theorem 1.15(2) for a finite
Carathéodory-measurable set. -/
theorem IsBorelRegularOuterMeasure.exists_isClosed_sdiff_lt
    {mu : MeasureTheory.OuterMeasure X} (hmu : IsBorelRegularOuterMeasure mu)
    (hopen : IsOpenSigmaFinite mu) {A : Set X}
    (hA : IsCaratheodoryMeasurable mu A) (hAfin : mu A ≠ ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ C : Set X, C ⊆ A ∧ IsClosed C ∧ mu (A \ C) < ε := by
  obtain ⟨B, hBA, hB, hAnull, hmuB⟩ :=
    hmu.exists_borel_subset_mod_null hopen hA
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  let nu : MeasureTheory.Measure X := hmu.toBorelMeasure
  letI : MeasureTheory.IsLocallyFiniteMeasure nu :=
    hmu.toBorelMeasure_isLocallyFinite hopen
  letI : MeasureTheory.Measure.WeaklyRegular nu := by infer_instance
  obtain ⟨C, hCB, hCclosed, hBC⟩ :=
    hB.exists_isClosed_sdiff_lt (μ := nu) (by simpa [nu, hmuB] using hAfin) hε
  refine ⟨C, hCB.trans hBA, hCclosed, ?_⟩
  have hsubset : A \ C ⊆ (A \ B) ∪ (B \ C) := by
    intro x hx
    by_cases hxB : x ∈ B
    · exact Or.inr ⟨hxB, hx.2⟩
    · exact Or.inl ⟨hx.1, hxB⟩
  calc
    mu (A \ C) ≤ mu ((A \ B) ∪ (B \ C)) := mu.mono hsubset
    _ ≤ mu (A \ B) + mu (B \ C) := MeasureTheory.measure_union_le _ _
    _ = mu (B \ C) := by rw [hAnull, zero_add]
    _ = nu (B \ C) := by simp [nu]
    _ < ε := hBC

end Metrizable

end Poincare.SimonGMT.Chapter01
