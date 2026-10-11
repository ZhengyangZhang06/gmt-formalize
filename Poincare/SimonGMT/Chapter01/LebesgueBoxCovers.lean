module

public import Poincare.SimonGMT.Chapter01.LebesgueOuterUniqueness

@[expose] public section

/-!
# Simon GMT, Chapter 1, (2.7): Lebesgue outer measure from open boxes

The cost is defined from endpoint differences, independently of `volume`.
The final infimum uses a subset of `ℕ` as index set, so both finite and
countably infinite covers are included without charging for empty padding.
-/

open Set MeasureTheory
open scoped ENNReal

namespace Poincare.SimonGMT.Chapter01

/-- Simon's box cost: the product of positive side lengths for a bounded
open coordinate box, and infinity for a set with no such representation. -/
noncomputable def simonLebesgueBoxCost {n : ℕ} (C : Set (Fin n → ℝ)) : ℝ≥0∞ :=
  ⨅ (a : Fin n → ℝ) (b : Fin n → ℝ) (_ : ∀ i, a i < b i)
    (_ : C = pi univ fun i => Ioo (a i) (b i)), ∏ i, ENNReal.ofReal (b i - a i)

/-- The literal box-cover outer measure of Simon (2.7). -/
noncomputable def simonLebesgueOuterMeasure (n : ℕ) : OuterMeasure (Fin n → ℝ) :=
  OuterMeasure.boundedBy simonLebesgueBoxCost

/-- The endpoint cost always bounds Lebesgue outer measure. -/
theorem volume_le_simonLebesgueBoxCost {n : ℕ} (C : Set (Fin n → ℝ)) :
    volume C ≤ simonLebesgueBoxCost C := by
  refine le_iInf fun a => le_iInf fun b => le_iInf fun _ => le_iInf fun hC => ?_
  rw [hC, lebesgueMeasure_openBox]

/-- On each allowed box, the independently defined cost is its side-length
product. -/
theorem simonLebesgueBoxCost_openBox {n : ℕ} (a b : Fin n → ℝ)
    (hab : ∀ i, a i < b i) :
    simonLebesgueBoxCost (pi univ fun i => Ioo (a i) (b i)) =
      ∏ i, ENNReal.ofReal (b i - a i) := by
  refine le_antisymm ?_ ?_
  · exact iInf_le_of_le a (iInf_le_of_le b (iInf_le_of_le hab (iInf_le _ rfl)))
  · rw [← lebesgueMeasure_openBox n a b]
    exact volume_le_simonLebesgueBoxCost _

/-- The literal box-cover construction agrees with the usual Lebesgue outer
measure in every natural dimension. -/
theorem simonLebesgueOuterMeasure_eq_volume (n : ℕ) :
    simonLebesgueOuterMeasure n = (volume : Measure (Fin n → ℝ)).toOuterMeasure := by
  have hlower : (volume : Measure (Fin n → ℝ)).toOuterMeasure ≤
      simonLebesgueOuterMeasure n :=
    OuterMeasure.le_boundedBy.mpr volume_le_simonLebesgueBoxCost
  refine le_antisymm (outerMeasure_le_volume_of_openBox _ ?_) hlower
  intro a b hab
  refine le_antisymm ?_ ?_
  · exact (OuterMeasure.boundedBy_le _).trans_eq (simonLebesgueBoxCost_openBox a b hab)
  · rw [← lebesgueMeasure_openBox n a b]
    exact hlower _

/-- Simon (2.7), with the infimum written explicitly over all finite or
countable families of positive-side-length open boxes.  Indexing by subsets
of `ℕ` includes the empty cover and handles dimension zero correctly. -/
theorem simon_theorem_2_7 (n : ℕ) (A : Set (Fin n → ℝ)) :
    volume A =
      ⨅ (J : Set ℕ) (a : J → Fin n → ℝ) (b : J → Fin n → ℝ) (_ : ∀ j i, a j i < b j i)
        (_ : A ⊆ ⋃ j : J, pi univ fun i => Ioo (a j i) (b j i)),
        ∑' j : J, ∏ i, ENNReal.ofReal (b j i - a j i) := by
  classical
  refine le_antisymm ?_ ?_
  · refine le_iInf fun J => le_iInf fun a => le_iInf fun b =>
      le_iInf fun _ => le_iInf fun hcover => ?_
    calc
      volume A ≤ volume (⋃ j : J, pi univ fun i => Ioo (a j i) (b j i)) :=
        measure_mono hcover
      _ ≤ ∑' j : J, volume (pi univ fun i => Ioo (a j i) (b j i)) := measure_iUnion_le _
      _ = ∑' j : J, ∏ i, ENNReal.ofReal (b j i - a j i) := by
        simp_rw [lebesgueMeasure_openBox]
  · change _ ≤ (volume : Measure (Fin n → ℝ)).toOuterMeasure A
    rw [← simonLebesgueOuterMeasure_eq_volume, simonLebesgueOuterMeasure,
      OuterMeasure.boundedBy_apply]
    refine le_iInf fun C => le_iInf fun hcover => ?_
    by_cases hfin : (∑' j, ⨆ _ : (C j).Nonempty, simonLebesgueBoxCost (C j)) = ∞
    · rw [hfin]
      exact le_top
    let J : Set ℕ := {j | (C j).Nonempty}
    have hboxes (j : J) : ∃ a b : Fin n → ℝ,
        (∀ i, a i < b i) ∧ C j = pi univ fun i => Ioo (a i) (b i) := by
      have hcost : simonLebesgueBoxCost (C j) < ∞ :=
        ((le_iSup (fun _ : (C j).Nonempty => simonLebesgueBoxCost (C j)) j.property).trans
          (ENNReal.le_tsum (f := fun k => ⨆ _ : (C k).Nonempty,
            simonLebesgueBoxCost (C k)) j)).trans_lt (lt_top_iff_ne_top.mpr hfin)
      obtain ⟨a, b, hab, heq, _⟩ :=
        (show ∃ a b : Fin n → ℝ, ∃ hab : ∀ i, a i < b i,
          ∃ heq : C j = pi univ fun i => Ioo (a i) (b i),
            (∏ i, ENNReal.ofReal (b i - a i)) < ∞ by
          simpa only [simonLebesgueBoxCost, iInf_lt_iff] using hcost)
      exact ⟨a, b, hab, heq⟩
    choose a b hab heq using hboxes
    have hcover' : A ⊆ ⋃ j : J, pi univ fun i => Ioo (a j i) (b j i) := by
      intro x hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hx)
      refine mem_iUnion.mpr ⟨⟨j, ⟨x, hj⟩⟩, ?_⟩
      rw [← heq]
      exact hj
    refine iInf_le_of_le J (iInf_le_of_le a (iInf_le_of_le b
      (iInf_le_of_le hab (iInf_le_of_le hcover' ?_))))
    calc
      (∑' j : J, ∏ i, ENNReal.ofReal (b j i - a j i)) =
          ∑' j : J, simonLebesgueBoxCost (C j) := by
        apply tsum_congr
        intro j
        rw [heq j, simonLebesgueBoxCost_openBox _ _ (hab j)]
      _ ≤ ∑' j : J, ⨆ _ : (C j).Nonempty, simonLebesgueBoxCost (C j) :=
        ENNReal.tsum_le_tsum fun j => le_iSup (fun _ => _) j.property
      _ ≤ ∑' j, ⨆ _ : (C j).Nonempty, simonLebesgueBoxCost (C j) :=
        Summable.tsum_le_tsum_of_inj ((↑) : J → ℕ) Subtype.val_injective
          (fun _ _ => bot_le) (fun _ => le_rfl) ENNReal.summable ENNReal.summable

end Poincare.SimonGMT.Chapter01
