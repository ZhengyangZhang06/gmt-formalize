module

public import Poincare.SimonGMT.Chapter01.SteinerDiameter

@[expose] public section

/-!
# Volume comparison for coordinate Steiner symmetrization

Fubini and the exact slice-length identity show that outer volume cannot
decrease.  Taking closure afterward gives a compact replacement without
increasing diameter.  This route deliberately does not require an unproved
measurability or compactness assertion about the assembled Steiner set.
-/

open Metric Set MeasureTheory
open scoped ENNReal

namespace Poincare.SimonGMT.Chapter01

/-- Coordinate Steiner symmetrization of a compact Euclidean set cannot
decrease Lebesgue outer volume.  The argument compares the symmetrized set
with its measurable hull, so no measurability premise about that set is used. -/
theorem volume_le_volume_simonSteinerSymmetrization
    {n : ℕ} (j : Fin n) {A : Set (EuclideanSpace ℝ (Fin n))} (hA : IsCompact A) :
    volume A ≤ volume (simonSteinerSymmetrization j A) := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ n =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j
    let φ : ℝ × (Fin n → ℝ) → EuclideanSpace ℝ (Fin (n + 1)) :=
      fun p => WithLp.toLp 2 (e.symm p)
    have hφ : MeasurePreserving φ volume volume :=
      (PiLp.volume_preserving_toLp (Fin (n + 1))).comp
        (MeasurePreserving.symm e (volume_preserving_piFinSuccAbove _ j))
    have hφcoord (t : ℝ) (z : Fin n → ℝ) : φ (t, z) j = t :=
      Fin.insertNth_apply_same (α := fun _ : Fin (n + 1) => ℝ) j t z
    let S := simonSteinerSymmetrization j A
    let T := toMeasurable volume S
    have hT : MeasurableSet T := measurableSet_toMeasurable volume S
    have hTA : S ⊆ T := subset_toMeasurable volume S
    have hslice (t : ℝ) (z : Fin n → ℝ) :
        simonCoordinateSlice j A (φ (t, z)) = (fun s => φ (s, z)) ⁻¹' A := by
      ext s
      change (WithLp.toLp 2 (Function.update (j.insertNth t z) j s) ∈ A) ↔
        WithLp.toLp 2 (j.insertNth s z) ∈ A
      rw [Fin.update_insertNth]
    have hfinite (z : Fin n → ℝ) : volume ((fun t => φ (t, z)) ⁻¹' A) ≠ ∞ := by
      have hproj : IsCompact ((fun x : EuclideanSpace ℝ (Fin (n + 1)) => x j) '' A) :=
        hA.image (by fun_prop)
      have hsub : (fun t => φ (t, z)) ⁻¹' A ⊆
          (fun x : EuclideanSpace ℝ (Fin (n + 1)) => x j) '' A := by
        intro t ht
        exact ⟨φ (t, z), ht, hφcoord t z⟩
      exact (measure_lt_top_of_subset hsub hproj.measure_lt_top.ne).ne
    calc
      volume A = volume (φ ⁻¹' A) := (hφ.measure_preimage hA.measurableSet.nullMeasurableSet).symm
      _ = ∫⁻ z : Fin n → ℝ, volume ((fun t => φ (t, z)) ⁻¹' A) :=
        Measure.prod_apply_symm (hA.measurableSet.preimage hφ.measurable)
      _ = ∫⁻ z : Fin n → ℝ, volume (simonCenteredSlice ((fun t => φ (t, z)) ⁻¹' A)) := by
        apply lintegral_congr
        intro z
        exact (volume_simonCenteredSlice (hfinite z)).symm
      _ ≤ ∫⁻ z : Fin n → ℝ, volume ((fun t => φ (t, z)) ⁻¹' T) := by
        apply lintegral_mono
        intro z
        apply measure_mono
        intro t ht
        apply hTA
        change φ (t, z) j ∈ simonCenteredSlice (simonCoordinateSlice j A (φ (t, z)))
        rw [hφcoord, hslice]
        exact ht
      _ = volume (φ ⁻¹' T) := (Measure.prod_apply_symm (hT.preimage hφ.measurable)).symm
      _ = volume T := hφ.measure_preimage hT.nullMeasurableSet
      _ = volume S := measure_toMeasurable S

/-- The closed version of coordinate Steiner symmetrization. -/
noncomputable def simonCompactSteiner {n : ℕ} (j : Fin n)
    (A : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  closure (simonSteinerSymmetrization j A)

/-- Closing the symmetrized set still does not increase diameter. -/
theorem ediam_simonCompactSteiner_le {n : ℕ} (j : Fin n)
    (A : Set (EuclideanSpace ℝ (Fin n))) : ediam (simonCompactSteiner j A) ≤ ediam A := by
  rw [simonCompactSteiner, ediam_closure]
  exact ediam_simonSteinerSymmetrization_le j A

/-- The closed replacement of a compact set is compact. -/
theorem isCompact_simonCompactSteiner {n : ℕ} (j : Fin n)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : IsCompact A) :
    IsCompact (simonCompactSteiner j A) := by
  apply Bornology.IsBounded.isCompact_closure
  apply isBounded_iff_ediam_ne_top.mpr
  exact ne_top_of_le_ne_top hA.isBounded.ediam_ne_top (ediam_simonSteinerSymmetrization_le j A)

/-- The compact replacement has at least the original volume. -/
theorem volume_le_volume_simonCompactSteiner {n : ℕ} (j : Fin n)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : IsCompact A) :
    volume A ≤ volume (simonCompactSteiner j A) :=
  (volume_le_volume_simonSteinerSymmetrization j hA).trans (measure_mono subset_closure)

end Poincare.SimonGMT.Chapter01
