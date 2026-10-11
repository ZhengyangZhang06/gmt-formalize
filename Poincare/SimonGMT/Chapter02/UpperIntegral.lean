module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

public section

/-!
# Simon GMT, Chapter 2, Remark 1.10: upper Lebesgue integrals

Simon defines the upper integral of an arbitrary nonnegative function as the
infimum of the integrals of its measurable majorants.  This file gives that
definition for `ℝ≥0∞`-valued functions and proves the three assertions in the
remark: existence of a minimizing measurable majorant, its a.e. uniqueness
when the upper integral is finite, and monotone convergence without a
measurability assumption on the original functions.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter02

universe u

variable {α : Type u} [MeasurableSpace α]

/-- A measurable pointwise majorant of an arbitrary `ℝ≥0∞`-valued function. -/
def MeasurableMajorant (f : α → ℝ≥0∞) :=
  {g : α → ℝ≥0∞ // Measurable g ∧ f ≤ g}

/-- Simon Remark 1.10: the upper Lebesgue integral is the infimum of the
Lebesgue integrals of all measurable majorants. -/
noncomputable def upperLebesgueIntegral (μ : Measure α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ g : MeasurableMajorant f, ∫⁻ x, g.1 x ∂μ

/-- Every admissible measurable majorant bounds the upper integral. -/
theorem upperLebesgueIntegral_le_lintegral (μ : Measure α) {f g : α → ℝ≥0∞}
    (hg : Measurable g) (hfg : f ≤ g) :
    upperLebesgueIntegral μ f ≤ ∫⁻ x, g x ∂μ := by
  exact iInf_le_of_le (⟨g, hg, hfg⟩ : MeasurableMajorant f) le_rfl

/-- On measurable functions Simon's upper integral is the usual Lebesgue
integral. -/
theorem upperLebesgueIntegral_eq_lintegral (μ : Measure α) {f : α → ℝ≥0∞}
    (hf : Measurable f) :
    upperLebesgueIntegral μ f = ∫⁻ x, f x ∂μ := by
  apply le_antisymm
  · exact upperLebesgueIntegral_le_lintegral μ hf le_rfl
  · apply le_iInf
    intro g
    exact lintegral_mono g.property.2

/-- Simon's upper integral is monotone for arbitrary functions. -/
theorem upperLebesgueIntegral_mono (μ : Measure α) {f g : α → ℝ≥0∞}
    (hfg : f ≤ g) :
    upperLebesgueIntegral μ f ≤ upperLebesgueIntegral μ g := by
  apply le_iInf
  intro h
  exact upperLebesgueIntegral_le_lintegral μ h.property.1
    (hfg.trans h.property.2)

/-- The infimum in Simon's definition is attained by a measurable majorant,
including when the upper integral is infinite. -/
theorem exists_measurableMajorant_lintegral_eq_upperLebesgueIntegral
    (μ : Measure α) (f : α → ℝ≥0∞) :
    ∃ g : α → ℝ≥0∞,
      Measurable g ∧ f ≤ g ∧
        ∫⁻ x, g x ∂μ = upperLebesgueIntegral μ f := by
  let I := upperLebesgueIntegral μ f
  by_cases hI : I = ∞
  · refine ⟨fun _ ↦ ∞, measurable_const, fun _ ↦ le_top, ?_⟩
    have hI' : upperLebesgueIntegral μ f = ∞ := hI
    have hle : upperLebesgueIntegral μ f ≤ ∫⁻ _ : α, ∞ ∂μ :=
      upperLebesgueIntegral_le_lintegral μ measurable_const (fun _ ↦ le_top)
    rw [hI']
    exact top_unique (hI' ▸ hle)
  · let ε : ℕ → ℝ≥0∞ := fun n ↦ ((n + 1 : ℕ) : ℝ≥0∞)⁻¹
    have hε_ne (n : ℕ) : ε n ≠ 0 := by
      simp [ε]
    have happrox (n : ℕ) :
        ∃ g : MeasurableMajorant f,
          (∫⁻ x, g.1 x ∂μ) < I + ε n := by
      have hlt : I < I + ε n := ENNReal.lt_add_right hI (hε_ne n)
      simpa only [I, upperLebesgueIntegral] using (iInf_lt_iff.mp hlt)
    choose g hg using happrox
    let G : α → ℝ≥0∞ := fun x ↦ ⨅ n, (g n).1 x
    have hGmeas : Measurable G := by
      exact Measurable.iInf fun n ↦ (g n).property.1
    have hfG : f ≤ G := by
      intro x
      exact le_iInf fun n ↦ (g n).property.2 x
    refine ⟨G, hGmeas, hfG, le_antisymm ?_ ?_⟩
    · apply ENNReal.le_of_forall_pos_le_add
      intro δ hδ _
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
      calc
        (∫⁻ x, G x ∂μ) ≤ ∫⁻ x, (g n).1 x ∂μ :=
          lintegral_mono fun x ↦ iInf_le_of_le n le_rfl
        _ ≤ I + ε n := (hg n).le
        _ ≤ I + (δ : ℝ≥0∞) := by
          gcongr
          simpa [ε, one_div] using ENNReal.coe_le_coe.mpr hn.le
    · exact upperLebesgueIntegral_le_lintegral μ hGmeas hfG

/-- When the upper integral is finite, its minimizing measurable majorant is
unique almost everywhere, as asserted in Simon Remark 1.10. -/
theorem ae_eq_of_lintegral_eq_upperLebesgueIntegral
    (μ : Measure α) {f g h : α → ℝ≥0∞}
    (hI : upperLebesgueIntegral μ f ≠ ∞)
    (hg : Measurable g) (hfg : f ≤ g)
    (hgI : (∫⁻ x, g x ∂μ) = upperLebesgueIntegral μ f)
    (hh : Measurable h) (hfh : f ≤ h)
    (hhI : (∫⁻ x, h x ∂μ) = upperLebesgueIntegral μ f) :
    g =ᵐ[μ] h := by
  let k : α → ℝ≥0∞ := fun x ↦ g x ⊓ h x
  have hk : Measurable k := hg.inf hh
  have hfk : f ≤ k := fun x ↦ le_inf (hfg x) (hfh x)
  have hkI : (∫⁻ x, k x ∂μ) = upperLebesgueIntegral μ f := by
    apply le_antisymm
    · calc
        (∫⁻ x, k x ∂μ) ≤ ∫⁻ x, g x ∂μ :=
          lintegral_mono fun x ↦ inf_le_left
        _ = upperLebesgueIntegral μ f := hgI
    · exact upperLebesgueIntegral_le_lintegral μ hk hfk
  have hkg : k =ᵐ[μ] g :=
    (lintegral_eq_iff_ae_eq_of_ae_le
      (hkI.trans_ne hI) hg.aemeasurable
      (ae_of_all μ fun x ↦ inf_le_left)).mp (hkI.trans hgI.symm)
  have hkh : k =ᵐ[μ] h :=
    (lintegral_eq_iff_ae_eq_of_ae_le
      (hkI.trans_ne hI) hh.aemeasurable
      (ae_of_all μ fun x ↦ inf_le_right)).mp (hkI.trans hhI.symm)
  exact hkg.symm.trans hkh

/-- Simon Remark 1.10, monotone convergence for upper integrals.  No
measurability assumption is imposed on the increasing sequence. -/
theorem upperLebesgueIntegral_iSup_of_monotone
    (μ : Measure α) (f : ℕ → α → ℝ≥0∞) (hf : Monotone f) :
    upperLebesgueIntegral μ (fun x ↦ ⨆ n, f n x) =
      ⨆ n, upperLebesgueIntegral μ (f n) := by
  choose g hgmeas hfg hgI using fun n ↦
    exists_measurableMajorant_lintegral_eq_upperLebesgueIntegral μ (f n)
  let h : ℕ → α → ℝ≥0∞ := fun n x ↦ ⨅ j : {j : ℕ // n ≤ j}, g j x
  have hmeas (n : ℕ) : Measurable (h n) := by
    exact Measurable.iInf fun j ↦ hgmeas j
  have hfh (n : ℕ) : f n ≤ h n := by
    intro x
    apply le_iInf
    intro j
    exact (hf j.property x).trans (hfg j x)
  have hhmono : Monotone h := by
    intro n m hnm x
    apply le_iInf
    intro j
    exact iInf_le_of_le (⟨j, hnm.trans j.property⟩ : {j : ℕ // n ≤ j}) le_rfl
  have hhI (n : ℕ) :
      (∫⁻ x, h n x ∂μ) = upperLebesgueIntegral μ (f n) := by
    apply le_antisymm
    · calc
        (∫⁻ x, h n x ∂μ) ≤ ∫⁻ x, g n x ∂μ :=
          lintegral_mono fun x ↦
            iInf_le_of_le (⟨n, le_rfl⟩ : {j : ℕ // n ≤ j}) le_rfl
        _ = upperLebesgueIntegral μ (f n) := hgI n
    · exact upperLebesgueIntegral_le_lintegral μ (hmeas n) (hfh n)
  let H : α → ℝ≥0∞ := fun x ↦ ⨆ n, h n x
  have hHmeas : Measurable H := Measurable.iSup hmeas
  have hfH : (fun x ↦ ⨆ n, f n x) ≤ H := by
    intro x
    apply iSup_le
    intro n
    exact (hfh n x).trans (le_iSup (fun m ↦ h m x) n)
  apply le_antisymm
  · calc
      upperLebesgueIntegral μ (fun x ↦ ⨆ n, f n x) ≤ ∫⁻ x, H x ∂μ :=
        upperLebesgueIntegral_le_lintegral μ hHmeas hfH
      _ = ⨆ n, ∫⁻ x, h n x ∂μ := lintegral_iSup hmeas hhmono
      _ = ⨆ n, upperLebesgueIntegral μ (f n) := by simp only [hhI]
  · apply iSup_le
    intro n
    apply upperLebesgueIntegral_mono μ
    intro x
    exact le_iSup (fun m ↦ f m x) n

end Poincare.SimonGMT.Chapter02
