module

public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Regular
public import Poincare.SimonGMT.Chapter01.Hausdorff

public section

/-!
# Simon GMT, Chapter 2, §1: Lipschitz functions

This module exposes the metric definition, Simon's explicit lower-envelope
formula and sharp real-valued extension theorem, Rademacher's theorem, and the
Hausdorff-measure image bound.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace Poincare.SimonGMT.Chapter02

universe u v

variable {X : Type u} {Y : Type v}

/-- Simon (1.1), with a specified nonnegative Lipschitz constant. -/
abbrev HasLipschitzConstant [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (K : ℝ≥0) (f : X → Y) : Prop :=
  LipschitzWith K f

/-- The distance-inequality form of Simon (1.1). -/
theorem hasLipschitzConstant_iff [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (K : ℝ≥0) (f : X → Y) :
    HasLipschitzConstant K f ↔
      ∀ x y, dist (f x) (f y) ≤ K * dist x y :=
  lipschitzWith_iff_dist_le_mul

/-- A function is Lipschitz in Simon's sense when it has some finite
nonnegative Lipschitz constant. -/
def IsLipschitz [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → Y) : Prop :=
  ∃ K : ℝ≥0, HasLipschitzConstant K f

/-- Simon's `Lip f`: the least nonnegative Lipschitz constant.  The value is
used below only when `f` is Lipschitz, so the defining set is nonempty. -/
noncomputable def optimalLipschitzConstant
    [PseudoMetricSpace X] [PseudoMetricSpace Y] (f : X → Y) : ℝ≥0 :=
  sInf {K : ℝ≥0 | LipschitzWith K f}

/-- The infimum defining `optimalLipschitzConstant` is itself a valid
Lipschitz constant. -/
theorem lipschitzWith_optimalLipschitzConstant
    [PseudoMetricSpace X] [PseudoMetricSpace Y] {f : X → Y}
    (hf : IsLipschitz f) :
    LipschitzWith (optimalLipschitzConstant f) f := by
  obtain ⟨K, hK⟩ := hf
  apply LipschitzWith.of_dist_le_mul
  intro x y
  by_cases hxy : dist x y = 0
  · have hzero : dist (f x) (f y) = 0 := by
      apply le_antisymm
      · simpa only [hxy, mul_zero] using hK.dist_le_mul x y
      · exact dist_nonneg
    simp only [hzero, hxy, mul_zero]
    exact le_rfl
  · have hpos : 0 < dist x y := lt_of_le_of_ne dist_nonneg (Ne.symm hxy)
    apply (div_le_iff₀ hpos).mp
    let q : ℝ≥0 := ⟨dist (f x) (f y) / dist x y,
      div_nonneg dist_nonneg dist_nonneg⟩
    have hq : q ≤ optimalLipschitzConstant f := by
      apply le_csInf
      · exact ⟨K, hK⟩
      · intro L hL
        apply NNReal.coe_le_coe.mp
        exact (div_le_iff₀ hpos).mpr (hL.dist_le_mul x y)
    exact NNReal.coe_le_coe.mpr hq

/-- Every specified Lipschitz bound is at least Simon's optimal constant. -/
theorem optimalLipschitzConstant_le_of_lipschitzWith
    [PseudoMetricSpace X] [PseudoMetricSpace Y] {f : X → Y} {K : ℝ≥0}
    (hf : LipschitzWith K f) : optimalLipschitzConstant f ≤ K := by
  apply csInf_le
  · exact ⟨0, fun _ _ ↦ bot_le⟩
  · exact hf

/-- The value at `x` of Simon's cone with vertex `(a, f a)` and slope `K`.
This is the family of functions whose lower envelope appears in Theorem 1.2
and Remark 1.3. -/
def mcShaneConeValue [PseudoMetricSpace X] {A : Set X}
    (f : A → ℝ) (K : ℝ≥0) (a : A) (x : X) : ℝ :=
  f a + K * dist x a

/-- Simon's explicit McShane extension: the lower envelope of all cones with
vertices on the graph of `f` and common slope `K`. -/
noncomputable def mcShaneExtension [PseudoMetricSpace X] {A : Set X}
    (f : A → ℝ) (K : ℝ≥0) (x : X) : ℝ :=
  ⨅ a : A, mcShaneConeValue f K a x

/-- The explicit formula in the proof of Simon Theorem 1.2. -/
theorem mcShaneExtension_eq_iInf [PseudoMetricSpace X] {A : Set X}
    (f : A → ℝ) (K : ℝ≥0) (x : X) :
    mcShaneExtension f K x =
      ⨅ a : A, f a + K * dist x a :=
  by simp only [mcShaneExtension, mcShaneConeValue]

/-- Simon Theorem 1.2 and Remark 1.3 in their constructive form: the lower
envelope of the slope-`K` cones is `K`-Lipschitz and agrees with `f` on `A`.
Thus the existential extension below is witnessed by the formula printed in
the book. -/
theorem mcShaneExtension_spec [PseudoMetricSpace X]
    {A : Set X} (hA : A.Nonempty) (f : A → ℝ) {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    LipschitzWith K (mcShaneExtension f K) ∧
      ∀ a : A, mcShaneExtension f K a = f a := by
  letI : Nonempty A := hA.to_subtype
  let a₀ : A := ⟨hA.choose, hA.choose_spec⟩
  have hbdd : ∀ x : X,
      BddBelow (range fun a : A ↦ mcShaneConeValue f K a x) := by
    intro x
    refine ⟨f a₀ - K * dist x a₀, ?_⟩
    rintro _ ⟨a, rfl⟩
    dsimp only [mcShaneConeValue]
    rw [sub_le_iff_le_add, add_assoc, ← mul_add, add_comm (dist x a)]
    calc
      f a₀ ≤ f a + K * dist a₀ a := hf.le_add_mul a₀ a
      _ ≤ f a + K * (dist x a₀ + dist x a) := by
        gcongr
        calc
          dist (a₀ : X) (a : X) ≤ dist (a₀ : X) x + dist x (a : X) :=
            dist_triangle _ _ _
          _ = dist x (a₀ : X) + dist x (a : X) := by
            rw [dist_comm (a₀ : X) x]
  have heq : ∀ a : A, mcShaneExtension f K a = f a := by
    intro a
    apply le_antisymm
    · simpa only [mcShaneExtension, mcShaneConeValue, add_zero,
        Subtype.dist_eq, dist_self, mul_zero] using
        ciInf_le (hbdd a) a
    · apply le_ciInf
      intro b
      change f a ≤ f b + K * dist (a : X) b
      exact hf.le_add_mul a b
  refine ⟨LipschitzWith.of_le_add_mul K fun x y ↦ ?_, heq⟩
  rw [← sub_le_iff_le_add]
  apply le_ciInf
  intro a
  rw [sub_le_iff_le_add]
  calc
    mcShaneExtension f K x ≤ f a + K * dist x a :=
      ciInf_le (hbdd x) a
    _ ≤ (f a + K * dist y a) + K * dist x y := by
      rw [add_assoc, ← mul_add, add_comm (dist y a)]
      gcongr
      exact dist_triangle _ _ _
    _ = mcShaneConeValue f K a y + K * dist x y := rfl

/-- Simon Theorem 1.2 (McShane extension), stated for a function whose domain
is the subtype `A`.  The extension has exactly the same specified constant.
The source assumes `A` nonempty, as this formulation does. -/
theorem lipschitz_extension_real_of_nonempty [PseudoMetricSpace X]
    {A : Set X} (hA : A.Nonempty) (f : A → ℝ) {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    ∃ F : X → ℝ, LipschitzWith K F ∧ ∀ x : A, F x = f x := by
  exact ⟨mcShaneExtension f K, (mcShaneExtension_spec hA f hf).1,
    (mcShaneExtension_spec hA f hf).2⟩

/-- Simon Theorem 1.2 with its full sharp conclusion: the extension has the
same *least* Lipschitz constant as the original function. -/
theorem lipschitz_extension_real_optimal
    [PseudoMetricSpace X] {A : Set X} (hA : A.Nonempty) (f : A → ℝ)
    (hf : IsLipschitz f) :
    ∃ F : X → ℝ,
      IsLipschitz F ∧
        (∀ x : A, F x = f x) ∧
          optimalLipschitzConstant F = optimalLipschitzConstant f := by
  have hopt := lipschitzWith_optimalLipschitzConstant hf
  obtain ⟨F, hF, hEq⟩ :=
    lipschitz_extension_real_of_nonempty hA f hopt
  have hFLip : IsLipschitz F := ⟨optimalLipschitzConstant f, hF⟩
  refine ⟨F, hFLip, hEq, le_antisymm
    (optimalLipschitzConstant_le_of_lipschitzWith hF) ?_⟩
  have hFopt := lipschitzWith_optimalLipschitzConstant hFLip
  apply optimalLipschitzConstant_le_of_lipschitzWith
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simpa only [hEq x, hEq y, Subtype.dist_eq] using
    hFopt.dist_le_mul x.1 y.1

/-- Simon Theorem 1.4 (Rademacher): a Lipschitz map between finite-dimensional
real normed spaces is Fréchet differentiable almost everywhere. -/
theorem rademacher_ae_differentiableAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {μ : Measure E}
    [MeasureTheory.Measure.IsAddHaarMeasure μ]
    {K : ℝ≥0} {f : E → F}
    (hf : LipschitzWith K f) :
    ∀ᵐ x ∂μ, DifferentiableAt ℝ f x :=
  hf.ae_differentiableAt

/-- The measure inequality in Simon Theorem 1.8(i), in Mathlib's general
real-dimensional Hausdorff-measure normalization.  It does not require the
source's measurability, finiteness, or sigma-compactness assumptions. -/
theorem hausdorffMeasure_image_le_of_lipschitzOn
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {A : Set X} {f : X → Y} {K : ℝ≥0} {d : ℝ}
    (hf : LipschitzOnWith K f A) (hd : 0 ≤ d) :
    μH[d] (f '' A) ≤ (K : ℝ≥0∞) ^ d * μH[d] A :=
  hf.hausdorffMeasure_image_le hd

/-- The normalized version of Simon Theorem 1.8(i)'s Hausdorff-measure
image bound. -/
theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {A : Set X} {f : X → Y} {K : ℝ≥0} (n : ℕ)
    (hf : LipschitzOnWith K f A) :
    μHE[n] (f '' A) ≤ (K : ℝ≥0∞) ^ n * μHE[n] A := by
  simp_rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply,
    ENNReal.smul_def, smul_eq_mul]
  calc
    _ ≤ (Measure.addHaarScalarFactor
          (volume : Measure (EuclideanSpace ℝ (Fin n))) μH[n] : ℝ≥0∞) *
        ((K : ℝ≥0∞) ^ n * μH[n] A) :=
      by
        gcongr
        simpa only [ENNReal.rpow_natCast] using
          hf.hausdorffMeasure_image_le
            (d := (n : ℝ)) (Nat.cast_nonneg n)
    _ = (K : ℝ≥0∞) ^ n *
        ((Measure.addHaarScalarFactor
          (volume : Measure (EuclideanSpace ℝ (Fin n))) μH[n] : ℝ≥0∞) *
          μH[n] A) := by ac_rfl

/-- Simon Theorem 1.8(i), image measurability in the finite-dimensional
Euclidean-domain case.  Mathlib's `NullMeasurableSet` is the faithful notion
here: Simon means measurability for the completed Hausdorff measure, not
necessarily Borel measurability. -/
theorem nullMeasurableSet_image_of_lipschitzOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {A : Set E} {f : E → Y} {K : ℝ≥0}
    (hA : MeasurableSet A)
    (hAfin : μHE[Module.finrank ℝ E] A ≠ ∞)
    (hf : LipschitzOnWith K f A) :
    NullMeasurableSet (f '' A) μHE[Module.finrank ℝ E] := by
  letI : Measure.Regular (μHE[Module.finrank ℝ E] : Measure E) := by
    rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
    infer_instance
  choose C hCA hCcompact hAC using fun j : ℕ ↦
    hA.exists_isCompact_sdiff_lt
      (μ := (μHE[Module.finrank ℝ E] : Measure E))
      hAfin (show ((j : ℝ≥0∞)⁻¹) ≠ 0 by simp)
  let B : Set Y := ⋃ j, f '' C j
  have hBsub : B ⊆ f '' A := by
    intro y hy
    obtain ⟨j, x, hxC, rfl⟩ := mem_iUnion.mp hy
    exact ⟨x, hCA j hxC, rfl⟩
  have hBmeas : MeasurableSet B := by
    apply MeasurableSet.iUnion
    intro j
    exact (hCcompact j).image_of_continuousOn
      ((hf.mono (hCA j)).continuousOn) |>.measurableSet
  let D : Set E := A \ ⋃ j, C j
  have hDzero : μHE[Module.finrank ℝ E] D = 0 := by
    apply le_antisymm
    · apply ge_of_tendsto ENNReal.tendsto_inv_nat_nhds_zero
      filter_upwards [] with j
      exact (measure_mono (show D ⊆ A \ C j by
        intro x hx
        exact ⟨hx.1, fun hxC ↦ hx.2 (mem_iUnion.mpr ⟨j, hxC⟩)⟩)).trans (hAC j).le
    · exact bot_le
  have hresSub : f '' A \ B ⊆ f '' D := by
    rintro y ⟨⟨x, hxA, rfl⟩, hxfB⟩
    refine ⟨x, ⟨hxA, ?_⟩, rfl⟩
    intro hxUnion
    obtain ⟨j, hxC⟩ := mem_iUnion.mp hxUnion
    exact hxfB (mem_iUnion.mpr ⟨j, ⟨x, hxC, rfl⟩⟩)
  have himageDzero : μHE[Module.finrank ℝ E] (f '' D) = 0 := by
    apply le_antisymm
    · calc
        μHE[Module.finrank ℝ E] (f '' D) ≤
            (K : ℝ≥0∞) ^ Module.finrank ℝ E *
              μHE[Module.finrank ℝ E] D :=
          euclideanHausdorffMeasure_image_le_of_lipschitzOn
            (Module.finrank ℝ E) (hf.mono inter_subset_left)
        _ = 0 := by rw [hDzero, mul_zero]
    · exact bot_le
  have hresZero : μHE[Module.finrank ℝ E] (f '' A \ B) = 0 :=
    measure_mono_null hresSub himageDzero
  rw [← union_sdiff_cancel hBsub]
  exact hBmeas.nullMeasurableSet.union (NullMeasurableSet.of_null hresZero)

end Poincare.SimonGMT.Chapter02
