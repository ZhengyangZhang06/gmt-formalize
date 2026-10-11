module

public import Poincare.SimonGMT.Chapter02.AreaLinearWeighted

@[expose] public section

/-!
# Simon GMT, Chapter 2, §3: fibers and multiplicity

This file formalizes the fiber-counting notation used in Simon (3.4) and the
weighted fiber sum occurring on the right side of (3.5).  Values lie in
`ℝ≥0∞`, so infinite fibers have the value `∞`, as required for the
nonnegative area formula.
-/

open Function MeasureTheory Module Set
open scoped ENNReal

namespace Poincare.SimonGMT.Chapter02

/-- The source fiber over `y`, restricted to `A`. -/
def areaFiber {E F : Type*} (A : Set E) (f : E → F) (y : F) :=
  {x : E // x ∈ A ∧ f x = y}

/-- Simon (3.4): the multiplicity `N(f,y)` is the cardinality of the fiber of
`f|A` over `y`, represented as an extended nonnegative real. -/
noncomputable def areaMultiplicity {E F : Type*}
    (A : Set E) (f : E → F) (y : F) : ℝ≥0∞ :=
  ∑' _ : areaFiber A f y, 1

/-- The fiber sum in the weighted form of Simon (3.5). -/
noncomputable def weightedAreaFiberSum {E F : Type*}
    (A : Set E) (f : E → F) (w : E → ℝ≥0∞) (y : F) : ℝ≥0∞ :=
  ∑' x : areaFiber A f y, w x.1

/-- Counting a fiber is the weighted fiber sum with unit weight. -/
theorem weightedAreaFiberSum_one {E F : Type*}
    (A : Set E) (f : E → F) (y : F) :
    weightedAreaFiberSum A f (fun _ ↦ 1) y = areaMultiplicity A f y :=
  rfl

/-- A point outside the image has multiplicity zero. -/
theorem areaMultiplicity_eq_zero_of_not_mem_image {E F : Type*}
    {A : Set E} {f : E → F} {y : F} (hy : y ∉ f '' A) :
    areaMultiplicity A f y = 0 := by
  letI : IsEmpty (areaFiber A f y) :=
    ⟨fun x ↦ hy ⟨x.1, x.2.1, x.2.2⟩⟩
  simp [areaMultiplicity]

/-- For an injective map, an occupied fiber has multiplicity one. -/
theorem areaMultiplicity_eq_one_of_injective {E F : Type*}
    {A : Set E} {f : E → F} (hf : Injective f) {x : E} (hx : x ∈ A) :
    areaMultiplicity A f (f x) = 1 := by
  let x₀ : areaFiber A f (f x) := ⟨x, hx, rfl⟩
  letI : Unique (areaFiber A f (f x)) := {
    default := x₀
    uniq z := Subtype.ext (hf z.2.2) }
  simp [areaMultiplicity]

/-- On an occupied fiber of an injective map, the weighted fiber sum is the
weight of its unique preimage. -/
theorem weightedAreaFiberSum_eq_of_injective {E F : Type*}
    {A : Set E} {f : E → F} (hf : Injective f) (w : E → ℝ≥0∞)
    {x : E} (hx : x ∈ A) :
    weightedAreaFiberSum A f w (f x) = w x := by
  let x₀ : areaFiber A f (f x) := ⟨x, hx, rfl⟩
  letI : Unique (areaFiber A f (f x)) := {
    default := x₀
    uniq z := Subtype.ext (hf z.2.2) }
  unfold weightedAreaFiberSum
  calc
    (∑' z : areaFiber A f (f x), w z.1) = w (default : areaFiber A f (f x)).1 := by
      simp
    _ = w x₀.1 := congrArg (fun z : areaFiber A f (f x) ↦ w z.1) (Unique.uniq _ _)
    _ = w x := rfl

/-- Simon (3.5) for an injective linear map in arbitrary codimension, now in
the source's fiber-sum form with a weight on the domain. -/
theorem weighted_linear_area_formula_fiberSum
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    (L : E →ₗ[ℝ] F) (hL : Injective L) {A : Set E} (hA : MeasurableSet A)
    (w : E → ℝ≥0∞) :
    ∫⁻ y in L '' A, weightedAreaFiberSum A L w y ∂μHE[finrank ℝ E] =
      ENNReal.ofReal L.normDet * ∫⁻ x in A, w x ∂μHE[finrank ℝ E] := by
  rw [weighted_linear_area_formula L hL hA]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem hA] with x hx
  exact weightedAreaFiberSum_eq_of_injective hL w hx

end Poincare.SimonGMT.Chapter02
