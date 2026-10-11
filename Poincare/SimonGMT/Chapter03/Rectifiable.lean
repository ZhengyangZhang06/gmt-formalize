module

public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Poincare.SimonGMT.Chapter02.Lipschitz

public section

/-!
# Simon GMT, Chapter 3: rectifiable sets

This module gives faithful definitions for countable rectifiability (1.1),
unweighted and weighted approximate tangent spaces (1.4 and 1.7), proves the
uniqueness assertion in Remark 1.5(1), defines pure unrectifiability (3.1), and
proves the full rectifiable/purely unrectifiable decomposition in Lemma 3.2.
The deep characterization, structure, area/coarea, and finite-perimeter
theorems are not asserted here.
-/

open Filter Function MeasureTheory Module Set
open scoped CompactlySupported ENNReal NNReal Topology

namespace Poincare.SimonGMT.Chapter03

universe u

variable {E : Type u}

/-- Simon Definition 1.1.  The source takes `E = ℝ^(n+ℓ)`; using an arbitrary
finite-dimensional real inner-product space avoids committing to coordinates.
-/
def CountablyRectifiable
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (n : ℕ) (M : Set E) : Prop :=
  ∃ M₀ : Set E, μHE[n] M₀ = 0 ∧
    ∃ F : ℕ → EuclideanSpace ℝ (Fin n) → E,
      (∀ j, ∃ K : ℝ≥0, LipschitzWith K (F j)) ∧
        M ⊆ M₀ ∪ ⋃ j, range (F j)

/-- A Hausdorff-null set is countably rectifiable: it is entirely absorbed by
the exceptional set `M₀` in Simon Definition 1.1. -/
theorem countablyRectifiable_of_measure_zero
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} {M : Set E} (hM : μHE[n] M = 0) :
    CountablyRectifiable n M := by
  refine ⟨M, hM, fun _ _ ↦ 0, ?_, subset_union_left⟩
  intro j
  exact ⟨0, LipschitzWith.const 0⟩

/-- Countable rectifiability is inherited by subsets. -/
theorem CountablyRectifiable.mono
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} {M N : Set E} (hM : CountablyRectifiable n M) (hNM : N ⊆ M) :
    CountablyRectifiable n N := by
  obtain ⟨M₀, hM₀, F, hF, hcover⟩ := hM
  exact ⟨M₀, hM₀, F, hF, hNM.trans hcover⟩

/-- The range of one Lipschitz parametrization is countably rectifiable. -/
theorem countablyRectifiable_range
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → E} {K : ℝ≥0}
    (hf : LipschitzWith K f) : CountablyRectifiable n (range f) := by
  refine ⟨∅, measure_empty, fun _ ↦ f, ?_, ?_⟩
  · exact fun _ ↦ ⟨K, hf⟩
  · intro x hx
    exact Or.inr (mem_iUnion.2 ⟨0, hx⟩)

/-- A countable union of countably rectifiable sets is countably
rectifiable.  The two countable indices are encoded with `Nat.pair`. -/
theorem countablyRectifiable_iUnion
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} (M : ℕ → Set E) (hM : ∀ i, CountablyRectifiable n (M i)) :
    CountablyRectifiable n (⋃ i, M i) := by
  classical
  choose M₀ hM₀ F hF hcover using hM
  refine ⟨⋃ i, M₀ i, measure_iUnion_null hM₀,
    fun k ↦ F (Nat.unpair k).1 (Nat.unpair k).2, ?_, ?_⟩
  · intro k
    exact hF (Nat.unpair k).1 (Nat.unpair k).2
  · intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    rcases hcover i hxi with hnull | himage
    · exact Or.inl (mem_iUnion.2 ⟨i, hnull⟩)
    · obtain ⟨j, hj⟩ := mem_iUnion.mp himage
      refine Or.inr (mem_iUnion.2 ⟨Nat.pair i j, ?_⟩)
      simpa only [Nat.unpair_pair] using hj

/-- Simon's dilation `η_{x,r}(y) = r⁻¹(y-x)`. -/
noncomputable def blowUpMap [AddCommGroup E] [Module ℝ E]
    (x : E) (r : ℝ) (y : E) : E :=
  r⁻¹ • (y - x)

/-- Simon Definition 1.4, written literally as convergence against every
compactly supported continuous real-valued test function. -/
def HasApproximateTangentSpaceAt
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (n : ℕ) (M : Set E) (x : E) (P : Submodule ℝ E) : Prop :=
  finrank ℝ P = n ∧
    ∀ f : C_c(E, ℝ),
      Tendsto
        (fun r : ℝ ↦ ∫ y in blowUpMap x r '' M, f y ∂μHE[n])
        (𝓝[>] 0)
        (𝓝 (∫ y in (P : Set E), f y ∂μHE[n]))

/-- The dimension condition carried by Simon's approximate-tangent
predicate.  This accessor keeps downstream developments independent of the
definition's internal conjunction. -/
theorem HasApproximateTangentSpaceAt.finrank_eq
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} {M : Set E} {x : E} {P : Submodule ℝ E}
    (h : HasApproximateTangentSpaceAt n M x P) : finrank ℝ P = n :=
  h.1

/-- An `n`-dimensional linear subspace has itself as approximate tangent at
each of its points.  This is the basic flat model for Definition 1.4. -/
theorem hasApproximateTangentSpaceAt_submodule
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} {P : Submodule ℝ E} (hP : finrank ℝ P = n) {x : E}
    (hx : x ∈ P) : HasApproximateTangentSpaceAt n (P : Set E) x P := by
  refine ⟨hP, fun f ↦ ?_⟩
  apply (Filter.tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : r ≠ 0 := ne_of_gt hr
  have himage : blowUpMap x r '' (P : Set E) = (P : Set E) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact P.smul_mem _ (P.sub_mem hz hx)
    · intro hy
      refine ⟨x + r • y, P.add_mem hx (P.smul_mem _ hy), ?_⟩
      simp [blowUpMap, hr0]
  rw [himage]

/-- The flat-model tangent assertion holds almost everywhere for Hausdorff
measure restricted to the plane (in fact, at every point of the plane). -/
theorem ae_hasApproximateTangentSpaceAt_submodule
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} {P : Submodule ℝ E} (hP : finrank ℝ P = n) :
    ∀ᵐ x ∂(μHE[n] : Measure E).restrict (P : Set E),
      HasApproximateTangentSpaceAt n (P : Set E) x P := by
  filter_upwards [ae_restrict_mem P.closed_of_finiteDimensional.measurableSet] with x hx
  exact hasApproximateTangentSpaceAt_submodule hP hx

/-- The support of the `n`-dimensional Euclidean Hausdorff measure restricted
to an `n`-plane is exactly that plane. -/
theorem support_euclideanHausdorffMeasure_restrict_submodule
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} {P : Submodule ℝ E} (hP : finrank ℝ P = n) :
    ((μHE[n] : Measure E).restrict (P : Set E)).support = (P : Set E) := by
  apply Set.Subset.antisymm
  · refine (Measure.support_restrict_subset.trans ?_)
    simp only [P.closed_of_finiteDimensional.closure_eq, inter_subset_left]
  · intro x hx
    rw [Measure.mem_support_iff_forall]
    intro U hU
    obtain ⟨V, hVU, hVopen, hxV⟩ := mem_nhds_iff.mp hU
    refine (show 0 < ((μHE[n] : Measure E).restrict (P : Set E)) V from ?_).trans_le
      (measure_mono hVU)
    rw [Measure.restrict_apply hVopen.measurableSet]
    have hpre : 0 < (μHE[n] : Measure P) ((P.subtypeₗᵢ : P → E) ⁻¹' V) := by
      rw [← hP]
      have hxV' : (P.subtypeₗᵢ (⟨x, hx⟩ : P)) ∈ V := hxV
      exact Measure.measure_pos_of_mem_nhds _
        (P.subtypeₗᵢ.continuous.continuousAt (hVopen.mem_nhds hxV'))
    rw [← P.subtypeₗᵢ.isometry.euclideanHausdorffMeasure_image (d := n)
      ((P.subtypeₗᵢ : P → E) ⁻¹' V)] at hpre
    have himage : P.subtypeₗᵢ '' ((P.subtypeₗᵢ : P → E) ⁻¹' V) =
        V ∩ (P : Set E) := by
      ext y
      simp [and_comm]
    rwa [himage] at hpre

/-- Restricting `n`-dimensional Euclidean Hausdorff measure to an `n`-plane
is a regular measure. -/
theorem regular_euclideanHausdorffMeasure_restrict_submodule
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} {P : Submodule ℝ E} (hP : finrank ℝ P = n) :
    ((μHE[n] : Measure E).restrict (P : Set E)).Regular := by
  have hrange : Set.range (P.subtypeₗᵢ : P → E) = (P : Set E) := by
    ext x
    simp
  have hmap :
      (μHE[n] : Measure P).map (P.subtypeₗᵢ : P → E) =
        (μHE[n] : Measure E).restrict (P : Set E) := by
    rw [← hrange]
    exact P.subtypeₗᵢ.isometry.map_euclideanHausdorffMeasure (d := n)
  letI : IsFiniteMeasureOnCompacts
      ((μHE[n] : Measure E).restrict (P : Set E)) := by
    constructor
    intro K hK
    rw [← hmap, Measure.map_apply P.subtypeₗᵢ.continuous.measurable hK.measurableSet]
    haveI : IsFiniteMeasureOnCompacts (μHE[n] : Measure P) := by
      rw [← hP]
      infer_instance
    exact (P.closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.isCompact_preimage
      hK).measure_lt_top
  letI : IsLocallyFiniteMeasure
      ((μHE[n] : Measure E).restrict (P : Set E)) := inferInstance
  exact Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

/-- If two planes satisfy Simon Definition 1.4 at the same point, their
restricted Hausdorff measures agree. -/
theorem HasApproximateTangentSpaceAt.planeMeasure_eq
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} {M : Set E} {x : E} {P Q : Submodule ℝ E}
    (hP : HasApproximateTangentSpaceAt n M x P)
    (hQ : HasApproximateTangentSpaceAt n M x Q) :
    (μHE[n] : Measure E).restrict (P : Set E) =
      (μHE[n] : Measure E).restrict (Q : Set E) := by
  letI := regular_euclideanHausdorffMeasure_restrict_submodule hP.1
  letI := regular_euclideanHausdorffMeasure_restrict_submodule hQ.1
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  exact tendsto_nhds_unique (hP.2 f) (hQ.2 f)

/-- Simon Remark 1.5(1): the approximate tangent plane in Definition 1.4 is
unique whenever it exists. -/
theorem HasApproximateTangentSpaceAt.unique
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} {M : Set E} {x : E} {P Q : Submodule ℝ E}
    (hP : HasApproximateTangentSpaceAt n M x P)
    (hQ : HasApproximateTangentSpaceAt n M x Q) : P = Q := by
  apply SetLike.ext'
  rw [← support_euclideanHausdorffMeasure_restrict_submodule hP.1,
    ← support_euclideanHausdorffMeasure_restrict_submodule hQ.1,
    hP.planeMeasure_eq hQ]

/-- Any two almost-everywhere tangent-plane fields for the same set agree
almost everywhere.  This is the representative-independence consequence of
Simon Remark 1.5(1) used by the rectifiable-varifold construction. -/
theorem approximateTangentField_ae_eq
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} {M : Set E} {P Q : E → Submodule ℝ E}
    (hP : ∀ᵐ x ∂(μHE[n] : Measure E).restrict M,
      HasApproximateTangentSpaceAt n M x (P x))
    (hQ : ∀ᵐ x ∂(μHE[n] : Measure E).restrict M,
      HasApproximateTangentSpaceAt n M x (Q x)) :
    P =ᵐ[(μHE[n] : Measure E).restrict M] Q := by
  filter_upwards [hP, hQ] with x hxP hxQ
  exact hxP.unique hxQ

/-- Measurability of the orthogonal-projection representative transfers to
every other almost-everywhere approximate-tangent representative. -/
theorem aemeasurable_starProjection_of_approximateTangentField
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} {M : Set E} {P Q : E → Submodule ℝ E}
    (hP : ∀ᵐ x ∂(μHE[n] : Measure E).restrict M,
      HasApproximateTangentSpaceAt n M x (P x))
    (hQ : ∀ᵐ x ∂(μHE[n] : Measure E).restrict M,
      HasApproximateTangentSpaceAt n M x (Q x))
    (hPm : AEMeasurable (fun x ↦ (P x).starProjection)
      ((μHE[n] : Measure E).restrict M)) :
    AEMeasurable (fun x ↦ (Q x).starProjection)
      ((μHE[n] : Measure E).restrict M) := by
  apply hPm.congr
  filter_upwards [approximateTangentField_ae_eq hP hQ] with x hx
  rw [hx]

/-- The positivity, measurability, and local integrability hypotheses on the
multiplicity in Simon Definition 1.7. -/
def IsLocallyIntegrableMultiplicity
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (n : ℕ) (M : Set E) (θ : E → ℝ) : Prop :=
  MeasurableSet M ∧
    (∀ x ∈ M, 0 < θ x) ∧
      AEMeasurable θ ((μHE[n]).restrict M) ∧
        ∀ K : Set E, IsCompact K → IntegrableOn θ (M ∩ K) μHE[n]

namespace IsLocallyIntegrableMultiplicity

/-- The carrier in Simon Definition 1.7 is Hausdorff measurable. -/
theorem measurableSet
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} {M : Set E} {θ : E → ℝ}
    (h : IsLocallyIntegrableMultiplicity n M θ) : MeasurableSet M :=
  h.1

/-- The multiplicity in Simon Definition 1.7 is positive on its carrier. -/
theorem positive
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} {M : Set E} {θ : E → ℝ}
    (h : IsLocallyIntegrableMultiplicity n M θ) {x : E} (hx : x ∈ M) :
    0 < θ x :=
  h.2.1 x hx

/-- The multiplicity is measurable for Hausdorff measure restricted to the
carrier. -/
theorem aemeasurable
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} {M : Set E} {θ : E → ℝ}
    (h : IsLocallyIntegrableMultiplicity n M θ) :
    AEMeasurable θ ((μHE[n] : Measure E).restrict M) :=
  h.2.2.1

/-- The multiplicity is integrable on the intersection of the carrier with
every compact set. -/
theorem integrableOn_inter_compact
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} {M : Set E} {θ : E → ℝ}
    (h : IsLocallyIntegrableMultiplicity n M θ) {K : Set E} (hK : IsCompact K) :
    IntegrableOn θ (M ∩ K) μHE[n] :=
  h.2.2.2 K hK

end IsLocallyIntegrableMultiplicity

/-- Simon Definition 1.7: approximate tangent space with a positive locally
integrable multiplicity. -/
def HasWeightedApproximateTangentSpaceAt
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (n : ℕ) (M : Set E) (θ : E → ℝ) (x : E) (P : Submodule ℝ E) : Prop :=
  finrank ℝ P = n ∧
    ∀ f : C_c(E, ℝ),
      Tendsto
        (fun r : ℝ ↦
          ∫ y in blowUpMap x r '' M, f y * θ (x + r • y) ∂μHE[n])
        (𝓝[>] 0)
        (𝓝 (θ x * ∫ y in (P : Set E), f y ∂μHE[n]))

/-- Weighted approximate tangent planes are unique at points where the
multiplicity is nonzero.  Positivity in Definition 1.7 supplies this
hypothesis on `M`. -/
theorem HasWeightedApproximateTangentSpaceAt.unique
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} {M : Set E} {θ : E → ℝ} {x : E} {P Q : Submodule ℝ E}
    (hθ : θ x ≠ 0)
    (hP : HasWeightedApproximateTangentSpaceAt n M θ x P)
    (hQ : HasWeightedApproximateTangentSpaceAt n M θ x Q) : P = Q := by
  have hmeasure :
      (μHE[n] : Measure E).restrict (P : Set E) =
        (μHE[n] : Measure E).restrict (Q : Set E) := by
    letI := regular_euclideanHausdorffMeasure_restrict_submodule hP.1
    letI := regular_euclideanHausdorffMeasure_restrict_submodule hQ.1
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    exact mul_left_cancel₀ hθ (tendsto_nhds_unique (hP.2 f) (hQ.2 f))
  apply SetLike.ext'
  rw [← support_euclideanHausdorffMeasure_restrict_submodule hP.1,
    ← support_euclideanHausdorffMeasure_restrict_submodule hQ.1, hmeasure]

/-- Simon Definition 3.1: `P` contains no countably `n`-rectifiable subset of
positive `n`-dimensional Hausdorff measure. -/
def PurelyUnrectifiable
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (n : ℕ) (P : Set E) : Prop :=
  ∀ R : Set E, R ⊆ P → CountablyRectifiable n R → μHE[n] R = 0

/-- Pure unrectifiability is inherited by subsets. -/
theorem PurelyUnrectifiable.mono
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} {P Q : Set E} (hP : PurelyUnrectifiable n P) (hQP : Q ⊆ P) :
    PurelyUnrectifiable n Q := by
  intro R hRQ hR
  exact hP R (hRQ.trans hQP) hR

/-- Every Hausdorff-null set is purely unrectifiable. -/
theorem purelyUnrectifiable_of_measure_zero
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} {P : Set E} (hP : μHE[n] P = 0) :
    PurelyUnrectifiable n P := by
  intro R hRP _
  exact nonpos_iff_eq_zero.mp ((measure_mono hRP).trans_eq hP)

section Decomposition

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Every countably rectifiable set has a Borel countably rectifiable
superset.  Lipschitz images of Euclidean space are countable unions of
compact sets, and the exceptional null set has a Borel null hull. -/
theorem CountablyRectifiable.exists_measurable_superset {n : ℕ} {M : Set E}
    (hM : CountablyRectifiable n M) :
    ∃ B : Set E, M ⊆ B ∧ MeasurableSet B ∧ CountablyRectifiable n B := by
  obtain ⟨M₀, hM₀, F, hF, hcover⟩ := hM
  let N := toMeasurable (μHE[n] : Measure E) M₀
  have hN : μHE[n] N = 0 := by simpa only [N, measure_toMeasurable] using hM₀
  have hFmeas : ∀ j, MeasurableSet (range (F j)) := by
    intro j
    obtain ⟨K, hK⟩ := hF j
    obtain ⟨C, hC, hUnion⟩ := isSigmaCompact_range hK.continuous
    rw [← hUnion]
    exact MeasurableSet.iUnion fun i ↦ (hC i).measurableSet
  refine ⟨N ∪ ⋃ j, range (F j), ?_,
    (measurableSet_toMeasurable _ _).union (MeasurableSet.iUnion hFmeas),
    ⟨N, hN, F, hF, Subset.rfl⟩⟩
  exact hcover.trans (union_subset_union (subset_toMeasurable _ _) Subset.rfl)

/-- Countable unions in set-of-sets notation preserve rectifiability. -/
theorem countablyRectifiable_sUnion {n : ℕ} {D : Set (Set E)}
    (hD : D.Countable) (hrect : ∀ S ∈ D, CountablyRectifiable n S) :
    CountablyRectifiable n (⋃₀ D) := by
  classical
  rcases D.eq_empty_or_nonempty with rfl | hne
  · simpa using countablyRectifiable_of_measure_zero (n := n) (measure_empty : μHE[n] (∅ : Set E) = 0)
  obtain ⟨F, hF⟩ := hD.exists_eq_range hne
  rw [hF, sUnion_range]
  apply countablyRectifiable_iUnion
  intro i
  exact hrect (F i) (hF ▸ mem_range_self i)

/-- Pure unrectifiability is preserved by finite unions. -/
theorem PurelyUnrectifiable.union {n : ℕ} {P Q : Set E}
    (hP : PurelyUnrectifiable n P) (hQ : PurelyUnrectifiable n Q) :
    PurelyUnrectifiable n (P ∪ Q) := by
  intro R hR hrect
  have hp : μHE[n] (R ∩ P) = 0 := hP _ inter_subset_right (hrect.mono inter_subset_left)
  have hq : μHE[n] (R ∩ Q) = 0 := hQ _ inter_subset_right (hrect.mono inter_subset_left)
  apply measure_mono_null _ (measure_union_null hp hq)
  intro x hx
  rcases hR hx with hxP | hxQ
  · exact Or.inl ⟨hx, hxP⟩
  · exact Or.inr ⟨hx, hxQ⟩

/-- The measurable-union argument in Simon Lemma 3.2.  It produces a
Borel rectifiable set capturing, up to Hausdorff-null sets, every rectifiable
subset of `A`. -/
theorem exists_measurable_rectifiable_sdiff_purelyUnrectifiable {n : ℕ} {A : Set E}
    [SFinite ((μHE[n] : Measure E).restrict A)] :
    ∃ R : Set E, MeasurableSet R ∧ CountablyRectifiable n R ∧
      PurelyUnrectifiable n (A \ R) := by
  let C : Set (Set E) := {S | MeasurableSet S ∧ CountablyRectifiable n S}
  obtain ⟨D, hDC, hDcount, hDcover⟩ :=
    Measure.exists_ae_subset_biUnion_countable ((μHE[n] : Measure E).restrict A)
      (C := C) (fun S hS ↦ hS.1)
  have hDmeas : MeasurableSet (⋃₀ D) :=
    MeasurableSet.sUnion hDcount (fun S hS ↦ (hDC hS).1)
  refine ⟨⋃₀ D, hDmeas,
    countablyRectifiable_sUnion hDcount (fun S hS ↦ (hDC hS).2), ?_⟩
  intro S hSA hS
  obtain ⟨B, hSB, hBmeas, hBrect⟩ := hS.exists_measurable_superset
  have hnull : ((μHE[n] : Measure E).restrict A) (B \ ⋃₀ D) = 0 :=
    ae_le_set.mp (hDcover B ⟨hBmeas, hBrect⟩)
  rw [Measure.restrict_apply (hBmeas.diff hDmeas)] at hnull
  have hsub : S ⊆ (B \ ⋃₀ D) ∩ A :=
    fun x hx ↦ ⟨⟨hSB hx, (hSA hx).2⟩, (hSA hx).1⟩
  exact measure_mono_null hsub hnull

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- An outer-Hausdorff-σ-finite set induces a σ-finite restricted measure.
The measurable hulls in this proof allow the covering sets, and `A` itself,
to be nonmeasurable, as in Simon Lemma 3.2. -/
theorem sigmaFinite_restrict_of_hausdorff_finite_cover {n : ℕ} {A : Set E}
    (S : ℕ → Set E) (hcover : A ⊆ ⋃ j, S j) (hfinite : ∀ j, μHE[n] (S j) < ∞) :
    SigmaFinite ((μHE[n] : Measure E).restrict A) := by
  let B : ℕ → Set E := fun j ↦ toMeasurable (μHE[n] : Measure E) (S j)
  have hBmeas : ∀ j, MeasurableSet (B j) := fun j ↦ measurableSet_toMeasurable _ _
  have hBfinite : ∀ j, μHE[n] (B j) < ∞ := by
    intro j
    simpa only [B, measure_toMeasurable] using hfinite j
  have hBUnion : MeasurableSet (⋃ j, B j) := MeasurableSet.iUnion hBmeas
  have hAB : A ⊆ ⋃ j, B j :=
    hcover.trans (iUnion_mono fun j ↦ subset_toMeasurable _ _)
  let : SigmaFinite ((μHE[n] : Measure E).restrict (⋃ j, B j)) := by
    refine ⟨⟨⟨fun j ↦ B j ∪ (⋃ k, B k)ᶜ, fun _ ↦ trivial, ?_, ?_⟩⟩⟩
    · intro j
      rw [Measure.restrict_apply ((hBmeas j).union hBUnion.compl)]
      apply (measure_mono ?_).trans_lt (hBfinite j)
      intro x hx
      exact hx.1.resolve_right (fun hnot ↦ hnot hx.2)
    · ext x
      simp only [mem_iUnion, mem_union, mem_compl_iff, mem_univ, iff_true]
      by_cases hx : ∃ j, x ∈ B j
      · obtain ⟨j, hj⟩ := hx
        exact ⟨j, Or.inl hj⟩
      · exact ⟨0, Or.inr hx⟩
  exact Measure.sigmaFinite_of_le _ (Measure.restrict_mono_set _ hAB)

/-- Simon Lemma 3.2, first assertion: every outer-Hausdorff-σ-finite set
is the disjoint union of a countably rectifiable set and a purely
unrectifiable set.  No measurability of `A` or its finite cover is assumed. -/
theorem rectifiable_purelyUnrectifiable_decomposition {n : ℕ} {A : Set E}
    (S : ℕ → Set E) (hcover : A ⊆ ⋃ j, S j) (hfinite : ∀ j, μHE[n] (S j) < ∞) :
    ∃ R P : Set E, A = R ∪ P ∧ Disjoint R P ∧
      CountablyRectifiable n R ∧ PurelyUnrectifiable n P := by
  let := sigmaFinite_restrict_of_hausdorff_finite_cover S hcover hfinite
  obtain ⟨M, _, hM, hpure⟩ :=
    exists_measurable_rectifiable_sdiff_purelyUnrectifiable (n := n) (A := A)
  refine ⟨A ∩ M, A \ M, ?_, ?_, hM.mono inter_subset_right, hpure⟩
  · ext x
    simp only [mem_union, mem_inter_iff, Set.mem_sdiff]
    tauto
  · exact disjoint_left.mpr fun x hx hxp ↦ hxp.2 hx.2

/-- Simon Lemma 3.2, Borel-choice assertion.  The source's Hausdorff
measurability is `NullMeasurableSet`, so this also covers sets measurable
only in the completed Hausdorff measure. -/
theorem measurable_rectifiable_purelyUnrectifiable_decomposition {n : ℕ} {A : Set E}
    (hA : NullMeasurableSet A (μHE[n] : Measure E))
    (S : ℕ → Set E) (hcover : A ⊆ ⋃ j, S j) (hfinite : ∀ j, μHE[n] (S j) < ∞) :
    ∃ R P : Set E, A = R ∪ P ∧ Disjoint R P ∧ MeasurableSet R ∧
      NullMeasurableSet P (μHE[n] : Measure E) ∧
      CountablyRectifiable n R ∧ PurelyUnrectifiable n P := by
  let := sigmaFinite_restrict_of_hausdorff_finite_cover S hcover hfinite
  obtain ⟨M, hMmeas, hM, hpure⟩ :=
    exists_measurable_rectifiable_sdiff_purelyUnrectifiable (n := n) (A := A)
  obtain ⟨R, hRsub, hRmeas, hRae⟩ :=
    (hA.inter hMmeas.nullMeasurableSet).exists_measurable_subset_ae_eq
  have hnull : μHE[n] ((A ∩ M) \ R) = 0 := ae_le_set.mp hRae.symm.le
  refine ⟨R, A \ R, ?_, disjoint_sdiff_right, hRmeas,
    hA.diff hRmeas.nullMeasurableSet, hM.mono (hRsub.trans inter_subset_right), ?_⟩
  · ext x
    constructor
    · intro hx
      by_cases hxR : x ∈ R
      · exact Or.inl hxR
      · exact Or.inr ⟨hx, hxR⟩
    · rintro (hx | hx)
      · exact (hRsub hx).1
      · exact hx.1
  · apply (hpure.union (purelyUnrectifiable_of_measure_zero hnull)).mono
    intro x hx
    by_cases hxM : x ∈ M
    · exact Or.inr ⟨⟨hx.1, hxM⟩, hx.2⟩
    · exact Or.inl ⟨hx.1, hxM⟩

/-- Simon Lemma 3.2 in its full two-part source form, including the Borel
choice when the given set is Hausdorff measurable. -/
theorem simon_lemma_3_2 {n : ℕ} {A : Set E}
    (S : ℕ → Set E) (hcover : A ⊆ ⋃ j, S j) (hfinite : ∀ j, μHE[n] (S j) < ∞) :
    (∃ R P : Set E, A = R ∪ P ∧ Disjoint R P ∧
      CountablyRectifiable n R ∧ PurelyUnrectifiable n P) ∧
    (NullMeasurableSet A (μHE[n] : Measure E) →
      ∃ R P : Set E, A = R ∪ P ∧ Disjoint R P ∧ MeasurableSet R ∧
        NullMeasurableSet P (μHE[n] : Measure E) ∧
        CountablyRectifiable n R ∧ PurelyUnrectifiable n P) :=
  ⟨rectifiable_purelyUnrectifiable_decomposition S hcover hfinite,
    fun hA ↦ measurable_rectifiable_purelyUnrectifiable_decomposition hA S hcover hfinite⟩

end Decomposition

end Poincare.SimonGMT.Chapter03
