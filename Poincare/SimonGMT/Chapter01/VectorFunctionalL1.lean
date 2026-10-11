module

public import Poincare.SimonGMT.Chapter01.VectorFunctionalEnvelope
public import Poincare.SimonGMT.Chapter01.RadonDensity
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

@[expose] public section

/-!
# The `L¹` extension in the proof of Simon Theorem 4.14

The source's local bound on a vector functional yields a dominating Radon
measure and a norm-at-most-one linear extension to vector-valued `L¹`.  The
compact-support density argument below works on locally compact Hausdorff
spaces, without normality, second countability, or sigma-compactness.

This closes the extension step without assuming a polar representation.
The existence of the measurable unit polar field is a separate remaining
step of the full theorem.
-/

open CompactlySupportedContinuousMap Set MeasureTheory TopologicalSpace
open scoped CompactlySupported ENNReal Topology

namespace Poincare.SimonGMT.Chapter01

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X]
  {H : Type v} [NormedAddCommGroup H] [NormedSpace ℝ H]

section Density

variable {μ : Measure X} [μ.Regular] {p : ℝ≥0∞}

/-- Vector-valued version of the compact-indicator approximation used in
Simon 4.10 and in the proof of 4.14. -/
theorem exists_compactlySupported_vector_eLpNorm_sub_indicator_le
    (hp : p ≠ ∞) {K : Set X} (hK : IsCompact K) (c : H)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : X → H, Continuous g ∧ HasCompactSupport g ∧
      eLpNorm (g - K.indicator (fun _ => c)) p μ ≤ ε := by
  obtain ⟨η, hηpos, hη⟩ := exists_eLpNorm_indicator_le (μ := μ) hp c hε
  have hηpos' : (0 : ℝ≥0∞) < η := ENNReal.coe_pos.mpr hηpos
  obtain ⟨V, hKV, hV, _, hVsmall⟩ :=
    hK.measurableSet.exists_isOpen_sdiff_lt (μ := μ)
      (hK.measure_lt_top (μ := μ)).ne hηpos'.ne'
  obtain ⟨f, hfK, hfc, hfV, hfI⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK hV hKV
  have hfzero : ∀ x ∉ V, f x = 0 := by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun h => hx (hfV h))
  have hgc : HasCompactSupport (fun x => f x • c) :=
    (show HasCompactSupport f from hfc).smul_right
  have hgcont : Continuous (fun x => f x • c) := f.continuous.smul continuous_const
  have hgmem : MemLp (fun x => f x • c) p μ :=
    hgcont.memLp_of_hasCompactSupport hgc
  have hgbound : ∀ x, ‖f x • c‖ ≤ ‖c‖ := by
    intro x
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hfI x).1]
    exact mul_le_of_le_one_left (norm_nonneg c) (hfI x).2
  have hdiff : ∀ x,
      ‖f x • c - K.indicator (fun _ => c) x‖ ≤
        ‖(V \ K).indicator (fun _ => c) x‖ := by
    intro x
    by_cases hxK : x ∈ K
    · simp [hxK, hfK hxK]
    · by_cases hxV : x ∈ V
      · simpa [hxK, hxV] using hgbound x
      · simp [hxK, hxV, hfzero x hxV]
  refine ⟨_, hgcont, hgc, ?_⟩
  exact (eLpNorm_mono (hgmem.aestronglyMeasurable.sub
    (aestronglyMeasurable_const.indicator hK.measurableSet)) hdiff).trans
      (hη _ hVsmall.le (hV.measurableSet.diff hK.measurableSet).nullMeasurableSet)

/-- Vector-valued compact-support density for an arbitrary Radon measure
on a locally compact Hausdorff space. -/
theorem exists_hasCompactSupport_vector_eLpNorm_sub_le_of_radon
    (hp : p ≠ ∞) {f : X → H} (hf : MemLp f p μ)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : X → H, eLpNorm (f - g) p μ ≤ ε ∧ Continuous g ∧ HasCompactSupport g := by
  apply hf.induction_dense hp (fun g => Continuous g ∧ HasCompactSupport g) ?_ ?_ hε
  · intro c A hA hAfin δ hδ
    obtain ⟨η, hηpos, hη⟩ := exists_Lp_half H μ p hδ
    obtain ⟨ζ, hζpos, hζ⟩ := exists_eLpNorm_indicator_le (μ := μ) hp c hηpos.ne'
    have hζpos' : (0 : ℝ≥0∞) < ζ := ENNReal.coe_pos.mpr hζpos
    obtain ⟨K, hKA, hK, hsmall⟩ :=
      hA.exists_isCompact_sdiff_lt hAfin.ne hζpos'.ne'
    have herror : eLpNorm (K.indicator (fun _ => c) - A.indicator (fun _ => c)) p μ ≤ η := by
      rw [← eLpNorm_neg, neg_sub, ← indicator_sdiff hKA]
      exact hζ _ hsmall.le (hA.diff hK.measurableSet).nullMeasurableSet
    obtain ⟨g, hgcont, hgc, hg⟩ :=
      exists_compactlySupported_vector_eLpNorm_sub_indicator_le (μ := μ) hp hK c hηpos.ne'
    refine ⟨g, ?_, hgcont, hgc⟩
    convert (hη _ _ hg herror).le using 2
    ext x
    simp
  · intro f g hf hg
    exact ⟨hf.1.add hg.1, hf.2.add hg.2⟩

end Density

/-- The natural linear map from vector-valued compactly supported continuous
functions into `L¹`; it need not be injective. -/
noncomputable def compactlySupportedToL1 (μ : Measure X) [IsFiniteMeasureOnCompacts μ] :
    C_c(X, H) →ₗ[ℝ] Lp H 1 μ where
  toFun f := (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport).toLp f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [T2Space X] [LocallyCompactSpace X] in
theorem compactlySupportedToL1_coeFn (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (f : C_c(X, H)) : compactlySupportedToL1 μ f =ᵐ[μ] f :=
  MemLp.coeFn_toLp (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport)

omit [T2Space X] [LocallyCompactSpace X] in
theorem compactlySupportedToL1_norm (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (f : C_c(X, H)) : ‖compactlySupportedToL1 μ f‖ = ∫ x, ‖f x‖ ∂μ := by
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [compactlySupportedToL1_coeFn μ f] with x hx
  rw [hx]

theorem compactlySupportedToL1_denseRange (μ : Measure X) [μ.Regular] :
    DenseRange (compactlySupportedToL1 μ (H := H)) := by
  intro F
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedEBall).2 fun ε hε => ?_
  obtain ⟨g, hg, hgcont, hgc⟩ :=
    exists_hasCompactSupport_vector_eLpNorm_sub_le_of_radon (by simp)
      (Lp.memLp F) hε.ne'
  let gCc : C_c(X, H) := ⟨⟨g, hgcont⟩, hgc⟩
  refine ⟨compactlySupportedToL1 μ gCc, mem_range_self gCc, ?_⟩
  rw [Metric.mem_closedEBall']
  change edist F ((hgcont.memLp_of_hasCompactSupport hgc).toLp g) ≤ ε
  rw [← Lp.toLp_coeFn F (Lp.memLp F), Lp.edist_toLp_toLp]
  exact hg

section Extension

variable [BorelSpace X]

/-- The proof of 4.14 supplies a norm-at-most-one `L¹` extension before the
unit polar field has been constructed.  This result starts only from the
printed compact-set boundedness assumption. -/
theorem simon_theorem_4_14_l1_extension (L : C_c(X, H) →ₗ[ℝ] ℝ)
    (hL : IsLocallyBoundedCcFunctional L) :
    ∃ Lbar : Lp H 1 (vectorFunctionalEnvelopeMeasure L hL) →L[ℝ] ℝ,
      ‖Lbar‖ ≤ 1 ∧
      ∀ f : C_c(X, H),
        Lbar (compactlySupportedToL1 (vectorFunctionalEnvelopeMeasure L hL) f) = L f := by
  let μ := vectorFunctionalEnvelopeMeasure L hL
  let e : C_c(X, H) →ₗ[ℝ] Lp H 1 μ := compactlySupportedToL1 μ
  have hdense : DenseRange e := compactlySupportedToL1_denseRange μ
  have hnorm : ∀ f : C_c(X, H), ‖L f‖ ≤ 1 * ‖e f‖ := by
    intro f
    rw [one_mul, compactlySupportedToL1_norm]
    exact norm_apply_le_integral_norm_vectorFunctionalEnvelopeMeasure L hL f
  exact ⟨L.extendOfNorm e, LinearMap.opNorm_extendOfNorm_le hdense zero_le_one hnorm,
    LinearMap.extendOfNorm_eq hdense ⟨1, hnorm⟩⟩

end Extension

end Poincare.SimonGMT.Chapter01
