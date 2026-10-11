module

public import Poincare.SimonGMT.Chapter02.AreaDerivative

public section

/-!
# Nonlinear area formula for regular parametrizations

This module proves Simon's injective nonlinear area formula in arbitrary
codimension when the derivative is injective at every source point. The
domain need only be measurable, and the supplied derivatives may be within
derivatives. In particular, no continuity of the derivative and no area or
measure-density identity are assumed.

The proof partitions the source into measurable linear-approximation pieces,
uses sharp Hausdorff estimates on each piece, and lets the relative error
tend to one. Critical points and noninjective multiplicities remain separate
obligations for the full Lipschitz area formula.
-/

open Function MeasureTheory Module Set Filter
open scoped ENNReal NNReal Topology Function

namespace Poincare.SimonGMT.Chapter02

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F]

private theorem area_comparison_of_injective_derivative
    {s : Set E} {f : E → F} {f' : E → E →L[ℝ] F}
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hreg : ∀ x ∈ s, Injective (f' x)) (hinj : InjOn f s)
    {q : ℝ≥0} (hq : 1 < q) :
    μHE[finrank ℝ E] (f '' s) ≤
        (q : ℝ≥0∞) ^ 2 * ∫⁻ x in s, ENNReal.ofReal (f' x).normDet ∂μHE[finrank ℝ E] ∧
      (∫⁻ x in s, ENNReal.ofReal (f' x).normDet ∂μHE[finrank ℝ E]) ≤
        (q : ℝ≥0∞) ^ 2 * μHE[finrank ℝ E] (f '' s) := by
  classical
  rcases eq_empty_or_nonempty s with rfl | hsne
  · simp
  have hchoice : ∀ L : E →L[ℝ] F, ∃ δ : ℝ≥0, 0 < δ ∧ (Injective L →
      (∀ B : E →L[ℝ] F, ‖B - L‖ ≤ δ →
        ENNReal.ofReal B.normDet ≤ q * ENNReal.ofReal L.normDet ∧
        ENNReal.ofReal L.normDet ≤ q * ENNReal.ofReal B.normDet) ∧
      (∀ (t : Set E) (g : E → F), _root_.ApproximatesLinearOn g L t δ →
        μHE[finrank ℝ E] (g '' t) ≤
            q * (ENNReal.ofReal L.normDet * μHE[finrank ℝ E] t) ∧
          ENNReal.ofReal L.normDet * μHE[finrank ℝ E] t ≤
            q * μHE[finrank ℝ E] (g '' t))) := by
    intro L
    by_cases hL : Injective L
    · obtain ⟨δ, hδ, hJ, harea⟩ := exists_radius_area_and_jacobian_comparison L hL hq
      exact ⟨δ, hδ, fun _ ↦ ⟨hJ, harea⟩⟩
    · exact ⟨1, zero_lt_one, fun h ↦ (hL h).elim⟩
  choose δ hδpos hδ using hchoice
  obtain ⟨t, L, hdisj, ht, hcover, happrox, hactual⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf'
      δ (fun L ↦ (hδpos L).ne')
  have hLreg (i : ℕ) : Injective (L i) := by
    obtain ⟨x, hx, hL⟩ := hactual hsne i
    rw [hL]
    exact hreg x hx
  have hseq : s = ⋃ i, s ∩ t i := by
    rw [← inter_iUnion]
    exact Subset.antisymm (subset_inter Subset.rfl hcover) inter_subset_left
  have hsumimage : μHE[finrank ℝ E] (f '' s) =
      ∑' i, μHE[finrank ℝ E] (f '' (s ∩ t i)) := by
    conv_lhs => rw [hseq, image_iUnion]
    apply measure_iUnion
    · intro i j hij
      exact Disjoint.image (Disjoint.mono inter_subset_right inter_subset_right (hdisj hij))
        hinj inter_subset_left inter_subset_left
    · intro i
      apply (hs.inter (ht i)).image_of_continuousOn_injOn
      · exact (fun x hx ↦ (hf' x hx.1).continuousWithinAt.mono inter_subset_left)
      · exact hinj.mono inter_subset_left
  have hsumintegral :
      (∫⁻ x in s, ENNReal.ofReal (f' x).normDet ∂μHE[finrank ℝ E]) =
        ∑' i, ∫⁻ x in s ∩ t i, ENNReal.ofReal (f' x).normDet ∂μHE[finrank ℝ E] := by
    conv_lhs => rw [hseq]
    exact lintegral_iUnion (fun i ↦ hs.inter (ht i))
      (pairwise_disjoint_mono hdisj (fun _ ↦ inter_subset_right)) _
  have hpiece (i : ℕ) :
      μHE[finrank ℝ E] (f '' (s ∩ t i)) ≤ (q : ℝ≥0∞) ^ 2 *
          ∫⁻ x in s ∩ t i, ENNReal.ofReal (f' x).normDet ∂μHE[finrank ℝ E] ∧
        (∫⁻ x in s ∩ t i, ENNReal.ofReal (f' x).normDet ∂μHE[finrank ℝ E]) ≤
          (q : ℝ≥0∞) ^ 2 * μHE[finrank ℝ E] (f '' (s ∩ t i)) := by
    have hJ := (hδ (L i) (hLreg i)).1
    obtain ⟨harea_upper, harea_lower⟩ :=
      (hδ (L i) (hLreg i)).2 (s ∩ t i) f (happrox i)
    have hderiv := area_approximation_norm_fderiv_sub_le μHE[finrank ℝ E]
      (happrox i) (hs.inter (ht i)) f' (fun x hx ↦ (hf' x hx.1).mono inter_subset_left)
    have hJupper :
        (∫⁻ x in s ∩ t i, ENNReal.ofReal (f' x).normDet ∂μHE[finrank ℝ E]) ≤
          q * (ENNReal.ofReal (L i).normDet * μHE[finrank ℝ E] (s ∩ t i)) := by
      calc
        _ ≤ ∫⁻ _ in s ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (L i).normDet
            ∂μHE[finrank ℝ E] := by
          apply lintegral_mono_ae
          filter_upwards [hderiv] with x hx
          exact (hJ (f' x) hx).1
        _ = _ := by rw [setLIntegral_const, mul_assoc]
    have hJlower : ENNReal.ofReal (L i).normDet * μHE[finrank ℝ E] (s ∩ t i) ≤
        q * ∫⁻ x in s ∩ t i, ENNReal.ofReal (f' x).normDet ∂μHE[finrank ℝ E] := by
      calc
        _ = ∫⁻ _ in s ∩ t i, ENNReal.ofReal (L i).normDet ∂μHE[finrank ℝ E] :=
          (setLIntegral_const _ _).symm
        _ ≤ ∫⁻ x in s ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (f' x).normDet
            ∂μHE[finrank ℝ E] := by
          apply lintegral_mono_ae
          filter_upwards [hderiv] with x hx
          exact (hJ (f' x) hx).2
        _ = _ := lintegral_const_mul' _ _ ENNReal.coe_ne_top
    constructor
    · calc
        _ ≤ q * (ENNReal.ofReal (L i).normDet * μHE[finrank ℝ E] (s ∩ t i)) := harea_upper
        _ ≤ q * (q * ∫⁻ x in s ∩ t i, ENNReal.ofReal (f' x).normDet
            ∂μHE[finrank ℝ E]) := by gcongr
        _ = _ := by rw [pow_two, mul_assoc]
    · calc
        _ ≤ q * (ENNReal.ofReal (L i).normDet * μHE[finrank ℝ E] (s ∩ t i)) := hJupper
        _ ≤ q * (q * μHE[finrank ℝ E] (f '' (s ∩ t i))) := by gcongr
        _ = _ := by rw [pow_two, mul_assoc]
  rw [hsumimage, hsumintegral]
  constructor
  · calc
      _ ≤ ∑' i, (q : ℝ≥0∞) ^ 2 *
          ∫⁻ x in s ∩ t i, ENNReal.ofReal (f' x).normDet ∂μHE[finrank ℝ E] :=
        ENNReal.tsum_le_tsum (fun i ↦ (hpiece i).1)
      _ = _ := ENNReal.tsum_mul_left
  · calc
      _ ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * μHE[finrank ℝ E] (f '' (s ∩ t i)) :=
        ENNReal.tsum_le_tsum (fun i ↦ (hpiece i).2)
      _ = _ := ENNReal.tsum_mul_left

/-- Simon (3.2) for an injective differentiable parametrization with
injective derivative, in arbitrary codimension. This uses normalized
Hausdorff measure in the source dimension on both spaces. -/
theorem injective_area_formula_of_injective_derivative
    {s : Set E} {f : E → F} {f' : E → E →L[ℝ] F}
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hreg : ∀ x ∈ s, Injective (f' x)) (hinj : InjOn f s) :
    μHE[finrank ℝ E] (f '' s) =
      ∫⁻ x in s, ENNReal.ofReal (f' x).normDet ∂μHE[finrank ℝ E] := by
  have hlimit (a : ℝ≥0∞) :
      Tendsto (fun q : ℝ≥0 ↦ (q : ℝ≥0∞) ^ 2 * a) (𝓝[>] 1) (𝓝 a) := by
    have hcoe : Tendsto (fun q : ℝ≥0 ↦ (q : ℝ≥0∞)) (𝓝[>] 1) (𝓝 1) :=
      (ENNReal.tendsto_coe.2 tendsto_id).mono_left nhdsWithin_le_nhds
    simpa only [one_pow, one_mul] using
      ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow (n := 2) hcoe) (Or.inl (by simp))
  apply le_antisymm
  · apply ge_of_tendsto (hlimit _)
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact (area_comparison_of_injective_derivative hs hf' hreg hinj hq).1
  · apply ge_of_tendsto (hlimit _)
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact (area_comparison_of_injective_derivative hs hf' hreg hinj hq).2

end
end Poincare.SimonGMT.Chapter02
