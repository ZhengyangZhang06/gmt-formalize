module

public import Poincare.SimonGMT.Chapter04.PositiveMultiplicityScale

@[expose] public section

/-!
# Simon GMT, Chapter 4, the support consequence of (3.13)

Any strictly positive almost-everywhere lower multiplicity bound extends
to every support point in the stationary open domain. Consequently the
canonical positive-density carrier equals the support intersected with
that domain and is relatively closed there.

This does not assume or assert the separate density=multiplicity a.e.
identification required for the representation in (3.12).
-/

open Filter Function Metric Set MeasureTheory
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}

namespace RectifiableVarifold

variable {V : RectifiableVarifold (E := E) n}

/-- Arbitrary positive lower multiplicity bounds give the same lower
bound for stationary density almost everywhere. -/
theorem IsStationaryIn.lowerMultiplicity_le_density_ae
    {U : Set E} (hV : V.IsStationaryIn U) (hU : IsOpen U) (hn : 0 < n)
    {α : ℝ} (hα : 0 < α)
    (hθ : ∀ᵐ x ∂V.weight.restrict U, α ≤ V.multiplicity x) :
    ∀ᵐ x ∂V.weight.restrict U, α ≤ V.stationaryDensityReal x := by
  rw [ae_restrict_iff' hU.measurableSet]
  filter_upwards [V.ae_weight_of_ae_restrict V.approximate_tangent] with x hx hxU
  exact V.lowerMultiplicity_le_density_of_approximateTangent hU hn hα hθ hxU hx
    (IsStationaryIn.tendsto_densityQuotient_real (V := V) hV hU hxU)

/-- Upper semicontinuity promotes the a.e. lower bound to every support
point, for the full positive-constant hypothesis of Simon (3.13). -/
theorem IsStationaryIn.lowerMultiplicity_le_density_of_mem_support
    {U : Set E} (hV : V.IsStationaryIn U) (hU : IsOpen U) (hn : 0 < n)
    {α : ℝ} (hα : 0 < α)
    (hθ : ∀ᵐ x ∂V.weight.restrict U, α ≤ V.multiplicity x)
    {x : E} (hx : x ∈ U) (hsupp : x ∈ V.weight.support) :
    α ≤ V.stationaryDensityReal x := by
  by_contra hnot
  have hlt : V.stationaryDensityReal x < α := lt_of_not_ge hnot
  have hupper := IsStationaryIn.upperSemicontinuousOn_stationaryDensityReal
    (V := V) hV hU x hx α hlt
  rw [hU.nhdsWithin_eq hx] at hupper
  have hneigh : {y | V.stationaryDensityReal y < α ∧ y ∈ U} ∈ 𝓝 x :=
    hupper.and (hU.mem_nhds hx)
  have hpos := (Measure.mem_support_iff_forall (μ := V.weight) x).mp hsupp _ hneigh
  have hae := hV.lowerMultiplicity_le_density_ae hU hn hα hθ
  rw [ae_restrict_iff' hU.measurableSet] at hae
  have hz : V.weight {y | V.stationaryDensityReal y < α ∧ y ∈ U} = 0 := by
    apply measure_mono_null (t := {y | ¬ (y ∈ U → α ≤ V.stationaryDensityReal y)})
    · intro y hy hgood
      exact (not_le_of_gt hy.1) (hgood hy.2)
    · exact ae_iff.mp hae
  exact hpos.ne' hz

/-- Stationary density is zero outside the weight support. -/
theorem IsStationaryIn.stationaryDensity_eq_zero_of_notMem_support
    {U : Set E} (hV : V.IsStationaryIn U) (hU : IsOpen U)
    {x : E} (hx : x ∈ U) (hsupp : x ∉ V.weight.support) :
    V.stationaryDensity x = 0 := by
  obtain ⟨R, hR, hzero⟩ := nhds_basis_closedBall.notMem_measureSupport.mp hsupp
  have ht : Tendsto (V.densityQuotient x) (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioc_mem_nhdsGT hR] with r hr
    have hz : V.weight (closedBall x r) = 0 :=
      measure_mono_null (closedBall_subset_closedBall hr.2) hzero
    rw [V.densityQuotient_eq x hr.1, hz, ENNReal.zero_div]
  exact tendsto_nhds_unique (IsStationaryIn.tendsto_densityQuotient (V := V) hV hU hx) ht

/-- Positive canonical density always implies membership in the support. -/
theorem IsStationaryIn.canonicalDensityCarrier_subset_support
    {U : Set E} (hV : V.IsStationaryIn U) (hU : IsOpen U) :
    V.canonicalDensityCarrier U ⊆ V.weight.support ∩ U := by
  intro x hx
  refine ⟨?_, hx.1⟩
  by_contra hs
  exact (ne_of_gt hx.2) (hV.stationaryDensity_eq_zero_of_notMem_support hU hx.1 hs)

/-- Simon (3.13), support conclusion: a uniform positive lower
multiplicity makes the canonical carrier exactly the support in `U`. -/
theorem IsStationaryIn.canonicalDensityCarrier_eq_support_inter
    {U : Set E} (hV : V.IsStationaryIn U) (hU : IsOpen U) (hn : 0 < n)
    {α : ℝ} (hα : 0 < α)
    (hθ : ∀ᵐ x ∂V.weight.restrict U, α ≤ V.multiplicity x) :
    V.canonicalDensityCarrier U = V.weight.support ∩ U := by
  apply subset_antisymm (hV.canonicalDensityCarrier_subset_support hU)
  intro x hx
  refine ⟨hx.2, ?_⟩
  exact (ENNReal.toReal_pos_iff.mp
    (hα.trans_le (hV.lowerMultiplicity_le_density_of_mem_support hU hn hα hθ hx.2 hx.1))).1

/-- The canonical carrier is relatively closed, and its canonical
multiplicity is at least the original positive lower bound everywhere. -/
theorem IsStationaryIn.canonicalDensityCarrier_closed_and_lower_bound
    {U : Set E} (hV : V.IsStationaryIn U) (hU : IsOpen U) (hn : 0 < n)
    {α : ℝ} (hα : 0 < α)
    (hθ : ∀ᵐ x ∂V.weight.restrict U, α ≤ V.multiplicity x) :
    IsClosed {x : U | (x : E) ∈ V.canonicalDensityCarrier U} ∧
      ∀ x ∈ V.canonicalDensityCarrier U, α ≤ V.stationaryDensityReal x := by
  have heq := hV.canonicalDensityCarrier_eq_support_inter hU hn hα hθ
  constructor
  · have hset : {x : U | (x : E) ∈ V.canonicalDensityCarrier U} =
        ((↑) : U → E) ⁻¹' V.weight.support := by
      ext x
      simp only [heq, mem_ofPred_eq, mem_inter_iff, x.property, and_true, mem_preimage]
    rw [hset]
    exact Measure.isClosed_support.preimage continuous_subtype_val
  · intro x hx
    rw [heq] at hx
    exact hV.lowerMultiplicity_le_density_of_mem_support hU hn hα hθ hx.2 hx.1

/-- The source's Hausdorff-a.e. formulation of the same support and
pointwise lower-multiplicity conclusions. -/
theorem IsStationaryIn.simon_3_13_support
    {U : Set E} (hV : V.IsStationaryIn U) (hU : IsOpen U) (hn : 0 < n)
    {α : ℝ} (hα : 0 < α)
    (hθ : ∀ᵐ x ∂(Measure.euclideanHausdorffMeasure n).restrict V.carrier,
      α ≤ V.multiplicity x) :
    V.canonicalDensityCarrier U = V.weight.support ∩ U ∧
      IsClosed {x : U | (x : E) ∈ V.canonicalDensityCarrier U} ∧
      ∀ x ∈ V.canonicalDensityCarrier U, α ≤ V.stationaryDensityReal x := by
  have hθ' := ae_restrict_of_ae (μ := V.weight) (s := U) (V.ae_weight_of_ae_restrict hθ)
  exact ⟨hV.canonicalDensityCarrier_eq_support_inter hU hn hα hθ',
    hV.canonicalDensityCarrier_closed_and_lower_bound hU hn hα hθ'⟩

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
