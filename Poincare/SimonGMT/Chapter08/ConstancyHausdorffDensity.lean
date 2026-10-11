module

public import Poincare.SimonGMT.Chapter08.StationaryHausdorff
public import Poincare.SimonGMT.Chapter02.SubmanifoldTopology
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

@[expose] public section

/-!
# Constructing the Hausdorff density in Simon's constancy theorem

Starting with Simon's actual `C²` local-parametrization definition, small
compact parameter balls give finite-Hausdorff-measure carrier pieces.
Second countability then gives a measurable, sigma-finite carrier, so the
Radon--Nikodym theorem constructs a nonnegative locally integrable density
for a stationary varifold supported on it. No density-existence premise
is used.

Source: Simon (8.4.1), proof after (4), printed pp. 214--215.
This does not yet identify the tangent field from the parametrizations or
transport the weak first-variation equation through those charts.
-/

open Set Filter MeasureTheory Metric Function
open scoped Topology ENNReal

namespace Poincare.SimonGMT.Chapter08
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
variable {N n : ℕ} {M : Set (Euclidean N)}

/-- Actual compact finite-measure pieces constructed from the source
parametrization, rather than imposed as an extra covering hypothesis. -/
theorem simonSubmanifold_exists_local_compact_carrier
    (hM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M)
    {y : Euclidean N} (hy : y ∈ M) :
    ∃ A K : Set (Euclidean N), IsOpen A ∧ y ∈ A ∧ IsCompact K ∧ K ⊆ M ∧
      A ∩ M ⊆ K ∧ Chapter01.simonHausdorffMeasureReal (n : ℝ) K < ∞ := by
  obtain ⟨D, W, φ, hyW, hφ⟩ := hM.exists_localRepresentation hy
  obtain ⟨u, hu, rfl⟩ : y ∈ φ '' D := by rw [hφ.image_eq]; exact ⟨hyW, hy⟩
  obtain ⟨r, hr, hrD⟩ := nhds_basis_closedBall.mem_iff.mp (hφ.isOpen_source.mem_nhds hu)
  have hbD : ball u r ⊆ D := ball_subset_closedBall.trans hrD
  obtain ⟨A, hAo, _, hA⟩ := hφ.exists_open_image_eq_inter isOpen_ball hbD
  have huA : φ u ∈ A ∩ M := by
    rw [← hA]
    exact mem_image_of_mem φ (mem_ball_self hr)
  let K := φ '' closedBall u r
  have hK : IsCompact K := (isCompact_closedBall u r).image_of_continuousOn
    (hφ.contDiffOn.continuousOn.mono hrD)
  have hKM : K ⊆ M := by
    intro x hx
    have hx' : x ∈ φ '' D := (image_mono hrD) hx
    rw [hφ.image_eq] at hx'
    exact hx'.2
  obtain ⟨L, hL⟩ := (hφ.contDiffOn.mono hrD).exists_lipschitzOnWith
    (by norm_num) (convex_closedBall u r) (isCompact_closedBall u r)
  have hraw : Measure.hausdorffMeasure (n : ℝ) K < ∞ := by
    apply (hL.hausdorffMeasure_image_le (Nat.cast_nonneg n)).trans_lt
    rw [ENNReal.rpow_natCast]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top)
      ((isCompact_closedBall u r).measure_lt_top (μ := Measure.hausdorffMeasure (n : ℝ)))
  refine ⟨A, K, hAo, huA.1, hK, hKM, ?_, ?_⟩
  · rw [← hA]
    exact image_mono ball_subset_closedBall
  · rw [Chapter01.simonHausdorffMeasureReal, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top
      (ENNReal.div_ne_top (Chapter01.realUnitBallVolume_ne_top _) (by simp)).lt_top hraw

/-- Countable compact carrier construction, with literal Simon
Hausdorff measure finite on every piece. -/
theorem simonSubmanifold_countable_compact_carrier
    (hM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M) :
    ∃ T : Set (Set (Euclidean N)), T.Countable ∧
      (∀ K ∈ T, IsCompact K ∧ Chapter01.simonHausdorffMeasureReal (n : ℝ) K < ∞) ∧
      ⋃₀ T = M := by
  classical
  choose A K hAo hyA hK hKM hAK hfin using
    fun x : M ↦ simonSubmanifold_exists_local_compact_carrier hM x.2
  have hcover : M ⊆ ⋃ x : M, A x := fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, hyA ⟨x, hx⟩⟩
  obtain ⟨S, hSc, hSM⟩ := (HereditarilyLindelofSpace.isLindelof M).elim_countable_subcover
    A hAo hcover
  refine ⟨K '' S, hSc.image K, ?_, ?_⟩
  · rintro B ⟨x, _, rfl⟩
    exact ⟨hK x, hfin x⟩
  · apply Subset.antisymm
    · rintro x ⟨B, ⟨i, _, rfl⟩, hx⟩
      exact hKM i hx
    · intro x hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hSM hx)
      exact mem_sUnion.mpr ⟨K i, mem_image_of_mem K hi, hAK i ⟨hxi, hx⟩⟩

theorem simonSubmanifold_measurableSet
    (hM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M) : MeasurableSet M := by
  obtain ⟨T, hTc, hT, rfl⟩ := simonSubmanifold_countable_compact_carrier hM
  exact MeasurableSet.sUnion hTc (fun K hK ↦ (hT K hK).1.measurableSet)

/-- Sigma-finiteness needed for Radon--Nikodym is proved from the actual
source manifold hypothesis, not required independently. -/
theorem simonSubmanifold_sigmaFinite_hausdorff
    (hM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M) :
    SigmaFinite ((Chapter01.simonHausdorffMeasureReal (n : ℝ)).restrict M) := by
  classical
  obtain ⟨T, hTc, hT, hTM⟩ := simonSubmanifold_countable_compact_carrier hM
  have hMm : MeasurableSet M := simonSubmanifold_measurableSet hM
  apply Measure.sigmaFinite_of_countable (hTc.insert Mᶜ)
  · intro K hK
    rcases mem_insert_iff.mp hK with rfl | hK
    · simp only [Measure.restrict_apply hMm.compl, compl_inter_self, measure_empty,
        ENNReal.zero_lt_top]
    · exact ((Measure.le_iff'.mp Measure.restrict_le_self) K).trans_lt (hT K hK).2
  · rw [sUnion_insert, hTM, compl_union_self]

namespace Varifold
variable {U : Set (Euclidean N)}

/-- Simon's Hausdorff density is constructed as the real-valued
Radon--Nikodym derivative. The following theorem proves its properties. -/
def constancyDensity (V : Varifold N n U) (M : Set (Euclidean N)) : Euclidean N → ℝ :=
  fun x ↦ (V.weight.rnDeriv ((Chapter01.simonHausdorffMeasureReal (n : ℝ)).restrict M) x).toReal

theorem Stationary.constancyDensity_representation {V : Varifold N n U}
    (hV : V.Stationary) (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M)
    (hM : U ∩ V.weight.support ⊆ M) :
    Measurable (V.constancyDensity M) ∧ (∀ x, 0 ≤ V.constancyDensity M x) ∧
      LocallyIntegrableOn (V.constancyDensity M) U
        ((Chapter01.simonHausdorffMeasureReal (n : ℝ)).restrict M) ∧
      ((Chapter01.simonHausdorffMeasureReal (n : ℝ)).restrict M).withDensity
        (fun x ↦ ENNReal.ofReal (V.constancyDensity M x)) = V.weight := by
  let ν := (Chapter01.simonHausdorffMeasureReal (X := Euclidean N) (n : ℝ)).restrict M
  let : SigmaFinite ν := simonSubmanifold_sigmaFinite_hausdorff hSM
  have hac : V.weight ≪ ν := hV.weight_absolutelyContinuous_carrier hM
  refine ⟨(Measure.measurable_rnDeriv V.weight ν).ennreal_toReal,
    fun _ ↦ ENNReal.toReal_nonneg, ?_, ?_⟩
  · intro x hx
    obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.mp (V.isOpen_domain.mem_nhds hx)
    refine ⟨closedBall x r, mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x hr), ?_⟩
    exact Measure.integrableOn_toReal_rnDeriv
      (V.weight_finite_on_compact _ (isCompact_closedBall x r) hrU)
  · change ν.withDensity (fun x ↦ ENNReal.ofReal ((V.weight.rnDeriv ν x).toReal)) = V.weight
    calc
      _ = ν.withDensity (V.weight.rnDeriv ν) := by
        apply withDensity_congr_ae
        filter_upwards [Measure.rnDeriv_ne_top V.weight ν] with x hx
        exact ENNReal.ofReal_toReal hx
      _ = V.weight := Measure.withDensity_rnDeriv_eq _ _ hac

/-- The constructed density gives the actual weighted integral, with an
integrability equivalence as well as equality of integral values. -/
theorem Stationary.integral_constancyDensity {V : Varifold N n U}
    (hV : V.Stationary) (hSM : Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M)
    (hM : U ∩ V.weight.support ⊆ M) (g : Euclidean N → ℝ) :
    (Integrable (fun x ↦ V.constancyDensity M x * g x)
      ((Chapter01.simonHausdorffMeasureReal (n : ℝ)).restrict M) ↔ Integrable g V.weight) ∧
      (∫ x, V.constancyDensity M x * g x
        ∂(Chapter01.simonHausdorffMeasureReal (n : ℝ)).restrict M) = ∫ x, g x ∂V.weight := by
  let : SigmaFinite ((Chapter01.simonHausdorffMeasureReal (n : ℝ)).restrict M) :=
    simonSubmanifold_sigmaFinite_hausdorff hSM
  exact ⟨integrable_toReal_rnDeriv_mul_iff (hV.weight_absolutelyContinuous_carrier hM),
    integral_toReal_rnDeriv_mul (hV.weight_absolutelyContinuous_carrier hM)⟩

end Varifold
end
end Poincare.SimonGMT.Chapter08
