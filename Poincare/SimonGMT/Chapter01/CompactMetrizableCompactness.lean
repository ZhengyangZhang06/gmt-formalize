module

public import Poincare.SimonGMT.Chapter01.RadonOuterMeasure
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.ContinuousMap.CompactlySupported

@[expose] public section

/-!
# A corrected compact-domain version of Simon 4.16

The source's Hausdorff and sigma-compact hypotheses alone do not imply the
sequential conclusion, as shown in `SequentialCompactnessCounterexample`.
Here compactness and metrizability are explicit sufficient hypotheses.
The proof extracts a subsequence of the masses and normalized probability
measures together, and then reconstructs the finite-measure limit.
-/

open MeasureTheory Set Filter TopologicalSpace
open scoped CompactlySupported ENNReal NNReal Topology

namespace Poincare.SimonGMT.Chapter01

universe u

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- Finite measures with uniformly bounded mass on a nonempty compact
metrizable space have a weakly convergent subsequence. -/
theorem finiteMeasure_tendsto_subseq_of_compact_metrizable [Nonempty X]
    (μ : ℕ → FiniteMeasure X) (C : ℝ≥0) (hC : ∀ n, (μ n).mass ≤ C) :
    ∃ (φ : ℕ → ℕ) (_ : StrictMono φ) (ν : FiniteMeasure X),
      Tendsto (fun n => μ (φ n)) atTop (𝓝 ν) := by
  let u : ℕ → ℝ≥0 × ProbabilityMeasure X := fun n => ((μ n).mass, (μ n).normalize)
  have hcompact : IsCompact (Icc (0 : ℝ≥0) C ×ˢ (univ : Set (ProbabilityMeasure X))) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨a, _, φ, hφ, ht⟩ := hcompact.tendsto_subseq (fun n =>
    show u n ∈ Icc (0 : ℝ≥0) C ×ˢ (univ : Set (ProbabilityMeasure X)) from
      ⟨⟨zero_le, hC n⟩, mem_univ _⟩)
  let reconstruct : ℝ≥0 × ProbabilityMeasure X → FiniteMeasure X :=
    fun a => a.1 • a.2.toFiniteMeasure
  have hcont : Continuous reconstruct :=
    continuous_fst.smul (ProbabilityMeasure.toFiniteMeasure_continuous.comp continuous_snd)
  refine ⟨φ, hφ, reconstruct a, ?_⟩
  have hlimit := (hcont.tendsto a).comp ht
  exact hlimit.congr' (Eventually.of_forall fun n =>
    (FiniteMeasure.self_eq_mass_smul_normalize (μ (φ n))).symm)

/-- A corrected version of Simon 4.16 for compact metrizable spaces.
The compact-set mass bound is retained literally.  No nonemptiness or
probability-measure assumption is imposed on the sequence. -/
theorem simon_theorem_4_16_compact_metrizable
    (μ : ℕ → Measure X)
    (hbound : ∀ K : Set X, IsCompact K → (⨆ n : ℕ, μ n K) < ∞) :
    ∃ (φ : ℕ → ℕ) (_ : StrictMono φ) (ν : Measure X),
      IsRadonOuterMeasure ν.toOuterMeasure ∧
      ∀ f : C_c(X, ℝ),
        Tendsto (fun n => ∫ x, f x ∂μ (φ n)) atTop (𝓝 (∫ x, f x ∂ν)) := by
  classical
  by_cases hX : Nonempty X
  · let : Nonempty X := hX
    let M := ⨆ n : ℕ, μ n univ
    have hM : M < ∞ := hbound univ isCompact_univ
    let μf : ℕ → FiniteMeasure X := fun n =>
      ⟨μ n, ⟨(le_iSup (fun n => μ n univ) n).trans_lt hM⟩⟩
    have hmass : ∀ n, (μf n).mass ≤ M.toNNReal := by
      intro n
      apply ENNReal.coe_le_coe.mp
      rw [FiniteMeasure.ennreal_mass, ENNReal.coe_toNNReal hM.ne]
      exact le_iSup (fun n => μ n univ) n
    obtain ⟨φ, hφ, ν, hν⟩ :=
      finiteMeasure_tendsto_subseq_of_compact_metrizable μf M.toNNReal hmass
    refine ⟨φ, hφ, ν, isRadonOuterMeasure_toOuterMeasure (ν : Measure X), ?_⟩
    intro f
    exact (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hν)
      f.toBoundedContinuousFunction
  · let : IsEmpty X := not_nonempty_iff.mp hX
    refine ⟨id, strictMono_id, 0, isRadonOuterMeasure_toOuterMeasure 0, ?_⟩
    intro f
    have hf : ∀ x, f x = 0 := fun x => isEmptyElim x
    simpa only [hf, integral_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

end Poincare.SimonGMT.Chapter01
