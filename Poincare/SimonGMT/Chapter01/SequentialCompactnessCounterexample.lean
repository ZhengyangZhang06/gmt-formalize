module

public import Poincare.SimonGMT.Chapter01.RadonOuterMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.ContinuousMap.CompactlySupported

@[expose] public section

/-!
# A counterexample to the printed Simon Theorem 4.16

The printed assumptions are locally compact, sigma-compact, and Hausdorff,
without metrizability or second countability.  They do not suffice for the
stated sequential conclusion.  On the compact cube `{0,1}^(Set Nat)`, put
`x_n(S) = 1` exactly when `n ∈ S`, and take the Dirac measures at these points.
Every subsequence is separated by the continuous coordinate associated with
its even-indexed terms.  In particular, no subsequence converges against all
compactly supported continuous real test functions.

The proof on page 37 uses Alaoglu to extract a subsequence.  General compactness
only supplies a subnet; a sequential conclusion requires additional hypotheses.
-/

open MeasureTheory Set Filter TopologicalSpace
open scoped CompactlySupported ENNReal Topology

namespace Poincare.SimonGMT.Chapter01

attribute [local instance] Classical.propDecidable

/-- A compact Hausdorff cube, with one two-point coordinate for each subset
of the natural numbers.  Compactness also supplies local compactness and
sigma-compactness, so all three printed topological hypotheses hold. -/
abbrev SimonCompactCube := Set ℕ → Fin 2

instance simonCompactCubeMeasurableSpace : MeasurableSpace SimonCompactCube :=
  borel SimonCompactCube

instance simonCompactCubeBorelSpace : BorelSpace SimonCompactCube := ⟨rfl⟩

/-- All printed topological hypotheses, with the stronger compactness
property made explicit. -/
theorem simonCompactCube_printed_hypotheses :
    CompactSpace SimonCompactCube ∧ LocallyCompactSpace SimonCompactCube ∧
      SigmaCompactSpace SimonCompactCube ∧ T2Space SimonCompactCube :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The `n`th point remembers membership of `n` in every subset of `Nat`. -/
noncomputable def simonCubePoint (n : ℕ) : SimonCompactCube :=
  fun S => if n ∈ S then 1 else 0

/-- Coordinate evaluation, regarded as a compactly supported real function.
The support is compact because the entire cube is compact. -/
noncomputable def simonCubeCoordinate (S : Set ℕ) : C_c(SimonCompactCube, ℝ) :=
  { toFun := fun x => ((x S : Fin 2) : ℝ)
    continuous_toFun :=
      (continuous_of_discreteTopology : Continuous (fun y : Fin 2 => (y : ℝ))).comp
        (continuous_apply S)
    hasCompactSupport' := HasCompactSupport.of_compactSpace _ }

@[simp] theorem simonCubeCoordinate_point (S : Set ℕ) (n : ℕ) :
    simonCubeCoordinate S (simonCubePoint n) = if n ∈ S then 1 else 0 := by
  classical
  by_cases h : n ∈ S <;> simp [simonCubeCoordinate, simonCubePoint, h]

/-- Dirac measures are regular even on a nonmetrizable Hausdorff space.
This direct proof does not use a second-countability regularity theorem. -/
theorem dirac_regular_of_t1 {X : Type*} [TopologicalSpace X] [T1Space X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (x : X) :
    (Measure.dirac x).Regular := by
  classical
  let : (Measure.dirac x).OuterRegular := ⟨fun A _ r hr => by
    by_cases hx : x ∈ A
    · refine ⟨univ, subset_univ _, isOpen_univ, ?_⟩
      simpa [Measure.dirac_apply_of_mem hx] using hr
    · refine ⟨{x}ᶜ, ?_, isClosed_singleton.isOpen_compl, ?_⟩
      · intro y hy hyx
        exact hx (mem_singleton_iff.mp hyx ▸ hy)
      · simpa [Measure.dirac_apply, hx] using hr⟩
  refine ⟨fun U _ r hr => ?_⟩
  by_cases hx : x ∈ U
  · refine ⟨{x}, singleton_subset_iff.mpr hx, isCompact_singleton, ?_⟩
    simpa [Measure.dirac_apply_of_mem hx] using hr
  · simp [Measure.dirac_apply, hx] at hr

/-- The uniformly bounded sequence used in the counterexample. -/
noncomputable def simonCubeDiracSequence (n : ℕ) : Measure SimonCompactCube :=
  Measure.dirac (simonCubePoint n)

theorem simonCubeDiracSequence_isRadon (n : ℕ) :
    IsRadonOuterMeasure (simonCubeDiracSequence n).toOuterMeasure := by
  let : (simonCubeDiracSequence n).Regular := dirac_regular_of_t1 (simonCubePoint n)
  exact isRadonOuterMeasure_toOuterMeasure (simonCubeDiracSequence n)

/-- In fact the bound is one for every set, not merely compact sets. -/
theorem simonCubeDiracSequence_uniform_bound (K : Set SimonCompactCube) :
    (⨆ n : ℕ, simonCubeDiracSequence n K) ≤ 1 := by
  classical
  refine iSup_le fun n => ?_
  simp only [simonCubeDiracSequence, Measure.dirac_apply]
  by_cases hx : simonCubePoint n ∈ K <;> simp [hx]

/-- Every strictly increasing subsequence has a continuous compactly
supported coordinate test whose integrals fail to converge to any real
number.  The even and odd subsubsequences have values one and zero. -/
theorem simonCubeDiracSequence_no_subsequence_limit
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ∃ f : C_c(SimonCompactCube, ℝ), ∀ c : ℝ,
      ¬ Tendsto (fun n => ∫ x, f x ∂simonCubeDiracSequence (φ n)) atTop (𝓝 c) := by
  classical
  let S : Set ℕ := range (fun j : ℕ => φ (2 * j))
  refine ⟨simonCubeCoordinate S, ?_⟩
  intro c hc
  have heven (j : ℕ) : φ (2 * j) ∈ S := mem_range_self j
  have hodd (j : ℕ) : φ (2 * j + 1) ∉ S := by
    rintro ⟨k, hk⟩
    have := hφ.injective hk
    omega
  have hmonoEven : StrictMono (fun j : ℕ => 2 * j) := by
    intro a b hab
    dsimp
    omega
  have hmonoOdd : StrictMono (fun j : ℕ => 2 * j + 1) := by
    intro a b hab
    dsimp
    omega
  have hlimOne : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 c) := by
    simpa [Function.comp_def, simonCubeDiracSequence, integral_dirac, heven] using
      hc.comp hmonoEven.tendsto_atTop
  have hlimZero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 c) := by
    simpa [Function.comp_def, simonCubeDiracSequence, integral_dirac, hodd] using
      hc.comp hmonoOdd.tendsto_atTop
  have hcOne : c = 1 := tendsto_nhds_unique hlimOne tendsto_const_nhds
  have hcZero : c = 0 := tendsto_nhds_unique hlimZero tendsto_const_nhds
  exact zero_ne_one (hcZero.symm.trans hcOne)

/-- Simon C01 4.16 is false as printed.  This fixed compact Hausdorff (hence
locally compact and sigma-compact) space carries a sequence of Radon measures
uniformly bounded on every compact set but with no vaguely convergent
subsequence, even when the proposed limiting measure is unrestricted. -/
theorem simon_theorem_4_16_counterexample :
    (∀ n, IsRadonOuterMeasure (simonCubeDiracSequence n).toOuterMeasure) ∧
    (∀ K : Set SimonCompactCube, IsCompact K →
      (⨆ n : ℕ, simonCubeDiracSequence n K) < ∞) ∧
    ¬ ∃ (φ : ℕ → ℕ) (_ : StrictMono φ) (μ : Measure SimonCompactCube),
      ∀ f : C_c(SimonCompactCube, ℝ),
        Tendsto (fun n => ∫ x, f x ∂simonCubeDiracSequence (φ n))
          atTop (𝓝 (∫ x, f x ∂μ)) := by
  refine ⟨simonCubeDiracSequence_isRadon, ?_, ?_⟩
  · intro K _
    exact (simonCubeDiracSequence_uniform_bound K).trans_lt ENNReal.one_lt_top
  · rintro ⟨φ, hφ, μ, hμ⟩
    obtain ⟨f, hf⟩ := simonCubeDiracSequence_no_subsequence_limit hφ
    exact hf (∫ x, f x ∂μ) (hμ f)

end Poincare.SimonGMT.Chapter01
