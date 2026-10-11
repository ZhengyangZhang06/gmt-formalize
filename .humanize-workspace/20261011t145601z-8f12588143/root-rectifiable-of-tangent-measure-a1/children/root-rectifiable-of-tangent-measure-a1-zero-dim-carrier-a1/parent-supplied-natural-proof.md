# Parent-supplied natural-language proof

- Parent DAG node: `root.rectifiable_of_tangent_measure-a1`
- Child DAG node: `root.rectifiable_of_tangent_measure-a1.zero_dim_carrier-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is Step 2 (case n = 0) of the parent proof. In the parent, the hypothesis of this child is supplied by the lower-density child applied with n = 0 (ρ⁰ = 1); the parent shows μ({x}) > 0 a.e. and takes R to be the set of atoms.

1. Atoms. Let x satisfy the hypothesis with constant c > 0 and threshold ρ₀ > 0, i.e. μ(B_ρ(x)) ≥ c for 0 < ρ < ρ₀. For any r > 0, ρ := min(r/2, ρ₀/2) lies in (0, ρ₀) and ρ < r, so μ(B_r(x)) ≥ μ(B_ρ(x)) ≥ c. The open balls B_{1/(k+1)}(x), k ∈ ℕ, decrease; their intersection is {x} (if y ≠ x choose k with 1/(k+1) < |y − x|); and μ(B_1(x)) ≤ μ(B̄_1(x)) < ∞ since B̄_1(x) is compact. By continuity from above (Mathlib `Antitone.measure_iInter`), μ({x}) = inf_k μ(B_{1/(k+1)}(x)) ≥ c > 0. Hence μ({x}) > 0 for μ-a.e. x.

2. Countably many atoms. μ is finite on compact sets, hence locally finite, hence σ-finite because ℝ^N is σ-compact (Mathlib instance `sigmaFinite_of_locallyFinite`), in particular s-finite. The singletons {x}, x ∈ ℝ^N, form a family of pairwise disjoint measurable sets, so only countably many of them have positive measure (Mathlib `Measure.countable_meas_pos_of_disjoint_iUnion`; elementarily, B̄_k(0) contains at most m μ(B̄_k(0)) points of mass ≥ 1/m). Thus R := {x : μ({x}) > 0} is countable.

3. R is Borel, being a countable union of closed singletons. By step 1, ℝ^N ∖ R = {x : μ({x}) = 0} is μ-null, i.e. μ(ℝ^N ∖ R) = 0.

4. Countable 0-rectifiability. Take the exceptional set M₀ := ∅ (H⁰(∅) = 0). If R = ∅, the constant maps F_j ≡ 0 : ℝ⁰ → ℝ^N work. Otherwise write R = {e_j : j ∈ ℕ} (Mathlib `Set.Countable.exists_eq_range`) and let F_j : ℝ⁰ → ℝ^N be the constant map with value e_j; it is Lipschitz with constant 0, and since ℝ⁰ = EuclideanSpace ℝ (Fin 0) is nonempty (it contains 0), e_j ∈ F_j(ℝ⁰). Hence R ⊆ M₀ ∪ ⋃_j F_j(ℝ⁰), which is Definition 1.1 with n = 0, i.e. CountablyRectifiable 0 R. ∎

Formalization appendix (verified, supplementary to the proof above). The following Lean proof of exactly this frozen statement compiled without errors or sorry against the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c, simongmt 2b366308), placed after `import GMT.Ch03.Submission` inside `namespace GMT.Ch03` with the contract's opens (`open Filter MeasureTheory Module Set`, `open scoped CompactlySupported ENNReal NNReal Topology`, `open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt HasWeightedApproximateTangentSpaceAt PurelyUnrectifiable blowUpMap)`); `#print axioms` reports only [propext, Classical.choice, Quot.sound]. It follows the numbered steps above.

```lean
theorem Submission.tangentMeasure_zero_dim_carrier : (∀ (N : ℕ) (μ : Measure (Rn N)), (∀ K : Set (Rn N), IsCompact K → μ K < ∞) → (∀ᵐ x ∂μ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ENNReal.ofReal c ≤ μ (Metric.ball x ρ)) → ∃ R : Set (Rn N), MeasurableSet R ∧ CountablyRectifiable 0 R ∧ μ Rᶜ = 0) := by
  intro N μ hfin hae
  haveI : IsFiniteMeasureOnCompacts μ := ⟨hfin⟩
  have hatom : ∀ᵐ x ∂μ, 0 < μ {x} := by
    filter_upwards [hae] with x hx
    obtain ⟨c, hc, hev⟩ := hx
    obtain ⟨ρ₀, hρ₀, hρ₀'⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hev
    have hall : ∀ r : ℝ, 0 < r → ENNReal.ofReal c ≤ μ (Metric.ball x r) := by
      intro r hr
      have hmin : min (r / 2) (ρ₀ / 2) ∈ Set.Ioo 0 ρ₀ :=
        ⟨by positivity, lt_of_le_of_lt (min_le_right _ _) (by linarith)⟩
      exact (hρ₀' hmin).trans (measure_mono (Metric.ball_subset_ball
        ((min_le_left _ _).trans (by linarith))))
    have hanti : Antitone (fun k : ℕ => Metric.ball x (1 / ((k : ℝ) + 1))) := by
      intro k l hkl
      apply Metric.ball_subset_ball
      gcongr
    have hinter : (⋂ k : ℕ, Metric.ball x (1 / ((k : ℝ) + 1))) = {x} := by
      ext y
      simp only [Set.mem_iInter, Metric.mem_ball, Set.mem_singleton_iff]
      constructor
      · intro h
        by_contra hne
        have hpos : 0 < dist y x := dist_pos.mpr hne
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
        exact absurd (h k) (not_lt.mpr hk.le)
      · rintro rfl k
        simp only [dist_self]
        positivity
    have hlim : μ {x} = ⨅ k : ℕ, μ (Metric.ball x (1 / ((k : ℝ) + 1))) := by
      rw [← hinter]
      exact hanti.measure_iInter (fun k => measurableSet_ball.nullMeasurableSet)
        ⟨0, (measure_mono Metric.ball_subset_closedBall).trans_lt
          (isCompact_closedBall x _).measure_lt_top |>.ne⟩
    rw [hlim]
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hc) (le_iInf fun k => hall _ (by positivity))
  set R := {x : Rn N | 0 < μ {x}} with hRdef
  have hRc : R.Countable := by
    have := Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ)
      (As := fun x : Rn N => ({x} : Set (Rn N))) (fun x => measurableSet_singleton x)
      (fun x y hxy => Set.disjoint_singleton.mpr hxy)
    simpa using this
  refine ⟨R, hRc.measurableSet, ?_, ?_⟩
  · rcases R.eq_empty_or_nonempty with hR | hR
    · rw [hR]
      exact ⟨∅, measure_empty, fun _ _ => 0, fun _ => ⟨0, LipschitzWith.const 0⟩, by simp⟩
    · obtain ⟨e, he⟩ := hRc.exists_eq_range hR
      refine ⟨∅, measure_empty, fun j _ => e j, fun j => ⟨0, LipschitzWith.const _⟩, ?_⟩
      intro x hx
      rw [he] at hx
      obtain ⟨j, rfl⟩ := hx
      exact Or.inr (Set.mem_iUnion.mpr ⟨j, ⟨0, rfl⟩⟩)
  · rw [ae_iff] at hatom
    refine measure_mono_null (fun x hx => ?_) hatom
    simpa [R] using hx
```

## Key steps

1. A uniform lower bound for μ(B_ρ(x)) at small radii and local finiteness give μ({x}) ≥ c > 0 by continuity from above.
2. μ is σ-finite, so the set R of atoms of μ is countable.
3. R is Borel and μ(ℝ^N ∖ R) = 0 by the first step.
4. A countable set is covered by the ranges of constant (Lipschitz) maps ℝ⁰ → ℝ^N, hence is countably 0-rectifiable.

## Reference use

### local-project

Queries:
- `cat local-references/d498d77b74ea2063/manifest.json (project d09bc8a18ce60face651f042976e8465f21f0f68, mathlib 25730c7c759d108ef87ab70af2342a196760f79d); diff project/GMT/Ch03/Contract.lean against the workspace contract (identical)`
- `grep -n theorem/def simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (CountablyRectifiable, countablyRectifiable_iUnion, countablyRectifiable_range, blowUpMap, regular_euclideanHausdorffMeasure_restrict_submodule, support_euclideanHausdorffMeasure_restrict_submodule)`
- `grep -n theorem simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean (locallyFinite_planeMeasure, planeMeasure_unit_closedBall, tangentDensityCutoff, one_le_density_of_approximateTangent)`
- `grep -rn "μHE\[" mathlib/Mathlib; read mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (euclideanHausdorffMeasure_def, isAddHaarMeasure_euclideanHausdorffMeasure, Isometry.map_euclideanHausdorffMeasure, euclideanHausdorffMeasure_smul₀, InnerProductSpace.euclideanHausdorffMeasure_eq_volume)`
- `grep -rn "LipschitzOnWith.extend_real|LipschitzOnWith.extend_pi|extend_finite_dimension" mathlib/Mathlib`
- `grep -rn "IsSigmaCompact.measurableSet|isSigmaCompact_range" mathlib/Mathlib (no IsSigmaCompact.measurableSet; isSigmaCompact_range in Topology/Compactness/SigmaCompact.lean)`
- `grep -rn "countable_meas_pos" mathlib/Mathlib (Measure.countable_meas_pos_of_disjoint_iUnion in Typeclasses/SFinite.lean); grep sigmaFinite_of_locallyFinite`
- `grep -n "starProjection_norm_le|norm_starProjection_apply_le|starProjection_eq_self_iff|orthogonalProjectionOnto|starProjection_apply" mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `grep IsSeparable.exists_countable_dense_subset, IsSeparable.of_separableSpace, exists_countable_dense, Dense.exists_dist_lt, exists_linearIndependent_of_le_finrank, finrank_span_eq_card, stdOrthonormalBasis/reindex, nhdsGT_basis, Antitone.measure_iInter, tendsto_measure_iInter_atTop, nullSingletonClass_hausdorff, mem_support_iff_forall, infDist_lt_iff, continuous_infDist_pt, integral_pos_iff_support_of_nonneg, integral_mono_of_nonneg, integral_indicator_one, integrableOn_const, Continuous.integrable_of_hasCompactSupport, ofReal_le_ofReal_iff'`
- `sed -n 60,280p book/chapter-03.txt (Remark 1.5(3) lines 91-105; proof of 1.6 '⇐' lines 145-274)`
- `python: contract_scope() and validate_lean_statement() from verifier/gmt-compare.py and verifier/lean_contract.py applied to every proposed lean_statement`
- `grep -rl for each proposed lean_name over .humanize, GMT and simongmt/Poincare (no match); dag.json lean_name listing`
- `lake env lean /tmp/rtm_scratch/Challenge.lean, /tmp/rtm_scratch/Assembly.lean, /tmp/rtm_scratch/ChildrenCDEF.lean, /tmp/rtm_scratch/ChildrenAB.lean, /tmp/rtm_scratch/Full.lean (with #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Metrizable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/LinearAlgebra/Dimension/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Order/LeftRightNhds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-rectifiable-of-tangent-measure-a1/parent-child-handoff.json`
- `/tmp/rtm_scratch/Challenge.lean`
- `/tmp/rtm_scratch/Assembly.lean`
- `/tmp/rtm_scratch/Full.lean`

Snapshot: project d09bc8a (Contract.lean identical to the workspace copy), Mathlib 25730c7c, pinned simongmt. Found and used: SimonGMT Chapter03 CountablyRectifiable, countablyRectifiable_iUnion, countablyRectifiable_range, blowUpMap, regular_euclideanHausdorffMeasure_restrict_submodule and support_euclideanHausdorffMeasure_restrict_submodule (plane measure Hⁿ⌞P is regular with support P when finrank P = n); Mathlib LipschitzOnWith.extend_finite_dimension (Lipschitz extension into finite-dimensional targets, replacing Simon Ch. 2 Thm 1.2), Measure.countable_meas_pos_of_disjoint_iUnion with sigmaFinite_of_locallyFinite (countable atoms), isSigmaCompact_range (Borel measurability of Lipschitz images), Measure.nullSingletonClass_hausdorff (no atoms for n ≥ 1), Submodule.norm_starProjection_apply_le / starProjection_eq_self_iff, IsSeparable.exists_countable_dense_subset, exists_linearIndependent_of_le_finrank, Antitone.measure_iInter, tendsto_measure_iInter_atTop, infDist_lt_iff, integral_pos_iff_support_of_nonneg, integral_mono_of_nonneg. No match: Mathlib has no IsSigmaCompact.measurableSet (σ-compact sets are handled by unfolding into a countable union of compacts), no countable rectifiability, and no Kirszbraun theorem (not needed: componentwise/finite-dimensional extension suffices); SimonGMT has no approximate-tangent-measure (HasApproxTangentPlaneWithMultiplicity) results. The six child propositions pass the verifier's statement validator and elaborate in the comparator's replayed contract scope; with the children as sorry stubs the parent glue compiles; and complete proofs of all six children plus the parent compile sorry-free using only propext, Classical.choice and Quot.sound. No proposed name is used elsewhere in the active DAG or the libraries.
