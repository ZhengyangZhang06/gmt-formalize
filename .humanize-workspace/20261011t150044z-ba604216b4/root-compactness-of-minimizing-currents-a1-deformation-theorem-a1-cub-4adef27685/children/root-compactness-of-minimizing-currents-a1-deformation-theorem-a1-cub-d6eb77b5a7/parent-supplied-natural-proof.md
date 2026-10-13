# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.integer_median-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.integer_median-a1.median_abs_le-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent proof, i.e. the bound (35) |β_F| ≤ 2∫_F |F| dLⁿ in Simon's proof of Ch. 6, 5.1 (book/chapter-06.txt lines 1906–1908). Simon deduces it from the median choice (31). The parent's case β = 0 is absorbed into case (a) below.

Notation. μ(A) := μ.real A for A ⊆ X.

1. Markov's inequality. |u| is nonnegative and μ-integrable (Integrable.abs). With ε := |β| ≥ 0, we have ε·μ{x : ε ≤ |u(x)|} ≤ ∫|u| dμ (mul_meas_ge_le_integral_of_nonneg). Mathematically:
   - ε·1_{ε ≤ |u|} ≤ |u| pointwise because ε ≥ 0;
   - the set {ε ≤ |u|} is μ-null-measurable because u is a.e.-measurable;
   - integrating the pointwise bound gives the inequality.
2. Claim: μ{x : |β| ≤ |u(x)|} ≥ 1/2. Since μ is finite, μ is monotone under inclusion (measureReal_mono).
   (a) If β ≥ 0: for every x with β ≤ u(x), |β| = β ≤ u(x) ≤ |u(x)|. Hence {β ≤ u} ⊆ {|β| ≤ |u|}, and μ{|β| ≤ |u|} ≥ μ{β ≤ u} ≥ 1/2 by hypothesis.
   (b) If β < 0: for every x with u(x) ≤ β, |β| = −β ≤ −u(x) ≤ |u(x)|. Hence {u ≤ β} ⊆ {|β| ≤ |u|}, and μ{|β| ≤ |u|} ≥ μ{u ≤ β} ≥ 1/2 by hypothesis.
3. By steps 1 and 2 and |β| ≥ 0, |β|·(1/2) ≤ |β|·μ{|β| ≤ |u|} ≤ ∫|u| dμ. Multiplying by 2 gives |β| ≤ 2∫|u| dμ. ∎

## Key steps

1. Markov's inequality for |u| at level |β|: |β|·μ{|β| ≤ |u|} ≤ ∫|u| dμ.
2. If β ≥ 0 then {β ≤ u} ⊆ {|β| ≤ |u|}; if β < 0 then {u ≤ β} ⊆ {|β| ≤ |u|}. Either way μ{|β| ≤ |u|} ≥ 1/2.
3. Hence |β|/2 ≤ ∫|u| dμ, i.e. |β| ≤ 2∫|u| dμ.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d, matches manifest.json and lake-manifest.json)`
- `python3 scan of runs/20261011T150044Z-ba604216b4/dag.json (1594 nodes): lean_statement search for '0 < y i ∧ y i < 1', 'volume {...} = 1', 'volume (Set.pi', 'volume.restrict', 'IsProbabilityMeasure', 'IsFiniteMeasure' and statement search for 'median'; collected all 1598 reserved lean_name/theorems identifiers and filtered for 'cmcdt_cbm', 'median', 'cube_volume', 'unit_cube'`
- `grep -c cmcdt_cbm_im dag.json issue-workers.json (0 and 0); git log --all --oneline -S cmcdt_cbm_im (no match)`
- `rg -n 'cmcdt_cbm_im|cube_volume|integer_median_exists|median_minimizes|median_abs_le' local-references/123e8435b4a2469b/project local-references/123e8435b4a2469b/mathlib/Mathlib lake-packages-25730c7c/simongmt -g '*.lean' (no match)`
- `rg -n 'theorem (volume_preserving_measurableEquiv|volume_preserving_symm_measurableEquiv_toLp|volume_preserving_ofLp|volume_preserving_toLp)' mathlib/Mathlib; rg -n 'volume_preserving' mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `rg -n 'theorem volume_pi_Ioo\b|theorem volume_pi_Ioo_toReal|theorem volume_Ioo\b' mathlib/Mathlib`
- `rg -n 'theorem (measureReal_mono|measureReal_compl₀|measureReal_add_measureReal_compl₀|measureReal_add_measureReal_compl|tendsto_measureReal_iUnion_atTop|tendsto_measureReal_iInter_atTop|probReal_compl_eq_one_sub₀|measureReal_univ_eq_one|probReal_le_one)\b' Mathlib; rg -n 'theorem measureReal_compl|theorem probReal_compl|lemma probReal_compl|theorem prob_compl' Mathlib`
- `rg -n 'theorem (Integrable\.indicator₀|integrable_indicator_iff₀|IntegrableOn\.integrable_indicator₀|integrable_indicator_iff)\b' Mathlib; rg -n 'theorem integral_const\b|theorem integral_const_mul\b|theorem integral_mul_left\b|theorem integral_mul_const\b' Mathlib`
- `lake env lean /tmp/im-decomp/Names.lean (#check of Measure.real, measureReal_def, integral_indicator_one, mul_meas_ge_le_integral_of_nonneg, Int.exists_least_of_bdd, Monotone.measure_iUnion, tendsto_measure_iUnion_atTop, tendsto_measure_iInter_atTop, prob_compl_eq_one_sub₀, measureReal_compl, probReal_compl_eq_one_sub, PiLp.volume_preserving_ofLp, PiLp.volume_preserving_toLp, Real.volume_pi_Ioo, isProbabilityMeasure_iff, Measure.restrict_apply_univ, Integrable.aemeasurable, AEMeasurable.nullMeasurableSet_preimage, nullMeasurableSet_le, measure_compl₀, integral_mono, integral_sub, integral_indicator₀, Integrable.abs, setIntegral_const after import GMT.Ch07.Submission; measure_iUnion_eq_iSup and Measure.real_apply do not exist)`
- `lake env lean /tmp/im-decomp/Children.lean (the four exact child types proved; the frozen parent type proved from them)`
- `lake env lean /tmp/im-decomp/AxiomsCheck.lean (#print axioms for the four children and the parent: propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/im-decomp/PPCheck.lean (pp.numericTypes shows (1 / 2 : ℝ) in the child types; volume on Euclid k is measureSpaceOfInnerProductSpace.volume by rfl)`
- `git show 64f176020a955d00c93754cd060d8de53ac5e331:GMT/Ch07/Submission.lean (accepted children are declared as theorem Submission.X inside namespace GMT.Ch07 after the contract section)`
- `sed -n 1870,1915p book/chapter-06.txt (Simon (31): β_F with min{Lⁿ{F ≥ β}, Lⁿ{F ≤ β}} ≥ 1/2, β_F ∈ ℤ for integer-valued F; (35): |β_F| ≤ 2∫|F| dLⁿ)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-4adef27685/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-4adef27685/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/im-decomp/Names.lean`
- `/tmp/im-decomp/Children.lean`
- `/tmp/im-decomp/AxiomsCheck.lean`
- `/tmp/im-decomp/PPCheck.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) has the same contract as the workspace Contract.lean and Submission.lean.

No reusable declaration exists:
- No project, SimonGMT or Mathlib file has an integer-median, median-L¹ or median-bound lemma.
- No accepted DAG node has the exact type `∀ k : ℕ, volume {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} = 1`. That fact appears only as a conjunct of the still-decomposing cmcdtfr_face_geometry.
- None of the four proposed cmcdt_cbm_im_* names occurs in the DAG, issue-workers, git history or the snapshot.

Mathlib within the import closure of GMT.Ch07.Submission supplies every tool the child proofs cite, so no extra imports are needed:
- PiLp.volume_preserving_ofLp, Real.volume_pi_Ioo, MeasurableSet.univ_pi;
- tendsto_measure_iUnion_atTop, tendsto_measure_iInter_atTop, ENNReal.tendsto_toReal;
- AEMeasurable.nullMeasurableSet_preimage, probReal_compl_eq_one_sub₀, measureReal_mono;
- Int.exists_least_of_bdd;
- IntegrableOn.integrable_indicator₀, integral_indicator₀, setIntegral_const, integral_const, integral_mono, integral_sub, integral_const_mul;
- abs_sub_le, mul_meas_ge_le_integral_of_nonneg.

All four children were proved in Lean with these lemmas. The frozen parent type was derived from the four exact child types using only propext, Classical.choice and Quot.sound.

Lean notes for this Mathlib pin: Set.mem_setOf_eq is deprecated in favour of Set.mem_ofPred_eq; use le_or_gt rather than le_or_lt and indicator_of_notMem rather than indicator_of_not_mem; push_neg is deprecated.
