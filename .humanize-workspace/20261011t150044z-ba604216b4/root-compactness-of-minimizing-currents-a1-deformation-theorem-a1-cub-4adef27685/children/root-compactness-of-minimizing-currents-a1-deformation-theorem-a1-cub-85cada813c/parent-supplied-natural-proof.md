# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.integer_median-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.integer_median-a1.median_minimizes-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the parent proof, the minimality of the median β. This minimizing property is what replaces the median hypothesis of Simon Ch. 2, 2.7. It is the classical fact that a median minimizes c ↦ E|u − c|; the pointwise comparison argument of the parent is used.

Notation. μ(A) := μ.real A for A ⊆ X; 1_s denotes the indicator of s (value 1 on s, 0 off s). Fix c ∈ ℝ.

1. Integrability. For every a ∈ ℝ, x ↦ |u(x) − a| is μ-integrable. Indeed u is integrable, the constant a is integrable because μ is finite (integrable_const), and differences and absolute values of integrable functions are integrable (Integrable.sub, Integrable.abs).
2. Null-measurability. u is integrable, hence μ-a.e.-measurable (Integrable.aemeasurable). So the sets {u ≤ β} = u⁻¹((−∞, β]) and {β ≤ u} = u⁻¹([β, ∞)) are μ-null-measurable (AEMeasurable.nullMeasurableSet_preimage with measurableSet_Iic, measurableSet_Ici).
3. Indicator integrals. Let s be μ-null-measurable.
   - 1_s is integrable: apply IntegrableOn.integrable_indicator₀ to the constant 1, which is integrable on the finite measure μ.
   - ∫ 1_s dμ = ∫_s 1 dμ = μ(s) (integral_indicator₀, setIntegral_const).
   - ∫ 1 dμ = μ(X) = 1 (integral_const, probReal_univ).
4. Key lemma. Let s be μ-null-measurable with μ(s) ≥ 1/2, let d ≥ 0, and assume the pointwise bound d·(2·1_s(x) − 1) ≤ |u(x) − c| − |u(x) − β| for all x ∈ X.
   - Both sides are integrable (steps 1 and 3).
   - By monotonicity (integral_mono) and linearity (integral_sub, integral_const_mul) of the integral, together with step 3: d·(2μ(s) − 1) = ∫ d·(2·1_s − 1) dμ ≤ ∫ (|u − c| − |u − β|) dμ = ∫|u − c| dμ − ∫|u − β| dμ.
   - Since d ≥ 0 and 2μ(s) − 1 ≥ 0, the left side is ≥ 0. Hence ∫|u − β| dμ ≤ ∫|u − c| dμ.
5. Case c ≥ β. Apply step 4 with s := {u ≤ β} and d := c − β ≥ 0. Here s is null-measurable by step 2 and μ(s) ≥ 1/2 by hypothesis. Pointwise check:
   (a) If u(x) ≤ β, then u(x) ≤ β ≤ c, so |u(x) − c| = c − u(x) and |u(x) − β| = β − u(x). Hence |u(x) − c| − |u(x) − β| = c − β = d·(2·1 − 1).
   (b) If u(x) > β, then 1_s(x) = 0. By the triangle inequality (abs_sub_le), |u(x) − β| ≤ |u(x) − c| + |c − β| = |u(x) − c| + (c − β). So |u(x) − c| − |u(x) − β| ≥ −(c − β) = d·(2·0 − 1).
6. Case c < β. Apply step 4 with s := {β ≤ u} and d := β − c > 0. Here s is null-measurable by step 2 and μ(s) ≥ 1/2 by hypothesis. Pointwise check:
   (a) If β ≤ u(x), then c < β ≤ u(x), so |u(x) − c| = u(x) − c and |u(x) − β| = u(x) − β. Hence |u(x) − c| − |u(x) − β| = β − c = d·(2·1 − 1).
   (b) If u(x) < β, then 1_s(x) = 0. By the triangle inequality, |u(x) − β| ≤ |u(x) − c| + |c − β| = |u(x) − c| + (β − c). So |u(x) − c| − |u(x) − β| ≥ −(β − c) = d·(2·0 − 1).
7. Steps 5 and 6 cover every c ∈ ℝ, so ∫|u − β| dμ ≤ ∫|u − c| dμ for all c. ∎

## Key steps

1. Every |u − a| is integrable, and so are the indicators of the null-measurable sets {u ≤ β} and {β ≤ u}; ∫1_s dμ = μ(s) and ∫1 dμ = 1.
2. Key lemma: if d ≥ 0, μ(s) ≥ 1/2 and d(2·1_s − 1) ≤ |u − c| − |u − β| pointwise, then integrating gives ∫|u − c| − ∫|u − β| ≥ d(2μ(s) − 1) ≥ 0.
3. Case c ≥ β: take s = {u ≤ β}, d = c − β; on s the difference equals c − β, and off s the triangle inequality gives ≥ −(c − β).
4. Case c < β: take s = {β ≤ u}, d = β − c; on s the difference equals β − c, and off s the triangle inequality gives ≥ −(β − c).

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
