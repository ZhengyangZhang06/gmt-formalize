# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.cube_bv_median-a1.integer_median-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.cube_bv_median-a1.integer_median-a1.median_minimizes-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the parent proof, the minimality of the median β. In the case c ≥ β it compares pointwise on {u ≤ β} and {u > β}, giving ∫|u − c| − ∫|u − β| ≥ (c − β)(μ{u ≤ β} − μ{u > β}) ≥ 0. In the case c < β it uses {u ≥ β} and {u < β}. Here it is stated for an arbitrary probability measure and any real β with the two half-measure properties. This minimizing property replaces the median hypothesis 2.7(‡) of Simon Ch. 2. Since μ{u > β} = 1 − μ{u ≤ β} for the null-measurable set {u ≤ β}, the parent's lower bound equals (c − β)(2μ{u ≤ β} − 1); the indicator formulation below computes exactly this. No density is assumed: this is the calculus-free pointwise comparison.

Notation. μ(A) := μ.real A for A ⊆ X, and 1_s denotes the indicator of s (value 1 on s, 0 off s). Fix c ∈ ℝ.

1. Integrability. For every a ∈ ℝ, x ↦ |u(x) − a| is μ-integrable. Indeed u is integrable, the constant a is integrable because μ is finite (integrable_const), and differences and absolute values of integrable functions are integrable (Integrable.sub, Integrable.abs).
2. Null-measurability. u is integrable, hence μ-a.e.-measurable (Integrable.aemeasurable). So {u ≤ β} = u⁻¹((−∞, β]) and {β ≤ u} = u⁻¹([β, ∞)) are μ-null-measurable (AEMeasurable.nullMeasurableSet_preimage with measurableSet_Iic, measurableSet_Ici).
3. Indicator integrals. Let s be μ-null-measurable.
   - 1_s is integrable (Integrable.indicator₀ applied to the constant 1, which is integrable since μ is finite).
   - ∫ 1_s dμ = ∫_s 1 dμ = μ(s) (integral_indicator₀, setIntegral_const).
   - ∫ 1 dμ = μ(X) = 1 (integral_const, probReal_univ).
4. Key lemma. Let s be μ-null-measurable with μ(s) ≥ 1/2, and let d ≥ 0. Assume d·(2·1_s(x) − 1) ≤ |u(x) − c| − |u(x) − β| for all x ∈ X.
   - Both sides are integrable (steps 1 and 3).
   - By monotonicity of the integral (integral_mono) and linearity (integral_const_mul, integral_sub), together with step 3: d·(2μ(s) − 1) = ∫ d·(2·1_s − 1) dμ ≤ ∫ (|u − c| − |u − β|) dμ = ∫|u − c| dμ − ∫|u − β| dμ.
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
- `cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean RUN/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean (identical); git rev-parse HEAD (b4d606db1da5da8fa2c0292ad4924d97de8b3c4b); git -C RUN/local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d = manifest.json mathlib_commit = lake-manifest inputRev)`
- `rg -n "theorem (volume_preserving_ofLp|volume_pi_Ioo|tendsto_measure_iInter_atTop|tendsto_measure_iUnion_atTop|probReal_compl_eq_one_sub₀|probReal_compl_eq_one_sub|measureReal_compl₀|measureReal_compl|mul_meas_ge_le_integral_of_nonneg|integral_indicator₀|integral_indicator_one|exists_least_of_bdd|measureReal_mono|measureReal_univ_eq_one|probReal_univ)\b" -A4 SNAPSHOT/mathlib/Mathlib`
- `rg -n "volume_preserving_ofLp|theorem integral_indicator₀|probReal_compl_eq_one_sub|probReal_univ|integrable_indicator_iff₀|IntegrableOn.integrable_indicator₀|Integrable.indicator₀" SNAPSHOT/mathlib/Mathlib; rg -n "CoeFun" SNAPSHOT/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `rg -n "theorem indicator_of_notMem|neg_le_abs|theorem lt_mem_nhds|theorem gt_mem_nhds|theorem setIntegral_const\b|theorem integral_const\b|theorem integral_const_mul\b|abs_sub_le" SNAPSHOT/mathlib/Mathlib`
- `rg -n -i -l median SNAPSHOT/mathlib/Mathlib -g '*.lean' (only LinearAlgebra/AffineSpace/Simplex/Centroid.lean, unrelated); rg -n -i median SNAPSHOT/project -g '*.lean' (no match)`
- `rg -n dimred_mbl_dt_cbm_im GMT SNAPSHOT/project lake-packages-25730c7c/simongmt -g '*.lean' (no match); grep -c dimred_mbl_dt_cbm_im RUN/issue-workers.json (0)`
- `python3 scan of RUN/dag.json (2092 nodes, 3344 reserved identifiers): 'dimred_mbl_dt_cbm_im' occurs 0 times; exact lean_statement matches: cmcdtfrfg_cube_volume (accepted, candidate_commit a104b3873f3c…, PR #7250) and twin cmcdt_cbm_im_{cube_volume, integer_median_exists, median_minimizes, median_abs_le} (rlcr-lean/decomposing, unaccepted); 951 existing cross-branch child references to accepted nodes`
- `git show a104b3873f3c979b07a45e8d97d3d4d1d84c106a:GMT/Ch07/Submission.lean | grep -n cmcdtfrfg_cube_volume (line 458, identical type); git show --stat a104b3873f3c`
- `sed -n on /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py: _decompose (node.depth >= max_depth disables splitting), _existing_lean_name_problem, _accepted_checkpoint, _solve_children (accepted-name reuse with identical type)`
- `python3 -I /tmp/dmdt-cbm-im-gG3zEg/scripts/emit.py (verifier/gmt-compare.py contract_scope/child_modules + both validate_lean_statement; all five types unchanged); lake env lean /tmp/dmdt-cbm-im-gG3zEg/chal/Challenge_{parent,cube_volume,integer_median_exists,median_minimizes,median_abs_le}.lean (only 'declaration uses sorry')`
- `lake env lean /tmp/dmdt-cbm-im-gG3zEg/lean/Final.lean (four child types fully proved; HumanizeNodeComparator.assembly proves the exact parent type from the four child types as hypotheses; #print axioms: [propext, Classical.choice, Quot.sound] for all six)`
- `lake env lean /tmp/dmdt-cbm-im-gG3zEg/lean/Inspect.lean (pp.numericTypes shows (1 / 2 : ℝ); MeasureTheory.Measure; volume on Euclid k = measureSpaceOfInnerProductSpace by rfl)`
- `python3 of twin nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-4adef27685/{decomposition-v1,decomposition-audit-v1,decomposition-review-receipt-v1,decomposition-scope-v1}.json (audited four-child split of the identical frozen type, acceptable: true)`
- `sed -n 1872,1912p book/chapter-06.txt (Simon Ch. 6, 5.1, displays (31) and (35))`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Int/LeastGreatest.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/AffineSpace/Simplex/Centroid.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-5a243b38c6/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-5a243b38c6/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-5a243b38c6/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-4adef27685/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-4adef27685/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-4adef27685/decomposition-review-receipt-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-4adef27685/decomposition-scope-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-4adef27685/parent-supplied-natural-proof.md`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/dmdt-cbm-im-gG3zEg/scripts/emit.py`
- `/tmp/dmdt-cbm-im-gG3zEg/scripts/items.json`
- `/tmp/dmdt-cbm-im-gG3zEg/chal/Challenge_parent.lean`
- `/tmp/dmdt-cbm-im-gG3zEg/chal/Challenge_cube_volume.lean`
- `/tmp/dmdt-cbm-im-gG3zEg/chal/Challenge_integer_median_exists.lean`
- `/tmp/dmdt-cbm-im-gG3zEg/chal/Challenge_median_minimizes.lean`
- `/tmp/dmdt-cbm-im-gG3zEg/chal/Challenge_median_abs_le.lean`
- `/tmp/dmdt-cbm-im-gG3zEg/lean/Children.lean`
- `/tmp/dmdt-cbm-im-gG3zEg/lean/Final.lean`
- `/tmp/dmdt-cbm-im-gG3zEg/lean/Inspect.lean`

Pins match: project b4d606db and Mathlib 25730c7c; Submission.lean is byte-identical to the frozen contract and to the snapshot contract. Neither the snapshot project, Mathlib nor SimonGMT contains an integer-median, median-minimality or median-bound lemma; Mathlib's only 'median' hit is the unrelated simplex Centroid file. All the Mathlib ingredients exist under the bare GMT.Ch07.Submission import: PiLp.volume_preserving_ofLp, Real.volume_pi_Ioo, tendsto_measure_iUnion_atTop/iInter_atTop, probReal_compl_eq_one_sub₀, measureReal_mono, Int.exists_least_of_bdd, Integrable.indicator₀, integral_indicator₀, setIntegral_const, integral_const, mul_meas_ge_le_integral_of_nonneg, lt_mem_nhds/gt_mem_nhds, abs_sub_le and neg_le_abs. The cube-volume child exactly matches the accepted declaration cmcdtfrfg_cube_volume (candidate a104b387, identical type at line 458), which the runtime allows to be reused. The three median children get fresh names, because the identically typed twin children cmcdt_cbm_im_* are unaccepted and owned by another parent. All five types elaborate in exact comparator form and pass both validators. All four children are fully proved, and an assembly proves the exact parent type from the four child types, using only propext, Classical.choice and Quot.sound.
