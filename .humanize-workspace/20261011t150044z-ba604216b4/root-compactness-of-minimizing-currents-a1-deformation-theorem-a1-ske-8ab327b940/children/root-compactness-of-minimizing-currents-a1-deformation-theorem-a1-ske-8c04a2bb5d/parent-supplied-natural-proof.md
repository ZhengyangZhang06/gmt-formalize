# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_deformation-a1.good_radius-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_deformation-a1.good_radius-a1.slice_liminf-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1–3 of the parent's supplied proof of cmcsd_good_radius, for one finite measure. The argument never uses the structure of ℝ^P, so it is stated for an arbitrary measurable space α; the parent applies it with α = ℝ^P (Euclid P), once to μ and once to μ'. The book source is Simon, Introduction to GMT, Ch. 6. The remark after 4.9 (book/chapter-06.txt lines 1361–1375) says t ↦ M_W(T⌞{f < t}) is increasing, hence differentiable L¹-a.e., and slice masses are controlled by liminf_{h↓0} h⁻¹·M(T⌞{t − h < f < t}). The proof of 5.1, (8)–(10) (lines 1725–1734) uses this to choose the slicing radius. Throughout, ofReal := ENNReal.ofReal, A_s := {x ∈ α : f(x) < s} for s ∈ ℝ, and F(s) := (μ(A_s)).toReal. So F is exactly the function fun s : ℝ => (μ {x | f x < s}).toReal of the statement, and the hypothesis says F is differentiable at t.

1. (Finite values of the distribution function.) For each s ∈ ℝ the set A_s is measurable, because f and the constant s are measurable (measurableSet_lt hf measurable_const). Since μ is a finite measure, μ(A_s) ≠ ∞ (measure_ne_top). Hence μ(A_s) = ofReal(F(s)) (ENNReal.ofReal_toReal) and F(s) ≥ 0 (ENNReal.toReal_nonneg).

2. (Slice bound.) Fix h > 0. Since t − h < t, A_{t−h} ⊆ A_t. If t − h < f(x) < t, then x ∈ A_t and x ∉ A_{t−h}, because f(x) < t − h would contradict t − h < f(x). Hence {x : t − h < f(x) < t} ⊆ A_t \ A_{t−h}. Apply monotonicity of μ (measure_mono) and measure_sdiff. The latter applies because A_{t−h} ⊆ A_t, A_{t−h} is measurable (hence null-measurable), and μ(A_{t−h}) ≠ ∞. This gives
   μ({t − h < f < t}) ≤ μ(A_t \ A_{t−h}) = μ(A_t) − μ(A_{t−h}) = ofReal(F(t)) − ofReal(F(t − h)) = ofReal(F(t) − F(t − h)).
   The last two equalities use step 1 and ENNReal.ofReal_sub, which is valid because F(t − h) ≥ 0. Multiplying both sides by ofReal(h⁻¹) preserves the inequality in [0, ∞] (monotonicity of multiplication, e.g. gcongr). So for every h > 0,
   ofReal(h⁻¹)·μ({t − h < f < t}) ≤ ofReal(h⁻¹)·ofReal(F(t) − F(t − h)).

3. (Comparison of the liminfs.) The set (0, ∞) belongs to the filter 𝓝[>] 0 (self_mem_nhdsWithin), so the inequality of step 2 holds eventually along 𝓝[>] 0. In the complete lattice [0, ∞], liminf is monotone under eventual inequality, with no boundedness side conditions (Filter.liminf_le_liminf; its boundedness arguments are discharged automatically in a complete lattice). Hence
   liminf_{h→0+} ofReal(h⁻¹)·μ({t − h < f < t}) ≤ liminf_{h→0+} ofReal(h⁻¹)·ofReal(F(t) − F(t − h)).

4. (Left slopes at a point of differentiability.) F is differentiable at t by hypothesis. The sibling cbr_smm_liminf_left_slope_le_deriv, applied to F and t, gives
   liminf_{h→0+} ofReal(h⁻¹)·ofReal(F(t) − F(t − h)) ≤ ofReal(deriv F t).
   This is step 3 of the parent's proof: the left quotients h⁻¹(F(t) − F(t − h)) tend to F′(t) as h ↓ 0, and for h > 0 the product equals ofReal(h⁻¹(F(t) − F(t − h))), which tends to ofReal(F′(t)).

5. (Conclusion.) Chaining steps 3 and 4 gives liminf_{h→0+} ofReal(h⁻¹)·μ({x : t − h < f(x) < t}) ≤ ofReal(deriv F t). This is the claim, because F is literally fun s : ℝ => (μ {x | f x < s}).toReal. ∎

## Key steps

1. A_s := {f < s} is measurable and μ(A_s) = ofReal(F(s)) with F(s) = (μ A_s).toReal ≥ 0 (finite measure).
2. For h > 0: {t − h < f < t} ⊆ A_t \ A_{t−h}, so μ({t − h < f < t}) ≤ μ(A_t) − μ(A_{t−h}) = ofReal(F(t) − F(t − h)) (measure_sdiff, ENNReal.ofReal_sub); multiply by ofReal(h⁻¹).
3. The bound holds eventually along 𝓝[>] 0, so the liminfs compare (Filter.liminf_le_liminf in [0, ∞]).
4. The sibling cbr_smm_liminf_left_slope_le_deriv bounds liminf ofReal(h⁻¹)·ofReal(F(t) − F(t − h)) by ofReal(deriv F t).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (local-project; project b4d606db1, mathlib 25730c7c); cmp snapshot project/GMT/Ch07/Contract.lean with workspace GMT/Ch07/Contract.lean and Submission.lean (identical); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n 'theorem Monotone.ae_differentiableAt|theorem measurable_deriv |theorem Measurable.ennreal_ofReal|theorem lintegral_eq_zero_iff |theorem mul_meas_ge_le_lintegral₀|theorem volume_Ioo|theorem nonempty_of_measure_ne_zero|theorem mul_top |theorem restrict_apply. |theorem measure_mono_null |theorem measure_union_null |theorem ae_iff |theorem lintegral_strict_mono ' mathlib/Mathlib`
- `rg -n 'measure_diff\b|measure_sdiff|measure_sdiff_null|liminf_le_liminf|Tendsto.liminf_eq|tendsto_slope_zero_left' mathlib/Mathlib (measure_diff is a deprecated alias of measure_sdiff since 2026-06-03)`
- `rg -n 'le_inv_iff_mul_le|ofReal_inv_of_pos|mul_le_mul_iff_right|ofReal_le_ofReal_iff' mathlib/Mathlib/Basic/ENNReal`
- `rg -n 'theorem Monotone.ae_hasDerivAt|theorem le_rightLim|theorem rightLim_le|theorem tendsto_leftLim|theorem measure_Ioo|theorem withDensity_apply_le|theorem withDensity_rnDeriv_le' mathlib/Mathlib`
- `python3 -I scan of runs/20261011T150044Z-ba604216b4/dag.json (1613 nodes): statements mentioning deriv F, Monotone or ofReal h⁻¹; lean_name and theorems collisions for cmcsd_gr_liminf_slice_le_deriv, cmcsd_gr_exists_deriv_le_off_null and the cmcsd_gr prefix (none); status and lean_statement identity of cmcs_smi_lintegral_ofReal_deriv_le and cbr_smm_liminf_left_slope_le_deriv (accepted, identical)`
- `grep -rl cmcsd_gr_ over the run directory, the snapshot project and mathlib, and lake-packages-25730c7c/simongmt/Poincare (no match)`
- `git show 6efe397f182ee5f93e5be9c4b09eb298c3f56ad8:GMT/Ch07/Submission.lean and git show 9e4623f7949b6e8a31421369c9b6bcbc190d2c41:GMT/Ch07/Submission.lean (accepted proofs of the two reused declarations, recompiled verbatim)`
- `python3 -I verifier/lean_contract.py validate_lean_statement and verifier/gmt-compare.py contract_scope/child_modules on all child types and the selected type`
- `lean GMT/Scratch/cmcsd_good_radius_decomposition/{Types,AssemblyAx,FullCheck,ComparatorStyle,InstCheck,SpecStub,SpecStubOldEuclid}.lean with the pinned LEAN_PATH`
- `sed -n 2782,2830p /runtime/flows/gmt-claude-0135a42af877/_recursive_lean/runtime.py (_install_speculative_assumptions stub layout)`
- `grep -n and sed -n 1340,1380p and 1651,1740p book/chapter-06.txt (Simon 4.9–4.10; proof of 5.1 (8)–(10))`
- `WebSearch: Lebesgue theorem monotone function differentiable a.e., integral of derivative at most f(b) - f(a); Markov inequality, measure-theoretic form`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Stieltjes.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/LeftRightLim.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-8ab327b940/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-9a64d46574/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-201a40b18c/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-slicing-a1-mass-integral-a-f8cc50fd1b/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-0135a42af877/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcsd_good_radius_decomposition/AssemblyAx.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcsd_good_radius_decomposition/FullCheck.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcsd_good_radius_decomposition/ComparatorStyle.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcsd_good_radius_decomposition/SpecStub.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcsd_good_radius_decomposition/draft_subproblems.json`

The snapshot contract (project b4d606db1, Mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean.

No snapshot or project declaration proves the selected statement or either new lemma. In the DAG, cbrld_radius_liminf_annulus_le_of_hasDerivAt covers only f = dist(·, x₁), cbr_smm_strip_distribution_function needs a continuous f, and cbrld_exists_good_slice_radius is specific to balls.

Two accepted declarations are reused with byte-identical frozen types. cmcs_smi_lintegral_ofReal_deriv_le (commit 6efe397f1) is Lebesgue's inequality. cbr_smm_liminf_left_slope_le_deriv (commit 9e4623f79) gives left slopes at a point of differentiability. Their accepted proofs recompile here with propext, Classical.choice and Quot.sound only.

Every Mathlib lemma the child proofs cite exists in the frozen import closure. This includes Monotone.ae_differentiableAt, measurable_deriv, mul_meas_ge_le_lintegral₀, lintegral_eq_zero_iff, Real.volume_Ioo, measure_sdiff (measure_diff is now a deprecated alias), measure_sdiff_null, nonempty_of_measure_ne_zero, ENNReal.mul_le_mul_iff_right, ENNReal.le_inv_iff_mul_le and ENNReal.ofReal_inv_of_pos.

The new names cmcsd_gr_liminf_slice_le_deriv and cmcsd_gr_exists_deriv_le_off_null do not occur anywhere. Both new children are fully proved without helpers or imports, and together they imply the selected frozen type. Both new child types are free of Euclid, so they also elaborate in the flow's speculative stub; the Euclid form does not. Book anchors: chapter-06.txt lines 1361–1375 (4.9–4.10) and 1725–1734 (5.1 (8)–(10)).
