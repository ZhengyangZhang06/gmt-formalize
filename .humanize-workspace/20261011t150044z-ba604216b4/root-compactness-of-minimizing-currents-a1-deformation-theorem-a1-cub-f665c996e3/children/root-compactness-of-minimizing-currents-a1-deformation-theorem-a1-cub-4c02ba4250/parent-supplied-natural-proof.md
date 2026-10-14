# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_approx-a1.mollify_l1-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_approx-a1.mollify_l1-a1.l1_contraction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 (L¹ contraction) of the supplied proof of the parent cmcdt_cbm_sa_mollify_l1. The argument is copied from there, with details filled in. The parent states this step for continuous k, but the argument never uses continuity, so that hypothesis is dropped. This is Young's convolution inequality ‖k ⋆ g‖₁ ≤ ‖k‖₁ ‖g‖₁ for a probability density k.

Notation. ℝⁿ := Euclid n = EuclideanSpace ℝ (Fin n) with Lebesgue measure (volume). For a ∈ ℝ, ‖a‖ₑ = ofReal|a| ∈ [0, ∞] is the extended norm. ∫⁻ is the [0, ∞]-valued Lebesgue integral and ∫ the Bochner integral. (k ⋆ g)(x) := ∫ k(t) g(x − t) dt is Mathlib's `convolution k g (ContinuousLinearMap.lsmul ℝ ℝ) volume x` (convolution_def; lsmul ℝ ℝ a b = a • b = a · b). Every lemma cited below is in the import closure of the frozen GMT/Ch07/Submission.lean, so no extra import is needed.

Assume k(z) ≥ 0 for all z, ∫ k = 1, and g is a.e.-strongly measurable.

1. k is integrable. By definition the Bochner integral of a non-integrable function is 0, while ∫ k = 1 ≠ 0. So k is integrable (integrable_of_integral_eq_one). In particular k is a.e.-strongly measurable, and t ↦ ‖k(t)‖ₑ is a.e.-measurable (AEStronglyMeasurable.enorm).

2. ∫⁻ ‖k(t)‖ₑ dt = 1. Since k ≥ 0, ‖k(t)‖ₑ = ofReal(k(t)) for every t (Real.enorm_eq_ofReal). By ofReal_integral_eq_lintegral_ofReal (k is integrable and 0 ≤ k everywhere, hence a.e.), ∫⁻ ofReal(k(t)) dt = ofReal(∫ k) = ofReal(1) = 1.

3. Pointwise bound. Fix x ∈ ℝⁿ. By convolution_def, (k ⋆ g)(x) = ∫ k(t) · g(x − t) dt. For every function φ : ℝⁿ → ℝ we have ‖∫ φ‖ₑ ≤ ∫⁻ ‖φ‖ₑ (enorm_integral_le_lintegral_enorm). This needs no integrability: if φ is not integrable, the left side is ‖0‖ₑ = 0. Since ‖k(t) · g(x − t)‖ₑ = ‖k(t)‖ₑ · ‖g(x − t)‖ₑ (enorm_mul), we get
   ‖(k ⋆ g)(x)‖ₑ ≤ ∫⁻ ‖k(t)‖ₑ · ‖g(x − t)‖ₑ dt.

4. Joint measurability. Put F(x, t) := ‖k(t)‖ₑ · ‖g(x − t)‖ₑ. Apply AEStronglyMeasurable.convolution_integrand to k (a.e.-strongly measurable by step 1) and g, with L = lsmul ℝ ℝ and μ = ν = volume. Its instance requirements hold: volume on ℝⁿ is s-finite and right invariant, and addition and negation are measurable. So (x, t) ↦ k(t) · g(x − t) is a.e.-strongly measurable for volume.prod volume. Taking extended norms (AEStronglyMeasurable.enorm) and rewriting with enorm_mul, the function uncurry F is a.e.-measurable for volume.prod volume.

5. Conclusion.
   ∫⁻_x ‖(k ⋆ g)(x)‖ₑ
   ≤ ∫⁻_x ∫⁻_t F(x, t)   (step 3 and lintegral_mono)
   = ∫⁻_t ∫⁻_x F(x, t)   (Tonelli, lintegral_lintegral_swap, using step 4)
   = ∫⁻_t ‖k(t)‖ₑ · ∫⁻_x ‖g(x − t)‖ₑ   (lintegral_const_mul', since ‖k(t)‖ₑ ≠ ∞)
   = ∫⁻_t ‖k(t)‖ₑ · ∫⁻_x ‖g(x)‖ₑ   (translation invariance of Lebesgue measure, lintegral_sub_right_eq_self)
   = (∫⁻_t ‖k(t)‖ₑ) · ∫⁻_x ‖g(x)‖ₑ   (lintegral_mul_const''; t ↦ ‖k(t)‖ₑ is a.e.-measurable by step 1, and ∫⁻ ‖g‖ₑ may be ∞)
   = ∫⁻_x ‖g(x)‖ₑ   (step 2). ∎

The case n = 0 needs no separate treatment.

Formalization note: a complete Lean proof of the exact frozen type compiles with only `import GMT.Ch07.Submission`. It is about 30 lines, follows steps 1–5 and has axioms propext, Classical.choice and Quot.sound.

## Key steps

1. k is integrable because ∫k = 1 ≠ 0, hence a.e.-strongly measurable; since k ≥ 0, ∫⁻‖k‖ₑ = ofReal(∫k) = 1.
2. Pointwise: ‖(k⋆g)(x)‖ₑ ≤ ∫⁻_t ‖k(t)‖ₑ‖g(x − t)‖ₑ (convolution_def, enorm_integral_le_lintegral_enorm, enorm_mul).
3. (x, t) ↦ ‖k(t)‖ₑ‖g(x − t)‖ₑ is a.e.-measurable for the product measure (AEStronglyMeasurable.convolution_integrand, then enorm).
4. Tonelli (lintegral_lintegral_swap), lintegral_const_mul', translation invariance (lintegral_sub_right_eq_self) and lintegral_mul_const'' give (∫⁻‖k‖ₑ)(∫⁻‖g‖ₑ) = ∫⁻‖g‖ₑ.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); git diff --quiet b4d606db1 025f2e75395fc2ea91d8e2d9b8f5b42619a13ab6 -- GMT lakefile.toml lake-manifest.json lean-toolchain (no diff); git -C .lake/packages/mathlib rev-parse HEAD = 25730c7c759d108ef87ab70af2342a196760f79d (= manifest.json mathlib_commit)`
- `rg -n -i 'mollif|convolution' project/GMT -g '*.lean' (no match)`
- `rg -n -A8 'theorem dist_convolution_le |theorem support_convolution_subset_swap|theorem AEStronglyMeasurable.convolution_integrand |theorem HasCompactSupport.convolutionExists_left|theorem HasCompactSupport.continuous_convolution_left|theorem ConvolutionExists.distrib_add|theorem Integrable.integrable_convolution|theorem convolution_def' mathlib/Mathlib/Analysis/Convolution.lean`
- `rg -n -B2 -A6 'convolutionExists_left|continuous_convolution_left' mathlib/Mathlib/Analysis/Convolution.lean; rg -n -A6 'theorem Integrable.exists_hasCompactSupport_lintegral_sub_le' mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `rg -n 'uniformContinuous_of_continuous' mathlib/Mathlib (HasCompactMulSupport.uniformContinuous_of_continuous with @[to_additive], Topology/UniformSpace/HeineCantor.lean:91)`
- `rg -n 'theorem lintegral_lintegral_swap|theorem lintegral_sub_right_eq_self|theorem enorm_integral_le_lintegral_enorm|theorem lintegral_indicator_const |theorem integrable_of_integral_eq_one|theorem ofReal_integral_eq_lintegral_ofReal|theorem lintegral_add_left'|theorem lintegral_const_mul' |theorem lintegral_mul_const' ' mathlib/Mathlib; rg -n 'lintegral_div_right_eq_self|to_additive' mathlib/Mathlib/MeasureTheory/Group/LIntegral.lean`
- `rg -n 'cmcdt_cbm_sa_ml_|ml_l1_contraction|compact_support_approx' project -g '*.lean'; rg -l 'cmcdt_cbm_sa_ml_' mathlib/Mathlib -g '*.lean'; rg -n 'cmcdt_cbm_sa_ml_' GMT -g '*.lean'; rg -c 'cmcdt_cbm_sa_ml_' dag.json DAG.md dag.mmd issue-workers.json; rg -l -g 'decomposition*.json' -g 'parent-child-handoff.json' 'cmcdt_cbm_sa_ml_' nodes (all no match)`
- `python3 -I scan of runs/20261011T150044Z-ba604216b4/dag.json for convolution|mollif|ContDiffBump|exists_hasCompactSupport nodes; git show d25d2377e19ed3ca45d577187262c010630879ff:GMT/Ch07/Submission.lean (accepted codim1_zsl_pc_mollify_indicator_l1, other branch)`
- `read nodes/...-ffb05fc76b/decomposition-v1.json (mollify_adjoint: should_split false, 87 lines) and nodes/...-57a8a4ba62/decomposition-v1.json (smoothed_field: should_split false, 59 lines)`
- `lake env lean /tmp/ml1-decomp/final/TypesOnly.lean; lake env lean /tmp/ml1-decomp/final/Children.lean; lake env lean /tmp/ml1-decomp/final/Final.lean (#print axioms: propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Group/LIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-f665c996e3/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-ffb05fc76b/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-57a8a4ba62/decomposition-v1.json`
- `/tmp/ml1-decomp/final/TypesOnly.lean`
- `/tmp/ml1-decomp/final/Children.lean`
- `/tmp/ml1-decomp/final/Final.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) is identical to the workspace Contract.lean and Submission.lean. The node's proof base 025f2e75 has no GMT or lake-file changes.

Nothing in the snapshot proves either child. The project GMT tree has no mollifier or convolution results. Mathlib has neither the L¹ contraction of convolution nor the uniform L¹ approximate identity.

Mathlib does supply every tool the child and assembly proofs use:
- Analysis/Convolution.lean: dist_convolution_le, support_convolution_subset_swap, AEStronglyMeasurable.convolution_integrand, convolution_def, HasCompactSupport.convolutionExists_left, HasCompactSupport.continuous_convolution_left, ConvolutionExists.distrib_add;
- ContinuousMapDense.lean: Integrable.exists_hasCompactSupport_lintegral_sub_le (outside the frozen import closure; only the parent needs it);
- HeineCantor.lean: HasCompactSupport.uniformContinuous_of_continuous (via to_additive);
- Measure/Prod.lean: lintegral_lintegral_swap;
- Group/LIntegral.lean: lintegral_sub_right_eq_self (via to_additive);
- Bochner/Basic.lean: integrable_of_integral_eq_one, enorm_integral_le_lintegral_enorm, ofReal_integral_eq_lintegral_ofReal;
- Lebesgue/Basic.lean: lintegral_indicator_const;
- Lebesgue/Add.lean: lintegral_add_left', lintegral_const_mul', lintegral_mul_const''.

The related accepted DAG nodes codim1_zsl_pc_mollify_indicator_l1 and codim1_rdo_dg_bvc_mollify_l1_le concern indicator functions on balls. They lie on other branches outside the proof base and are not reusable.

The sibling decompositions (mollify_adjoint, smoothed_field) chose not to split and reserve no cmcdt_cbm_sa_ml_* names. No such name exists anywhere searched.

The Lean checks in /tmp/ml1-decomp/final show:
- both child types elaborate under import GMT.Ch07.Submission;
- both children compile with only that import;
- the exact frozen parent compiles from the two children;
- the axioms are only propext, Classical.choice and Quot.sound.
