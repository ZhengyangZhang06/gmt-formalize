# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_approx-a1.mollify_l1-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_approx-a1.mollify_l1-a1.compact_support_approx-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3 and 4 (choice of r and the continuous compactly supported case) of the supplied proof of the parent cmcdt_cbm_sa_mollify_l1. The argument is copied from there, with details filled in. Two changes: the tolerance ε/4 there becomes a general ε > 0 here, and the hypothesis that ρ is continuous is dropped because the argument never uses it. Step 3(a) is Mathlib's dist_convolution_le.

Notation. ℝⁿ := Euclid n = EuclideanSpace ℝ (Fin n) with Lebesgue measure (volume), and |·| is the Euclidean norm. For a ∈ ℝ, ‖a‖ₑ = ofReal|a| ∈ [0, ∞]; ∫⁻ is the [0, ∞]-valued Lebesgue integral. (ρ ⋆ h)(x) := ∫ ρ(t) h(x − t) dt is Mathlib's `convolution ρ h (ContinuousLinearMap.lsmul ℝ ℝ) volume x`. B_r(0) is the open ball. A + B := {a + b : a ∈ A, b ∈ B} is the Minkowski sum, which in Lean needs `open scoped Pointwise`, e.g. `open scoped Pointwise in` before the theorem. 1_S is the indicator function of S. Every lemma cited is in the import closure of the frozen GMT/Ch07/Submission.lean.

Fix h continuous with compact support, and ε > 0.

1. The compact set S. Let S := tsupport h + closedBall(0, 1).
   - tsupport h is compact (HasCompactSupport.isCompact) and closedBall(0, 1) is compact (isCompact_closedBall), so S is compact (IsCompact.add).
   - Hence S is closed, so measurable (IsCompact.isClosed, IsClosed.measurableSet), and vol(S) < ∞ (IsCompact.measure_lt_top).
   - Put V := vol(S).toReal ≥ 0. Then vol(S) = ofReal(V) (ENNReal.ofReal_toReal, since vol(S) ≠ ∞).

2. Choice of r. Put η := ε / (4(V + 1)) > 0. Since h is continuous with compact support, it is uniformly continuous (HasCompactSupport.uniformContinuous_of_continuous). By Metric.uniformContinuous_iff there is r₀ > 0 such that dist(h(a), h(b)) < η whenever dist(a, b) < r₀. Put r := min(r₀, 1) > 0. This r depends only on h and ε, so it is chosen before ρ, as the statement requires.

Now let ρ : ℝⁿ → ℝ satisfy ρ ≥ 0, ∫ ρ = 1 and support ρ ⊆ B_r(0).

3. Pointwise bound. For every x, ‖(ρ ⋆ h)(x) − h(x)‖ₑ ≤ 1_S(x) · ofReal(η).
 (a) Case x ∈ S. Apply dist_convolution_le with kernel ρ, radius R := r, centre x₀ := x, target z₀ := h(x) and bound η ≥ 0. Its hypotheses hold:
   - support ρ ⊆ ball(0, r);
   - ρ ≥ 0 and ∫ ρ = 1 (the lemma derives integrability of ρ from ∫ ρ = 1);
   - h is a.e.-strongly measurable, being continuous;
   - for every y ∈ ball(x, r), dist(y, x) < r ≤ r₀, so dist(h(y), h(x)) < η, in particular ≤ η.
   So dist((ρ ⋆ h)(x), h(x)) ≤ η. Since ‖a − b‖ₑ = ofReal(‖a − b‖) = ofReal(dist(a, b)) (ofReal_norm, dist_eq_norm) and ofReal is monotone, ‖(ρ ⋆ h)(x) − h(x)‖ₑ ≤ ofReal(η) = 1_S(x) · ofReal(η).
 (b) Case x ∉ S.
   - h(x) = 0. Otherwise x ∈ support h ⊆ tsupport h (subset_tsupport), and x = x + 0 with 0 ∈ closedBall(0, 1), so x ∈ S.
   - (ρ ⋆ h)(x) = 0. Otherwise x ∈ support(ρ ⋆ h) ⊆ support h + support ρ (support_convolution_subset_swap), so x = a + t with h(a) ≠ 0 and ρ(t) ≠ 0. Then a ∈ tsupport h, and t ∈ B_r(0), so |t| < r ≤ 1 and t ∈ closedBall(0, 1). Hence x ∈ S, a contradiction.
   So ‖(ρ ⋆ h)(x) − h(x)‖ₑ = ‖0 − 0‖ₑ = 0 = 1_S(x) · ofReal(η).

4. Integration. By lintegral_mono with step 3, then lintegral_indicator_const (S is measurable), then ENNReal.ofReal_mul (η ≥ 0):
   ∫⁻ ‖(ρ ⋆ h)(x) − h(x)‖ₑ dx ≤ ∫⁻ 1_S(x) · ofReal(η) dx = ofReal(η) · vol(S) = ofReal(η) · ofReal(V) = ofReal(η · V).

5. Numerics. η · V = ε V / (4(V + 1)) ≤ ε, because ε V ≤ 4ε(V + 1) when ε > 0 and V ≥ 0. Hence ofReal(η · V) ≤ ofReal(ε) (ENNReal.ofReal_le_ofReal), which together with step 4 proves the claim. ∎

The case n = 0 needs no separate treatment.

Formalization note: a complete Lean proof of the exact frozen type compiles with only `import GMT.Ch07.Submission` and `open scoped Pointwise in`. It is about 50 lines, follows steps 1–5 and has axioms propext, Classical.choice and Quot.sound.

## Key steps

1. S := tsupport h + closedBall(0, 1) is compact, hence measurable with finite measure; put V := vol(S).toReal.
2. η := ε/(4(V + 1)) > 0; uniform continuity of h gives r₀, and r := min(r₀, 1) is chosen before ρ.
3. For x ∈ S, dist_convolution_le gives ‖ρ⋆h(x) − h(x)‖ₑ ≤ ofReal(η). For x ∉ S, h(x) = 0 and ρ⋆h(x) = 0 by subset_tsupport and support_convolution_subset_swap.
4. ∫⁻‖ρ⋆h − h‖ₑ ≤ ofReal(η)·vol(S) = ofReal(ηV) ≤ ofReal(ε), since ηV ≤ ε.

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
