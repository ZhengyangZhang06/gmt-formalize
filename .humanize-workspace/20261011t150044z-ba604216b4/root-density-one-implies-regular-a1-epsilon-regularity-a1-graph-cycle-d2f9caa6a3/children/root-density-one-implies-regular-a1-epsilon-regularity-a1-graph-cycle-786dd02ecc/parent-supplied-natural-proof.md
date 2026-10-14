# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.smooth_to_c1_tests-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.smooth_to_c1_tests-a1.normalized_mollifier-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof ("Mollifiers": a ContDiffBump B_r centred at 0 with rIn = r/2, rOut = r, normalized by hand as ϱ_r := (∫B_r)⁻¹·B_r). Mathlib's ContDiffBump.normed / ContDiffBump.integral_normed live in Mathlib/Analysis/Calculus/BumpFunction/Normed.lean, which is NOT in the import closure of GMT.Ch07.Submission, so the normalization is done by hand.
Notation: ℝⁿ = Euclid n = EuclideanSpace ℝ (Fin n) with Lebesgue measure volume; ∫ means ∫ ... ∂volume.
1. Fix n ∈ ℕ and r > 0. Euclid n is a finite-dimensional real normed space, so the instance HasContDiffBump (Euclid n) is found by instance search (ExistsContDiffBumpBase.instHasContDiffBumpOfFiniteDimensionalReal; HasContDiffBump is a Prop, so which instance is found does not matter). Let B : ContDiffBump (0 : Euclid n) be the bump with rIn := r/2 and rOut := r; the side conditions 0 < r/2 and r/2 < r are half_pos hr and half_lt_self hr. Write B(x) for its value (the coercion Euclid n → ℝ).
2. Properties of B. (i) ContDiff ℝ (⊤ : ℕ∞) B (ContDiffBump.contDiff holds for every order in ℕ∞). (ii) B is continuous (ContDiffBump.continuous). (iii) 0 ≤ B(x) for every x (ContDiffBump.nonneg). (iv) support B = ball 0 r (ContDiffBump.support_eq, since rOut = r). (v) HasCompactSupport B (ContDiffBump.hasCompactSupport; Euclid n is finite-dimensional).
3. B is integrable: it is continuous with compact support and volume is finite on compact sets (Continuous.integrable_of_hasCompactSupport with 2(ii), 2(v)).
4. I := ∫ B(x) dx is positive. By integral_pos_iff_support_of_nonneg (B ≥ 0 by 2(iii), integrable by 3), 0 < I if and only if 0 < volume (support B). By 2(iv), support B = ball 0 r, and volume (ball 0 r) > 0 because r > 0 and Lebesgue measure gives positive mass to nonempty open sets (Metric.measure_ball_pos volume 0 hr). Hence I > 0; in particular I ≠ 0 and I⁻¹ ≥ 0.
5. Define ρ(x) := I⁻¹ · B(x), i.e. ρ = fun x => (∫ y, B y)⁻¹ * B x. Then:
 (a) ρ is C^∞ (order (⊤ : ℕ∞)): it is the product of the constant function I⁻¹ and B (contDiff_const.mul with 2(i)).
 (b) ρ has compact support: support ρ ⊆ support B, and HasCompactSupport.mul_left applied to 2(v) gives HasCompactSupport ρ.
 (c) ρ(x) ≥ 0 for every x: mul_nonneg of I⁻¹ ≥ 0 (inv_nonneg, step 4) and B(x) ≥ 0 (2(iii)).
 (d) ∫ ρ = I⁻¹ · ∫ B = I⁻¹ · I = 1, by integral_const_mul and inv_mul_cancel₀ (I ≠ 0, step 4).
 (e) support ρ ⊆ support B = ball 0 r, by Function.support_mul_subset_right (the support of x ↦ c · B(x) is contained in the support of B) and 2(iv).
6. Thus ρ is smooth, compactly supported, nonnegative, has integral 1 and support ρ ⊆ ball (0 : Euclid n) r, which is the claim. ∎

## Key steps

1. Take the ContDiffBump B centred at 0 with rIn = r/2, rOut = r: smooth, nonnegative, support B = ball 0 r, compact support, integrable.
2. I := ∫B > 0 by integral_pos_iff_support_of_nonneg, since volume (ball 0 r) > 0.
3. ρ := I⁻¹·B is smooth, compactly supported, nonnegative, has ∫ρ = I⁻¹·I = 1, and support ρ ⊆ support B = ball 0 r.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD vs manifest.json project_commit`
- `lake env lean /tmp/stc1-work/Closure.lean: #check ContDiffBump.{contDiff,support_eq,nonneg,normed,integral_normed,dist_normed_convolution_le,convolution_tendsto_right}, HasContDiffBump (Euclid 3), HasCompactSupport.contDiff_convolution_left, HasCompactSupport.hasFDerivAt_convolution_right, convolution_precompR_apply, dist_convolution_le, support_convolution_subset, IsCompact.exists_cthickening_subset_open, IsCompact.cthickening, LocallyIntegrableOn.integrableOn_compact_subset, integral_pos_iff_support_of_nonneg, Metric.measure_ball_pos, fderiv_of_notMem_tsupport, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, Integrable.mul_bdd, norm_integral_le_of_norm_le, setIntegral_eq_integral_of_forall_compl_eq_zero, HasCompactSupport.fderiv, HasCompactSupport.uniformContinuous_of_continuous, ContDiff.continuous_fderiv, EuclideanSpace.basisFun_apply after import GMT.Ch07.Submission`
- `lake env lean /tmp/stc1-work/Names.lean: #check ContDiffBump.hasCompactSupport, ContDiffBump.continuous, integral_const_mul, Function.support_mul_subset_right, HasCompactSupport.exists_bound_of_continuous, mem_cthickening_of_dist_le, isClosed_cthickening, self_subset_cthickening, HasCompactSupport.mul_left, ae_restrict_of_forall_mem, Continuous.locallyIntegrable, HasFDerivAt.fderiv, Metric.uniformContinuous_iff, IsCompact.of_isClosed_subset, closure_minimal, Set.mem_add, integral_sub, integral_mul_const, Continuous.clm_apply`
- `#synth HasContDiffBump (EuclideanSpace ℝ (Fin 3))`
- `rg -n 'theorem dist_convolution_le\b|contDiff_convolution_left|hasFDerivAt_convolution_right|theorem convolution_precompR_apply|theorem support_convolution_subset' mathlib/Mathlib/Analysis/Convolution.lean`
- `rg -n 'theorem support_eq|protected theorem contDiff|theorem nonneg|protected theorem hasCompactSupport|protected theorem continuous|^structure ContDiffBump' mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean; rg -n 'def normed|theorem integral_normed' mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean; rg -n 'hasContDiffBump_of_innerProductSpace' mathlib/Mathlib/Analysis/Calculus/BumpFunction/InnerProduct.lean`
- `rg -n 'exists_cthickening_subset_open|mem_cthickening_of_dist_le|isClosed_cthickening|IsCompact.cthickening' mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `rg -n 'integral_pos_iff_support_of_nonneg|setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|setIntegral_eq_integral_of_forall_compl_eq_zero|Integrable.mul_bdd' in mathlib/Mathlib/MeasureTheory/Integral/Bochner/{Basic,Set}.lean and Function/L1Space/Integrable.lean`
- `rg -n 'mollif|ContDiffBump|convolution' project/GMT; rg -ln 'ContDiffBump|convolution' simongmt/Poincare; rg -n 'ContDiffBump|convolution|^theorem' Chapter08/DistributionalConstancy.lean Chapter02/WhitneyPartition.lean`
- `python3 scan of dag.json node lean_name/lean_statement/title for mollif|ContDiffBump|convolution|bump, and of nodes/*/decomposition-v*.json lean_names for mollif|bump`
- `grep -rl dgcr_stc_ dag.json nodes/; git grep -l <each proposed name> over all refs`
- `python3 -I: verifier lean_contract.validate_lean_statement and gmt-compare.contract_scope replay -> /tmp/stc1-work/Challenge.lean (exact Submission.X for each child type)`
- `lake env lean /tmp/stc1-work/{A,B,C,Split,All,Challenge}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-d2f9caa6a3/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-d2f9caa6a3/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-d2f9caa6a3/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/InnerProduct.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyPartition.lean`
- `/tmp/stc1-work/Closure.lean`
- `/tmp/stc1-work/Names.lean`
- `/tmp/stc1-work/A.lean`
- `/tmp/stc1-work/B.lean`
- `/tmp/stc1-work/C.lean`
- `/tmp/stc1-work/Split.lean`
- `/tmp/stc1-work/All.lean`
- `/tmp/stc1-work/Challenge.lean`

The snapshot is project b4d606d and mathlib 25730c7c. Its Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, and HEAD equals the manifest project_commit.

Import closure of GMT.Ch07.Submission:
- Every lemma cited in the three child proofs and the parent glue resolves after import GMT.Ch07.Submission. This includes the ContDiffBump basics, the HasContDiffBump instance on Euclid n, contDiff_convolution_left, hasFDerivAt_convolution_right, convolution_precompR_apply, dist_convolution_le, support_convolution_subset, the cthickening lemmas and the Bochner set-integral lemmas.
- ContDiffBump.normed, integral_normed, dist_normed_convolution_le and convolution_tendsto_right are Unknown constants. They live in Mathlib/Analysis/Calculus/BumpFunction/Normed.lean and Convolution files outside the closure, so the hand-normalized mollifier child is necessary.

No reusable local declaration exists:
- project/GMT has no mollifier, bump or convolution lemma.
- SimonGMT Chapter08/DistributionalConstancy.lean uses ContDiffBump.normed with C¹ tests and is outside the closure.
- Chapter02/WhitneyPartition.lean has only unnormalized Whitney bumps.
- The DAG nodes dor_ims_sua_mollify_unit_field and regcomp_exists_smooth_unit_form_approx approximate covector fields themselves, not derivatives, and sit in other branches.

The three proposed names dgcr_stc_* collide with nothing in dag.json, nodes/* or any git ref.

Lean checks:
- All child types pass validate_lean_statement and elaborate in the comparator contract scope.
- Each child type is proved in scratch.
- The exact parent type follows from the three child types.
- All four theorems use only propext, Classical.choice and Quot.sound.
