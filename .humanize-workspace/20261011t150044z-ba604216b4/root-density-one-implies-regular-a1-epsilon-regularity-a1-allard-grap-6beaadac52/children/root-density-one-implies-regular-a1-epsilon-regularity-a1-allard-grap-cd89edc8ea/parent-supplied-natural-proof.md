# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.poincare_ball-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.poincare_ball-a1.sq_integral_le-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the Cauchy–Schwarz inequality used twice in the parent proof. In step 3 ('Cauchy–Schwarz on [0, 1]') it is applied with μ = L¹ restricted to (0, 1] and μ(α) = 1. In step 4 ('(u(x) − ū)² ≤ ω^{−1}∫_B (u(x) − u(y))² dy') it is applied with μ = Lⁿ restricted to the set and μ(α) = ω. It is written out here by expanding a square.

1. (Integrability.)
- Since μ(α) < ∞, μ is a finite measure.
- As h ∈ L²(μ) and μ is finite, h ∈ L¹(μ): L² ⊆ L¹ on a finite measure space (Mathlib: MemLp.integrable with 1 ≤ 2).
- h² ∈ L¹(μ): apply MemLp.integrable_norm_pow with p = 2 and use ‖h(x)‖² = h(x)². MemLp.integrable_sq is in Mathlib/MeasureTheory/Function/L2Space.lean, which is outside the import closure of the frozen contract.
- Constants are μ-integrable because μ is finite.
Put m := μ(α) ∈ [0, ∞), read as a real number, and c := ∫ h dμ.

2. (Case m = 0.) Then μ(α) = 0, because μ(α) is finite and its real value is 0. So μ is the zero measure (Measure.measure_univ_eq_zero). Hence c = 0 and ∫ h² dμ = 0, and both sides of the claimed inequality are 0.

3. (Case m > 0.) The function x ↦ (h(x) − c/m)² is nonnegative, so 0 ≤ ∫ (h − c/m)² dμ. Pointwise, (h − c/m)² = h² − 2(c/m)h + (c/m)². Each term is integrable by step 1, so linearity and ∫ a dμ = a·m for constants a give
∫ (h − c/m)² dμ = ∫ h² dμ − 2(c/m)·c + (c/m)²·m = ∫ h² dμ − c²/m.

4. (Conclusion.) Steps 3 gives c²/m ≤ ∫ h² dμ. Multiplying by m > 0 gives c² ≤ m·∫ h² dμ, that is (∫ h dμ)² ≤ μ(α)·∫ h² dμ. ∎

## Key steps

1. μ is finite, and h, h² ∈ L¹(μ) (MemLp.integrable; MemLp.integrable_norm_pow at p = 2).
2. If m = μ(α) = 0, then μ = 0 and both sides vanish.
3. If m > 0, set c = ∫h; then 0 ≤ ∫(h − c/m)² dμ = ∫h² dμ − c²/m by linearity.
4. Multiply by m to get c² ≤ m∫h² dμ.

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json  (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean && cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean  (IDENTICAL)`
- `sed -n 200,260p <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean; grep -n 'theorem\|lemma' <snapshot>/mathlib/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean; sed -n 300,330p (same file)`
- `grep -n '^theorem\|^lemma' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean; rg -n 'lintegral_comp_smul|setLIntegral_comp_smul|lintegral_map_equiv|lintegral_add_left_eq_self' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem (sq_integral|integral_sq|sq_integral_le|integral_mul_le_Lp_mul_Lq|inner_le_nnorm_mul_nnorm|integral_mul_self_le|abs_integral_mul_le)' <snapshot>/mathlib/Mathlib`
- `rg -n "variance_le_expectation_sq|variance_def'|theorem variance_nonneg|sq_integral_le_integral_sq|integral_sq_le|ConvexOn.map_integral_le|map_average_le" <snapshot>/mathlib/Mathlib`
- `grep -rn 'integrable_sq\|two_iff_integrable' <snapshot>/mathlib/Mathlib --include=*.lean`
- `grep -n for LipschitzWith.ae_differentiableAt (Analysis/Calculus/Rademacher.lean), map_addHaar_smul / addHaar_preimage_smul (Measure/Lebesgue/EqHaar.lean), measure_prod_null / ae_ae_of_ae_prod / prod_apply_symm / lintegral_lintegral_swap (Measure/Prod.lean), Integrable.integral_prod_left (Integral/Prod.lean), MemLp.integrable_norm_pow (Function/L1Space/Integrable.lean)`
- `lean (toolchains/lean-4.35.0-rc3-linux, LEAN_PATH = workspace .lake builds) #check probes /tmp/poincare-decomp/Test0.lean, Test1.lean, Names2.lean of the cited lemmas in the import closure of GMT.Ch07.Submission`
- `grep -rn -E 'AbsolutelyContinuousOnInterval|integral_deriv_eq_sub|sq_integral|variance|ae_differentiableAt' .lake/packages/simongmt/Poincare; grep -n -E '^(theorem|lemma)' .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/Poincare.lean; grep -rn -i -E 'poincar|segment_ftc|sq_integral|variance_bound' <snapshot>/project/GMT`
- `python3 -I scans of dag.json (316 nodes) and nodes/*/*.json for 'dorag_ha_pb' names and for related nodes (poincare/segment/cauchy/variance, LipschitzWith with fderiv): no collision`
- `for b in $(git branch): git show $b:GMT/Ch07/Submission.lean | grep -c '^import'  (4 branches add one import; root.density_and_tangent_cones-a1.im_sub-a1 accepted)`
- `python3 -I: verifier/gmt-compare.py contract_scope('GMT.Ch07.main_theorem') replay and lean_contract.validate_lean_statement on the 7 child types; lean NodeChallengeBase.lean (import GMT.Ch07.Submission, 7 x sorry) and NodeSolution.lean (exact Submission.X against compiled /tmp/poincare-decomp/build/PBFull.olean)`
- `lean /tmp/poincare-decomp/{Children,Assembly,Pair,Double,Variance,LeafCS,LeafFTC,LeafNull,LeafSlice,Full}.lean; #print axioms GMT.Ch07.Submission.dorag_ha_poincare_ball`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L2Space.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convex/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Probability/Moments/Variance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Group/LIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/Poincare.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/SobolevTruncation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-6beaadac52/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-6beaadac52/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/poincare-decomp/Children.lean`
- `/tmp/poincare-decomp/Assembly.lean`
- `/tmp/poincare-decomp/Pair.lean`
- `/tmp/poincare-decomp/Double.lean`
- `/tmp/poincare-decomp/Variance.lean`
- `/tmp/poincare-decomp/LeafCS.lean`
- `/tmp/poincare-decomp/LeafFTC.lean`
- `/tmp/poincare-decomp/LeafNull.lean`
- `/tmp/poincare-decomp/LeafSlice.lean`
- `/tmp/poincare-decomp/Full.lean`
- `/tmp/poincare-decomp/cmp/NodeChallengeBase.lean`
- `/tmp/poincare-decomp/cmp/NodeSolution.lean`

Scope: the snapshot pins project b4d606d and Mathlib 25730c7c. GMT/Ch07/Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, so the child types were checked in the frozen scope.

What is NOT in the contract's import closure:
- AbsolutelyContinuousOnInterval.integral_deriv_eq_sub (AbsolutelyContinuousFun.lean:225);
- LipschitzOnWith.absolutelyContinuousOnInterval (AbsolutelyContinuous.lean:309);
- ConvexOn.map_average_le (Analysis/Convex/Integral.lean:128);
- ProbabilityTheory.variance_def';
- MemLp.integrable_sq (Function/L2Space.lean:42).
Hence sq_integral_le is a separate child, the proofs use MemLp.integrable_norm_pow (L1Space/Integrable.lean:212), and segment_ftc must add the two AbsolutelyContinuous imports. Extra imports are accepted by the comparator (im_sub-a1 precedent).

What IS available, as confirmed by #check:
- LipschitzWith.ae_differentiableAt (Rademacher.lean:385), measurableSet_of_differentiableAt, measurable_fderiv, norm_fderiv_le_of_lipschitz;
- Measure.map_addHaar_smul and addHaar_preimage_smul (EqHaar.lean:336,352), measure_preimage_add, lintegral_add_left_eq_self;
- Measure.measure_prod_null, ae_ae_of_ae_prod and prod_apply_symm (Prod.lean:401,433,706), lintegral_lintegral_swap (Prod.lean:1071);
- Integrable.integral_prod_left (Integral/Prod.lean:331), ofReal_integral_eq_lintegral_ofReal, integral_eq_lintegral_of_nonneg_ae, MemLp.of_bound, convex_ball, intervalIntegral.integral_congr_ae.

Nothing reusable: the project and SimonGMT have no Euclidean Poincaré, segment-FTC or Cauchy–Schwarz lemma. SimonGMT Chapter04/Poincare.lean is the varifold (Michael–Simon) inequality; Chapter02/Lipschitz.lean:192 only re-exports Rademacher. No comparator-accepted declaration with these types exists in dag.json, and the names dorag_ha_pb_* are free.

Lean checks:
- all seven child types elaborate in comparator scope and pass validate_lean_statement;
- the parent compiles from variance_bound and double_integral_bound;
- each dependent child compiles from its declared siblings, and the four leaves are fully proved;
- the 457-line tree has no sorry, and the parent's axioms are exactly propext, Classical.choice and Quot.sound;
- NodeSolution `exact Submission.X` passes for all seven.
