# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.exp_monotonicity-a1`
- Child DAG node: `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.exp_monotonicity-a1.ode_monotonicity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent proof (Simon Ch. 4, 3.16–3.17: multiply by the integrating factor and integrate), isolated as a one-variable calculus lemma.
1. Reduction. For s > 0, exp(n·log s) = (exp(log s))^n = s^n, hence exp(κs − n·log s) = e^{κs}/s^n (Real.exp_sub, Real.exp_nat_mul, Real.exp_log). Define G(s) := exp(κs − n·log s)·I(s). Then G(s) = e^{κs}/s^n·I(s) for every s ∈ (0, r]. So it suffices to prove that G is monotone on (0, r] and transfer this along the equality on (0, r] (MonotoneOn.congr).
2. Derivative of G. Let s ∈ (0, r). Since s ≠ 0, log has derivative 1/s at s, so s ↦ κs − n·log s has derivative κ − n/s at s. By the chain rule for exp and the product rule with HasDerivAt I (I′ s) s, G has derivative G′(s) = exp(κs − n·log s)·((κ − n/s)·I(s) + I′(s)) at s.
3. Sign of G′. For s ∈ (0, r), (κ − n/s)·I(s) + I′(s) = (κ·s·I(s) − (n·I(s) − s·I′(s)))/s. The numerator is ≥ 0 by hypothesis and s > 0, so this quotient is ≥ 0. Since exp(·) > 0, G′(s) ≥ 0.
4. Continuity of G on (0, r]. On (0, r] ⊆ (0, ∞), log is continuous, so s ↦ κs − n·log s and its exponential are continuous there. I is continuous on (0, r] by hypothesis, so G is continuous on (0, r].
5. Mean value theorem. The set (0, r] = Ioc 0 r is convex and its interior is (0, r) (interior_Ioc). By steps 2–4, G is continuous on (0, r] and differentiable on (0, r), with deriv G(s) = G′(s) ≥ 0 for s ∈ (0, r). Hence monotoneOn_of_deriv_nonneg shows that G is monotone on (0, r]. If r ≤ 0, the set is empty and the argument holds trivially.
6. Conclusion. By step 1, s ↦ e^{κs}/s^n·I(s) agrees with G on (0, r], so it is monotone on (0, r].
Lean remark (optional aid; the proof above is complete without it): during decomposition, a warning-free, kernel-checked proof of exactly this frozen type was written. It uses only the axioms propext, Classical.choice and Quot.sound, and it follows steps 1–6. Scratch copies, which may no longer exist: /tmp/dsmc-em-decomp/C1.lean, and /tmp/dsmc-em-decomp/Full.lean (all four children plus the parent assembly).

## Key steps

1. On (0, r], e^{κs}/s^n·I(s) = G(s) := exp(κs − n·log s)·I(s).
2. G′(s) = exp(κs − n·log s)·((κ − n/s)I(s) + I′(s)) for s ∈ (0, r).
3. (κ − n/s)I + I′ = (κsI − (nI − sI′))/s ≥ 0 by the hypothesis, so G′ ≥ 0 on (0, r).
4. G is continuous on (0, r]; monotoneOn_of_deriv_nonneg on the convex set Ioc 0 r, whose interior is Ioo 0 r, gives monotonicity; transfer to e^{κs}/s^n·I(s).

## Reference use

### local-project

Queries:
- `cat nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ex-17c79c81ce/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.json}`
- `python3 -I over dag.json: list every node id, lean_name and status; print statements and lean_statements of the siblings under mean_curvature_monotonicity-a1 and of the related monotonicity nodes (dimred monotonicity, dorag monotonicity, dtc cone monotonicity_identity, regcomp monotonicity_mass_bound)`
- `cat GMT/Ch07/Submission.lean (IMRep, IMRep.measure, approxTangentPlane, tangentialDivergence, IMRep.firstVariation)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `rg -n 'smoothTransition|monotoneOn_of_deriv_nonneg|hasDerivAt_integral_of_dominated|exp_monotone|cutoff' local-references/123e8435b4a2469b/project --glob '*.lean' (no match: the snapshot project contains only the frozen contract)`
- `rg -n 'ofReal_measureReal|monotoneOn_of_deriv_nonneg|continuousOn_of_dominated|hasDerivAt_integral_of_dominated_loc_of_deriv_le|Antitone.deriv_nonpos|Monotone.deriv_nonneg|interior_Ioc|tendsto_integral_of_dominated_convergence' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n 'theorem integral_indicator_one|theorem integral_withDensity_eq_integral_smul|theorem starProjection_eq_sum_rankOne' local-references/123e8435b4a2469b/mathlib/Mathlib; rg the smoothTransition API (zero_of_nonpos, one_of_one_le, nonneg, le_one, contDiff, monotone) in Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `grep -n 'def HasApproximateTangentSpaceAt' -A 25 simongmt Chapter03/Rectifiable.lean (finrank = n conjunct, .finrank_eq, .unique)`
- `grep -n '^theorem' simongmt Chapter04/MeanCurvature.lean; sed -n 1,130p (RectifiableVarifold monotonicity; module not imported by the contract)`
- `sed -n 452,1105p .swarm-worktrees/5a60867de71e532024b6/gmt-ch07/GMT/Ch07/Submission.lean (accepted Submission.regcomp_monotonicity_mass_bound at commit 67f6a7b)`
- `sed -n 200,440p book/chapter-04.txt (Simon Ch. 4, 3.1–3.17)`
- `python3 -I: verifier/gmt-compare.py contract_scope + child_modules to generate the exact NodeChallenge/NodeSolution text for the four child types`
- `lake env lean /tmp/dsmc-em-decomp/{Stmts,Assembly,C1,C2,C3,C4,Full,FullSol,AllChallenges}.lean, each with #print axioms`
- `rg -l --fixed-strings dsmc_em_ in dag.json, GMT/, .swarm-worktrees (*.lean) and lake-packages simongmt (name-collision check: no match)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ex-17c79c81ce/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ex-17c79c81ce/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ex-17c79c81ce/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/DenselyOrdered.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/MeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/.swarm-worktrees/5a60867de71e532024b6/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/dsmc-em-decomp/Stmts.lean`
- `/tmp/dsmc-em-decomp/Assembly.lean`
- `/tmp/dsmc-em-decomp/C1.lean`
- `/tmp/dsmc-em-decomp/C2.lean`
- `/tmp/dsmc-em-decomp/C3.lean`
- `/tmp/dsmc-em-decomp/C4.lean`
- `/tmp/dsmc-em-decomp/Full.lean`
- `/tmp/dsmc-em-decomp/FullSol.lean`
- `/tmp/dsmc-em-decomp/AllChallenges.lean`
- `/tmp/dsmc-em-decomp/statements.json`

Snapshot: project b4d606d, mathlib 25730c7c. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

The snapshot project holds only the frozen contract, so it contains no declaration for any child; no rg match. Mathlib in the snapshot provides every library fact the children use:
- monotoneOn_of_deriv_nonneg, interior_Ioc;
- continuousOn_of_dominated, hasDerivAt_integral_of_dominated_loc_of_deriv_le, tendsto_integral_of_dominated_convergence;
- Antitone.deriv_nonpos, the Real.smoothTransition API;
- integral_indicator_one, integral_withDensity_eq_integral_smul, OrthonormalBasis.starProjection_eq_sum_rankOne, ofReal_measureReal.

SimonGMT supplies the following:
- HasApproximateTangentSpaceAt includes finrank = n, and approximate tangent spaces are unique (.unique).
- Chapter04/MeanCurvature.lean has the same monotonicity, but only for its RectifiableVarifold and not imported by the contract, so it was used only as a reference.

The accepted proof of Submission.regcomp_monotonicity_mass_bound provided proven tactic patterns: the a.e. frame from R.orients, trace of ∑ rankOne, Bessel, the withDensity integral conversion, and smoothTransition cutoffs.

Results in Lean:
- All four proposed child types elaborate in the exact comparator scope. The challenge modules were generated by the verifier's own code.
- Each child type was fully proved in scratch files.
- The parent's frozen type dsmc_exp_ball_mass_monotone was proved from the four children.
- #print axioms shows only propext, Classical.choice and Quot.sound.
- The bare names dsmc_em_* do not collide with any DAG node, worktree or library declaration.
