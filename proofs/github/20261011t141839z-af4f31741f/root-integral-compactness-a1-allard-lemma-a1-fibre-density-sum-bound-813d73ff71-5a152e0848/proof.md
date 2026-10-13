# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1.allard_lemma-a1.fibre_density_sum_bound-a1`
- Child DAG node: `root.integral_compactness-a1.allard_lemma-a1.fibre_density_sum_bound-a1.one_point_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent proof (the case s = {y}), with the density bound of step 1 as hypothesis; the parent adds the term δ afterwards.
Conventions. All quantities lie in [0,∞]; a real a enters as ofReal a.

1. Real bounds. From 0 < δ ≤ 1/2 ≤ 1: δ⁴ ≤ δ² and δ² ≤ 1/4. Hence ε ≤ δ⁴ ≤ δ² ≤ 1/4.

2. The radius σ := 1 − ε satisfies 0 < σ < 1 (as 0 < ε ≤ 1/4), and B_{1−ε}(y) ⊆ B_1(x): if |z − y| ≤ 1 − ε then |z − x| ≤ |z − y| + |y − x| ≤ (1 − ε) + ε = 1.

3. e^{ε(1−ε)} ≤ e^ε ≤ 1 + 2ε. The first inequality holds because ε(1 − ε) ≤ ε (ε > 0, 1 − ε ≤ 1) and exp is monotone. For the second, |ε| = ε ≤ 1, and the estimate |e^t − 1| ≤ 2|t| for |t| ≤ 1 (Real.abs_exp_sub_one_le) at t = ε gives e^ε − 1 ≤ 2ε.

4. (1 − ε)^{−1} ≤ 1 + 2ε. Since 1 − ε > 0 this is equivalent to 1 ≤ (1 − ε)(1 + 2ε) = 1 + ε(1 − 2ε), which holds because 0 < ε ≤ 1/2.

5. For u := 2ε ∈ [0,1] and every m ∈ ℕ: (1 + u)^m ≤ 1 + (2^m − 1)u. Induction on m: for m = 0 both sides equal 1. If it holds for k, then, as 1 + u ≥ 0, (1 + u)^{k+1} = (1 + u)^k(1 + u) ≤ (1 + (2^k − 1)u)(1 + u) = 1 + 2^k·u + (2^k − 1)u² ≤ 1 + 2^k·u + (2^k − 1)u = 1 + (2^{k+1} − 1)u, using 2^k − 1 ≥ 0 and u² ≤ u (0 ≤ u ≤ 1).

6. ((1 − ε)^n)^{−1} = ((1 − ε)^{−1})^n ≤ (1 + 2ε)^n ≤ 1 + (2^n − 1)·2ε, by step 4 and monotonicity of t ↦ t^n on [0,∞), then step 5 with m = n.

7. The real inequality e^{ε(1−ε)}/(1 − ε)^n ≤ 1 + δ. By steps 3 and 6 (all factors ≥ 0):
 e^{ε(1−ε)}·((1 − ε)^n)^{−1} ≤ (1 + 2ε)(1 + (2^n − 1)2ε) = 1 + 2^{n+1}ε + 4(2^n − 1)ε² ≤ 1 + 2^{n+1}ε + 2^{n+2}ε² ≤ 1 + 2^{n+2}ε,
 where the last step uses 2^{n+2}ε² ≤ 2^{n+1}ε, i.e. 2ε ≤ 1. Moreover 2^{n+2}ε ≤ 2^{n+2}δ² = (2^{n+2}δ)·δ ≤ δ by step 1 and 2^{n+2}δ ≤ 1. Hence e^{ε(1−ε)}/(1 − ε)^n ≤ 1 + δ.

8. Conclusion in [0,∞]. The hypothesis at σ = 1 − ε gives θ ≤ ofReal(e^{ε(1−ε)})·μ(B_{1−ε}(y))/(ω_n·ofReal(1 − ε)^n). Since (1 − ε)^n > 0, ofReal(e^{ε(1−ε)}/(1 − ε)^n) = ofReal(e^{ε(1−ε)})/ofReal((1 − ε)^n) and ofReal((1 − ε)^n) = ofReal(1 − ε)^n; and (ω_n·r)^{−1} = ω_n^{−1}·r^{−1} for r := ofReal(1 − ε)^n ∈ (0,∞). Rearranging the product therefore gives
 θ ≤ ofReal(e^{ε(1−ε)}/(1 − ε)^n)·μ(B_{1−ε}(y))/ω_n ≤ ofReal(1 + δ)·μ(B_1(x))/ω_n,
 by step 7 (monotonicity of ofReal) and step 2 (monotonicity of μ). ∎

## Key steps

1. ε ≤ δ² ≤ 1/4; σ := 1 − ε ∈ (0,1) and B_{1−ε}(y) ⊆ B_1(x)
2. e^{ε(1−ε)} ≤ e^ε ≤ 1 + 2ε and (1 − ε)^{−1} ≤ 1 + 2ε
3. (1 + u)^m ≤ 1 + (2^m − 1)u for u = 2ε ∈ [0,1], by induction
4. e^{ε(1−ε)}(1 − ε)^{−n} ≤ 1 + 2^{n+2}ε ≤ 1 + 2^{n+2}δ² ≤ 1 + δ
5. apply the density bound at σ = 1 − ε and rewrite in [0,∞]

## Reference use

### local-project

Queries:
- `cat local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae6, mathlib_commit 25730c7c)`
- `sha256sum snapshot project/GMT/Ch08/Contract.lean vs workspace GMT/Ch08/Contract.lean and Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `rg -n 'intcpt_allard|densityRatio|unitBallVolume' project/GMT/Ch08/Contract.lean`
- `rg -n 'theorem abs_exp_sub_one_le|theorem mul_inv \{a b|theorem ofReal_div_of_pos|theorem add_div \(|theorem norm_add_sq_real|theorem card_eq_one|theorem one_lt_card |theorem mem_offDiag' mathlib/Mathlib`
- `rg -n 'theorem sum_div|theorem toReal_pos|theorem ofReal_toReal|lemma one_le_pow₀|lemma pow_le_pow_of_le_one|theorem pow_le_pow_left₀|theorem measure_ball_pos|theorem measure_ball_lt_top' mathlib/Mathlib`
- `rg -n '(theorem|lemma) exists_min_image' mathlib/Mathlib (only Set and Northcott versions; Finset.exists_min_image confirmed by #check from import GMT.Ch08.Submission)`
- `rg -n 'theorem projectionLinearMap_isSymmetric|theorem project_project' simongmt Poincare/SimonGMT/Chapter08/Varifold.lean`
- `lake env lean /tmp/fdsb-decomp-v1/Probe.lean (#check Real.abs_exp_sub_one_le, measure_ball_pos, measure_ball_lt_top, ENNReal.mul_inv, ENNReal.sum_div, Finset.exists_min_image, Grassmannian.projectionLinearMap_isSymmetric, Grassmannian.project_project, tendsto_nhds_unique, one_add_mul_le_pow)`
- `grep -n '5.10|5.11|(6)' book/chapter-08.txt; sed -n 770,960p book/chapter-08.txt`
- `python3 over dag.json: frozen lean_statements of good_point_monotonicity, cylinder_monotonicity, cylinder_cluster_bound, fibre_density_sum_bound; decomposition-v1.json of allard_lemma-a1 and cylinder_cluster_bound-a1 (conventions)`
- `lake env lean /tmp/fdsb-decomp-v1/{Stubs,Assembly,ChildA,ChildB,ChildC,Full}.lean and Comp_*_Challenge.lean`
- `python3 -I verifier/lean_contract.py validate_lean_statement and verifier/gmt-compare.py child_modules (contract mode) on the 3 child statements`
- `grep -rl intcpt_allard_fdsb over the run directory; git grep intcpt_allard_fdsb over every ref of git for-each-ref (0 hits)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Complex/Exponential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/BigOperators.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Data/Finset/Card.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Data/Finset/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Data/Set/Finite/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-08.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-fibre-density-sum-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-cylinder-cluster-bound-a1/decomposition-v1.json`
- `/tmp/fdsb-decomp-v1/Assembly.lean`
- `/tmp/fdsb-decomp-v1/ChildA.lean`
- `/tmp/fdsb-decomp-v1/ChildB.lean`
- `/tmp/fdsb-decomp-v1/ChildC.lean`
- `/tmp/fdsb-decomp-v1/Full.lean`

The snapshot is project 63436ae6 + Mathlib 25730c7c. Its Contract is byte-identical to the workspace Contract and Submission; densityRatio, HasDensity and unitBallVolume are Contract lines 41–52. The children cite only lemmas in the snapshot or in Submission's import closure: Real.abs_exp_sub_one_le (Analysis/Complex/Exponential.lean:533); ENNReal.mul_inv, ofReal_div_of_pos and add_div (Basic/ENNReal/Inv.lean:245, 960, 505); ENNReal.sum_div (Basic/ENNReal/BigOperators.lean:143); ENNReal.toReal_pos (Real.lean:133); ENNReal.ofReal_toReal (Basic.lean:248); norm_add_sq_real (InnerProductSpace/Basic.lean:411); measure_ball_pos (Measure/OpenPos.lean:212); measure_ball_lt_top (Typeclasses/Finite.lean:373); Finset.card_eq_one and Finset.one_lt_card (Data/Finset/Card.lean:693, 747); Finset.mem_offDiag (Data/Finset/Prod.lean:266); Finset.exists_min_image (#check); one_le_pow₀, pow_le_pow_of_le_one and pow_le_pow_left₀ (Algebra/Order/GroupWithZero/Basic.lean); and SimonGMT Grassmannian.projectionLinearMap_isSymmetric and project_project (Chapter08/Varifold.lean:98, 108). No project declaration states printed (6), the one-point density bound or the separated sum. The related node ccb_one_point_ball_bound, in another branch, concerns the monotone ratio at σ ≤ δ², so it is not reused. All three children are fully proved in scratch using only these lemmas (axioms propext, Classical.choice, Quot.sound). The parent's frozen type follows from them plus the three sibling dependencies.
