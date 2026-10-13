# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1.allard_lemma-a1.fibre_density_sum_bound-a1`
- Child DAG node: `root.integral_compactness-a1.allard_lemma-a1.fibre_density_sum_bound-a1.separated_sum_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent proof (the case #s ≥ 2), with the per-point output of step 2 and the conclusion of the sibling cylinder_cluster_bound as hypotheses, and the absorption of the constants by Aδ ≤ 1.
Conventions. All quantities lie in [0,∞]; a real a enters as ofReal a; for r > 0, r^n := ofReal(r)^n.

0. Preliminaries. ω_n is the Lebesgue measure of the open unit ball of ℝ^n; it is positive (nonempty open set, measure_ball_pos) and finite (bounded set in a proper space, measure_ball_lt_top). Hence ω := ω_n.toReal > 0 and ofReal(ω) = ω_n. From 0 < δ ≤ 1/2: δ² ≤ 1/4 and δ⁴ ≤ δ², so ε ≤ δ² ≤ 1/4. The estimate |e^t − 1| ≤ 2|t| for |t| ≤ 1 (Real.abs_exp_sub_one_le) at t = ε gives e^ε ≤ 1 + 2ε ≤ 1 + 2δ², and in particular e^ε ≤ 2.

1. Minimal separation. Since #s ≥ 2 there are distinct a, b ∈ s, so the finite set of pairs (y, y') ∈ s × s with y ≠ y' is nonempty; choose a pair (y₀, y₁) minimizing |y − y'| over it, and let d := |y₀ − y₁|. Then d > 0 (y₀ ≠ y₁), d ≤ |y − y'| for all distinct y, y' ∈ s, and d = |(y₀ − x) − (y₁ − x)| ≤ |y₀ − x| + |y₁ − x| < ε + ε = 2ε.

2. Scales. Put τ := d/16 and σ := d/(8δ²). Then: τ > 0; τ ≤ 1/4, since d < 2ε ≤ 1/2; σ > 0; σ < δ²/4, since d < 2ε ≤ 2δ⁴ gives d/(8δ²) < 2δ⁴/(8δ²); hence σ ≤ δ² and σ < 1 (δ² ≤ 1/4); 2δ²σ = d/4; 4τ = d/4; and Kεσ/τ = 2Kε/δ² ≤ 2Kδ², since Kε ≤ Kδ⁴ (K ≥ 0, ε ≤ δ⁴).

3. Per-point bound. For y ∈ s let X_y := μ(U^{d/4}_σ(y))/σ^n. The hypothesis at (τ, σ) (valid by step 2), rewritten with 4τ = d/4, gives Θ(y) ≤ (e^ε·X_y + Kεσ/τ)/ω_n ≤ (e^ε·X_y + 2Kδ²)/ω_n, by step 2 and monotonicity of ofReal, + and /ω_n.

4. Cluster bound. (CB) applies to (σ, d/4): 0 < σ ≤ δ², 2δ²σ = d/4 ≤ d/4, and 4·(d/4) = d ≤ |y − y'| for distinct y, y' ∈ s by step 1. With B := μ(B_1(x)) it gives Σ_{y∈s} X_y ≤ (1 + cδ²)B + cδ².

5. Summation. Summing step 3 over s, distributing the division by ω_n over the finite sum (ENNReal.sum_div), splitting the sum (Finset.sum_add_distrib) and pulling out the constant factor e^ε (Finset.mul_sum):
 Σ_{y∈s} Θ(y) ≤ (e^ε·Σ_{y∈s} X_y + #s·ofReal(2Kδ²))/ω_n.
 Since #s ≤ M, #s·ofReal(2Kδ²) ≤ M·ofReal(2Kδ²) = ofReal(M·2Kδ²). With step 4 and monotonicity:
 Σ_{y∈s} Θ(y) ≤ (e^ε·((1 + cδ²)B + cδ²) + M·2Kδ²)/ω_n = (ofReal(e^ε(1 + cδ²))·B + ofReal(e^ε·cδ² + 2MKδ²))/ω_n,
 using ofReal(a)ofReal(b) = ofReal(ab) and ofReal(a) + ofReal(b) = ofReal(a + b) for a, b ≥ 0.

6. Absorption (real inequalities). The summands 2c/ω and 2MK/ω of A are ≥ 0, so A ≥ 2 + 2c and A ≥ 2c/ω + 2MK/ω; and Aδ² = (Aδ)δ ≤ δ.
 (i) e^ε(1 + cδ²) ≤ (1 + 2δ²)(1 + cδ²) = 1 + (2 + c)δ² + 2cδ⁴ ≤ 1 + (2 + 2c)δ² ≤ 1 + Aδ² ≤ 1 + δ, using 2cδ⁴ ≤ cδ² (c ≥ 0, 2δ² ≤ 1).
 (ii) e^ε·cδ² + 2MKδ² ≤ 2cδ² + 2MKδ² = ω·(2c/ω + 2MK/ω)·δ² ≤ ω·Aδ² ≤ ωδ, using e^ε ≤ 2, c ≥ 0, ω > 0.

7. Conclusion. By step 6 and monotonicity, Σ_{y∈s} Θ(y) ≤ (ofReal(1 + δ)·B + ofReal(δω))/ω_n = ofReal(1 + δ)·B/ω_n + ofReal(δω)/ω_n (ENNReal.add_div). Finally ofReal(δω) = ofReal(δ)·ofReal(ω) = ofReal(δ)·ω_n, and ofReal(δ)·ω_n/ω_n = ofReal(δ) because ω_n ∈ (0,∞). Hence Σ_{y∈s} Θ(y) ≤ (1 + δ)μ(B_1(x))/ω_n + δ. Every step is a monotone operation in [0,∞], so the argument also covers μ(B_1(x)) = ∞. ∎

## Key steps

1. ω_n ∈ (0,∞), ω = ω_n.toReal > 0; ε ≤ δ² ≤ 1/4 and e^ε ≤ 1 + 2δ² ≤ 2
2. d := minimal distance between distinct points of s: 0 < d < 2ε and d ≤ |y − y'|
3. τ = d/16, σ = d/(8δ²): τ ≤ 1/4, 0 < σ < δ²/4 ≤ δ² < 1, 2δ²σ = d/4 = 4τ, Kεσ/τ ≤ 2Kδ²
4. per-point bound Θ(y) ≤ (e^ε X_y + 2Kδ²)/ω_n and (CB) at (σ, d/4)
5. sum: Σ Θ ≤ (e^ε(1 + cδ²)B + e^ε cδ² + 2MKδ²)/ω_n using #s ≤ M
6. absorb with Aδ ≤ 1: e^ε(1 + cδ²) ≤ 1 + δ and e^ε cδ² + 2MKδ² ≤ ωδ

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
