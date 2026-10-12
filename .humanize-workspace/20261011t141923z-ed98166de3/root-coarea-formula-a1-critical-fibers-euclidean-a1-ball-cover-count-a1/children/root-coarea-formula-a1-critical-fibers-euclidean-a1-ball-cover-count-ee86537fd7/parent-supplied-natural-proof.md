# Parent-supplied natural-language proof

- Parent DAG node: `root.coarea_formula-a1.critical_fibers_euclidean-a1.ball_cover_count-a1`
- Child DAG node: `root.coarea_formula-a1.critical_fibers_euclidean-a1.ball_cover_count-a1.packing_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1, 2 and 5 of the parent-supplied proof of bounded_set_closedBall_cover_card_mul_pow_le (packing by the disjoint balls B(x, r/2) inside the reference set thickening(1, K)).
Notation: Lⁿ = volume on ℝⁿ = Rn n; B(z,ρ) = {w : dist(w, z) < ρ} is the open ball.
1. Constants. Let U := thickening(1, K) = {z : infEdist(z, K) < 1}. By Metric.mem_thickening_iff, z ∈ U iff dist(z, a) < 1 for some a ∈ K. Since K is bounded, U is bounded (Bornology.IsBounded.thickening). ℝⁿ is proper and Lⁿ is finite on compacts, so Lⁿ(U) < ∞ (Bornology.IsBounded.measure_lt_top). Put A := Lⁿ(U).toReal and b := Lⁿ(B(0,1)).toReal. Lⁿ is positive on nonempty open sets, so 0 < Lⁿ(B(0,1)) (measure_ball_pos), and Lⁿ(B(0,1)) < ∞ (measure_ball_lt_top). Hence b > 0 (ENNReal.toReal_pos). Put C := 2ⁿ·A/b. C depends only on n and K.
Fix r ∈ ℝ with 0 < r ≤ 1, and a finite F ⊆ K with r < dist(x, y) for all distinct x, y ∈ F. We show card(F)·rⁿ ≤ C.
2. Ball volumes. Lⁿ is an additive Haar measure on the finite-dimensional space ℝⁿ, and finrank ℝ ℝⁿ = n (finrank_euclideanSpace_fin). Since r/2 > 0, Measure.addHaar_ball_of_pos gives Lⁿ(B(z, r/2)) = ofReal((r/2)ⁿ)·Lⁿ(B(0,1)) for every z ∈ ℝⁿ. This includes the case n = 0.
3. Disjointness. Let x ≠ y in F, and suppose z ∈ B(x, r/2) ∩ B(y, r/2). Then dist(x, y) ≤ dist(z, x) + dist(z, y) < r/2 + r/2 = r (dist_triangle_left), which contradicts r < dist(x, y). So the balls B(x, r/2), x ∈ F, are pairwise disjoint.
4. Containment. Let x ∈ F and z ∈ B(x, r/2). Then x ∈ K and dist(z, x) < r/2 < 1, because r ≤ 1. So z ∈ U by Metric.mem_thickening_iff. Hence ⋃_{x∈F} B(x, r/2) ⊆ U.
5. Measure count. Open balls are measurable. Finite additivity over the pairwise disjoint family (measure_biUnion_finset), step 2 and monotonicity of Lⁿ give card(F)·(ofReal((r/2)ⁿ)·Lⁿ(B(0,1))) = Σ_{x∈F} Lⁿ(B(x, r/2)) = Lⁿ(⋃_{x∈F} B(x, r/2)) ≤ Lⁿ(U).
6. Real form. Lⁿ(U) is finite, so ENNReal.toReal preserves the inequality of step 5 (ENNReal.toReal_mono). toReal is multiplicative (ENNReal.toReal_mul), sends the natural number card(F) to card(F), and sends ofReal((r/2)ⁿ) to (r/2)ⁿ because (r/2)ⁿ ≥ 0. Therefore card(F)·((r/2)ⁿ·b) ≤ A.
7. Conclusion. Since b > 0, the goal card(F)·rⁿ ≤ 2ⁿ·A/b is equivalent to card(F)·rⁿ·b ≤ 2ⁿ·A (le_div_iff₀). Since (r/2)ⁿ = rⁿ/2ⁿ, card(F)·rⁿ·b = 2ⁿ·(card(F)·((r/2)ⁿ·b)). By step 6 and 2ⁿ ≥ 0, this is ≤ 2ⁿ·A. Hence card(F)·rⁿ ≤ C. C was fixed in step 1 before r and F were chosen, so the same C works for all r ∈ (0, 1] and all such F.

## Key steps

1. U := thickening(1, K) is bounded, so A := Lⁿ(U).toReal is finite. b := Lⁿ(B(0,1)).toReal > 0. C := 2ⁿ·A/b, independent of r.
2. Lⁿ(B(z, r/2)) = ofReal((r/2)ⁿ)·Lⁿ(B(0,1)) (Measure.addHaar_ball_of_pos with finrank ℝⁿ = n).
3. For an r-separated F ⊆ K, the balls B(x, r/2), x ∈ F, are pairwise disjoint (triangle inequality) and lie in U (r/2 < 1).
4. Finite additivity and monotonicity give card(F)·ofReal((r/2)ⁿ)·Lⁿ(B(0,1)) ≤ Lⁿ(U). Applying toReal gives card(F)·((r/2)ⁿ·b) ≤ A.
5. card(F)·rⁿ·b = 2ⁿ·card(F)·(r/2)ⁿ·b ≤ 2ⁿ·A, hence card(F)·rⁿ ≤ C.

## Reference use

### local-project

Queries:
- `rg -n 'def maximalSeparatedSet|lemma isCover_maximalSeparatedSet|def packingNumber' mathlib/Mathlib/Topology/MetricSpace/CoveringNumbers.lean`
- `rg -n 'def IsSeparated|def IsCover|IsCover.of_maximal_isSeparated|isCover_iff_subset_iUnion_closedBall' mathlib/Mathlib/Topology/MetricSpace`
- `rg -n 'theorem addHaar_ball_of_pos|theorem finrank_euclideanSpace_fin|theorem measure_biUnion_finset |IsBounded.measure_lt_top|theorem mem_thickening_iff |IsBounded.thickening|theorem measure_ball_pos|theorem measure_ball_lt_top|theorem findGreatest_is_greatest|theorem card_insert_of_notMem|theorem dist_triangle_left|theorem le_floor |lemma le_div_iff₀|theorem pairwise_insert ' mathlib/Mathlib`
- `rg -n 'findGreatest_spec' mathlib/Mathlib/Data/Nat/Find.lean`
- `rg -n 'theorem coe_insert|theorem mem_insert ' mathlib/Mathlib/Data/Finset/Insert.lean`
- `rg -n 'abbrev Rn' project (Contract.lean l.48)`
- `rg -n -i 'separated|packing|maximalSeparated|closedBall_cover' project (no Lean match; only a Ch01 README row on Metric.AreSeparated)`
- `rg -n -g '*.lean' 'maximalSeparatedSet|packingNumber|IsSeparated' lake-packages-25730c7c/simongmt (no match)`
- `python3 -I gen_checks.py / gen_solutions.py (gmt-compare.child_modules in contract mode + lean_contract.validate_lean_statement) on the parent and both child statements`
- `lean NodeChallenge_{parent,packing,maxsep}.lean against a scratch olean of GMT.Ch02.Submission; lean NodeSolution_{parent,packing,maxsep}.lean against a scratch Submission containing the child proofs (#print axioms)`
- `lean LeafPacking.lean / LeafMaxSep.lean / Assembly.lean / FullFinal.lean (children proved verbatim; check_parent : frozen parent type; #print axioms)`
- `python3 -I: lean_name membership test of both proposed names over dag.json (110 nodes)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/CoveringNumbers.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Cover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/MetricSeparated.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Data/Nat/Find.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Data/Finset/Card.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Data/Finset/Insert.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Data/Set/Pairwise/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Algebra/Order/Floor/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-coarea-formula-a1-critical-fibers-euclidean-a1-ball-cover-count-a1/parent-child-handoff.json`
- `/tmp/ballcover-decomp/assembly/LeafPacking.lean`
- `/tmp/ballcover-decomp/assembly/LeafMaxSep.lean`
- `/tmp/ballcover-decomp/assembly/Assembly.lean`
- `/tmp/ballcover-decomp/assembly/FullFinal.lean`
- `/tmp/ballcover-decomp/sim/checks/NodeSolution_parent.lean`
- `/tmp/ballcover-decomp/sim/checks/NodeSolution_packing.lean`
- `/tmp/ballcover-decomp/sim/checks/NodeSolution_maxsep.lean`

Neither the project nor SimonGMT has a lemma for packing or covering counts. The project's only match is a Ch01 README row about Metric.AreSeparated, and the SimonGMT search returns no match. Rn is the abbrev at Contract.lean l.48.

The snapshot's Mathlib supplies every tool the children need:
- Measure.addHaar_ball_of_pos (EqHaar.lean l.445) and finrank_euclideanSpace_fin (PiL2.lean l.205);
- measure_biUnion_finset (Measure/Basic.lean l.150);
- Bornology.IsBounded.measure_lt_top (Typeclasses/Finite.lean l.357) and measure_ball_lt_top (l.373);
- measure_ball_pos (OpenPos.lean l.212);
- mem_thickening_iff (Thickening.lean l.143) and Bornology.IsBounded.thickening (l.164);
- dist_triangle_left (Pseudo/Defs.lean l.213);
- Nat.findGreatest_spec (Find.lean l.209) and Nat.findGreatest_is_greatest (l.246);
- Finset.card_insert_of_notMem (Card.lean l.103);
- Nat.le_floor (Floor/Defs.lean l.140) and le_div_iff₀ (GroupWithZero/Basic.lean l.1128).

Mathlib also offers an alternative route for child 2: maximalSeparatedSet (CoveringNumbers.lean l.288), isCover_maximalSeparatedSet (l.306) and packingNumber (l.80), plus IsCover.of_maximal_isSeparated (Cover.lean l.100, Vershynin 4.2.6) and isCover_iff_subset_iUnion_closedBall (l.131). That route needs ℝ≥0/ℝ≥0∞ radius conversions, so the supplied Nat.findGreatest argument is kept.

Both child statements pass validate_lean_statement, and their comparator-generated NodeChallenge modules compile in the replayed contract scope. In scratch, both children were proved verbatim and the frozen parent type was assembled from them. Simulated NodeSolution modules for the parent and both children compile, with axioms limited to propext, Classical.choice and Quot.sound. Neither proposed name is reserved among the 110 DAG nodes.
