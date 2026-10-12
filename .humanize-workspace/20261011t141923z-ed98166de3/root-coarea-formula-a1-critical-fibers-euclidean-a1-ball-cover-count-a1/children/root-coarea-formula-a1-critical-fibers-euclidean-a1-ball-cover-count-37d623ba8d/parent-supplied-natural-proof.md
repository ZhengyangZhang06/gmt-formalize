# Parent-supplied natural-language proof

- Parent DAG node: `root.coarea_formula-a1.critical_fibers_euclidean-a1.ball_cover_count-a1`
- Child DAG node: `root.coarea_formula-a1.critical_fibers_euclidean-a1.ball_cover_count-a1.maximal_separated_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3 and 4 of the parent-supplied proof of bounded_set_closedBall_cover_card_mul_pow_le. Those steps take an r-separated finite subset of maximal cardinality via Nat.findGreatest and show that maximality forces the closed-ball cover. Here the cardinality bound from parent step 2 is replaced by the hypothesis with bound N, and the parent's 0 < r is weakened to 0 ≤ r.
Work classically, so every predicate on ℕ is decidable and X has decidable equality. Call a finite F ⊆ X r-separated if r < dist(x, y) for all distinct x, y ∈ F.
1. For c ∈ ℕ let P(c) be the statement: there is a finite r-separated F ⊆ K with card(F) = c. P(0) holds with F = ∅, which is vacuously r-separated and a subset of K. If P(c) holds with witness F, the hypothesis gives c = card(F) ≤ N.
2. Let c₀ := Nat.findGreatest P N. Since 0 ≤ N and P(0) holds, Nat.findGreatest_spec gives P(c₀). Fix a witness: a finite r-separated F ⊆ K with card(F) = c₀.
3. P(c₀ + 1) fails. If c₀ + 1 ≤ N, this is Nat.findGreatest_is_greatest, since c₀ < c₀ + 1 ≤ N. If c₀ + 1 > N, then P(c₀ + 1) would give c₀ + 1 ≤ N by step 1, a contradiction.
4. F is already finite, r-separated and contained in K. It remains to show K ⊆ ⋃_{x∈F} B̄(x, r). Let a ∈ K, and suppose for contradiction that a ∉ B̄(x, r) for every x ∈ F, i.e. r < dist(a, x) for all x ∈ F.
5. Then a ∉ F. Otherwise step 4 with x = a gives r < dist(a, a) = 0, contradicting 0 ≤ r.
6. Let F' := insert a F = F ∪ {a}. F' is finite, and F' ⊆ K because a ∈ K and F ⊆ K. F' is r-separated: let x ≠ y in F'. If x, y ∈ F, use the r-separation of F. If x = a and y ∈ F, step 4 gives r < dist(a, y). If x ∈ F and y = a, step 4 gives r < dist(a, x) = dist(x, a) by symmetry of dist. The case x = y = a is excluded by x ≠ y. Since a ∉ F (step 5), card(F') = card(F) + 1 = c₀ + 1 (Finset.card_insert_of_notMem). So F' witnesses P(c₀ + 1).
7. Step 6 contradicts step 3. Hence every a ∈ K satisfies dist(a, x) ≤ r for some x ∈ F, i.e. a ∈ B̄(x, r), so K ⊆ ⋃_{x∈F} B̄(x, r). Together with step 2, F is a finite r-separated subset of K whose closed r-balls cover K, as required.

## Key steps

1. P(c) := 'some finite r-separated F ⊆ K has card c'. P(0) holds, and P(c) implies c ≤ N by hypothesis.
2. c₀ := Nat.findGreatest P N satisfies P(c₀) (Nat.findGreatest_spec). Fix a witness F.
3. ¬P(c₀+1): use Nat.findGreatest_is_greatest if c₀+1 ≤ N, and the bound c ≤ N otherwise.
4. If some a ∈ K had r < dist(a, x) for all x ∈ F, then a ∉ F (since 0 ≤ r), and insert a F would witness P(c₀+1).
5. Hence K ⊆ ⋃_{x∈F} closedBall x r, with F finite, r-separated and contained in K.

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
