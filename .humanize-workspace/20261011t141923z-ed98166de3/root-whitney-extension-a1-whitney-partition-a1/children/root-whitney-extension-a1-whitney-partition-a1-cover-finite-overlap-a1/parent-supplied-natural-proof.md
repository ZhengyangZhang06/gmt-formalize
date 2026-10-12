# Parent-supplied natural-language proof

- Parent DAG node: `root.whitney_extension-a1.whitney_partition-a1`
- Child DAG node: `root.whitney_extension-a1.whitney_partition-a1.cover_finite_overlap-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1-5 (facts (F1)-(F3)) of the parent-supplied proof of whitney_smooth_partition_of_unity (Simon, Introduction to GMT, Ch. 2, Theorem 1.6, proof supplied after [EG92]), extracted as a stand-alone lemma. The parent's step 4 bounds the overlap twice: once by a measure comparison and once ("Equivalently") by a separated-set count. Here the separated-set version is written out in full, with the packing fact it uses, and it is also used for the finiteness of J'(x) (the parent's step 5).

Notation:
- ℝⁿ = EuclideanSpace ℝ (Fin n), with Euclidean norm |·|.
- B(x,ρ) and B̄(x,ρ) are the open and closed balls.
- d(x) := Metric.infDist x A and r(x) := min{1, d(x)}/20.
- J(x) := {s ∈ J : |x − s| < 10r(s)}.
- J'(x) := {s ∈ J : ∃ z ∈ ℝⁿ, |z − s| < 10r(s) and |z − x| < r(x)}.

Claim. Let A ⊆ ℝⁿ be closed and nonempty. Then there are J ⊆ ℝⁿ and N ∈ ℕ such that:
- (C1) J ⊆ ℝⁿ∖A;
- (C2) every x ∉ A has some s ∈ J with |x − s| ≤ 5r(s);
- (C3) for every x ∉ A, J(x) is finite and #J(x) ≤ N;
- (C4) for every x ∉ A, J'(x) is finite.

Proof.

1. Distance and scale. A is closed and nonempty, so d(x) ≥ 0 and |d(x) − d(y)| ≤ |x − y| (lipschitz_infDist_pt). Also x ∉ A ⇔ d(x) > 0 (IsClosed.notMem_iff_infDist_pos). The map t ↦ min{1, t} is 1-Lipschitz, so:
   - 0 ≤ r(x) ≤ 1/20 for every x;
   - r(x) > 0 for every x ∉ A;
   - |r(x) − r(y)| ≤ |x − y|/20 for all x, y.

2. (F1) Comparable radii. Let x, s ∈ ℝⁿ with |x − s| ≤ 10r(s). Then |r(x) − r(s)| ≤ |x − s|/20 ≤ r(s)/2, so r(s)/2 ≤ r(x) ≤ 3r(s)/2. That is, (2/3)r(x) ≤ r(s) ≤ 2r(x).

3. Vitali selection; (C1) and (C2). Apply Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall with index set U := ℝⁿ∖A, centres x ↦ x, radii r, bound R := 1/20 (valid by step 1) and τ := 5 > 3. This gives J ⊆ ℝⁿ∖A such that:
   - the closed balls B̄(s, r(s)), s ∈ J, are pairwise disjoint;
   - every x ∉ A has some s ∈ J with B̄(x, r(x)) ⊆ B̄(s, 5r(s)).
   Since r(x) ≥ 0, x ∈ B̄(x, r(x)), hence |x − s| ≤ 5r(s). This gives (C1) and (C2). If A = ℝⁿ (in particular if n = 0), then U = ∅, J = ∅, and (C2)-(C4) hold vacuously.

4. Separation. If s, s' ∈ J and s ≠ s', then |s − s'| > r(s). Otherwise s' ∈ B̄(s, r(s)). Also s' ∈ B̄(s', r(s')) because r(s') ≥ 0. This contradicts the disjointness of B̄(s, r(s)) and B̄(s', r(s')).

5. Packing lemma. Let K ⊆ ℝⁿ be compact and δ > 0. Then there is N(K, δ) ∈ ℕ such that every S ⊆ K whose distinct points are at distance ≥ δ from each other is finite with #S ≤ N(K, δ). Proof: K is totally bounded, so there is a finite T ⊆ ℝⁿ with K ⊆ ⋃_{q∈T} B(q, δ/2) (Metric.totallyBounded_iff). For y ∈ S choose q(y) ∈ T with |y − q(y)| < δ/2. If q(y) = q(y'), then |y − y'| < δ, so y = y'. Thus y ↦ q(y) is an injection S → T. So S is finite and #S ≤ #T =: N(K, δ).

6. (F2) Uniform overlap bound; (C3). Let N := N(B̄(0, 20), 2/3) from step 5. It does not depend on x. Fix x ∉ A, so r(x) > 0 by step 1. Let f(c) := (c − x)/r(x); f is injective and |f(c) − f(c')| = |c − c'|/r(x).
   - Let s ∈ J(x). Since |x − s| < 10r(s), step 2 gives (2/3)r(x) ≤ r(s) ≤ 2r(x). Hence |f(s)| = |s − x|/r(x) < 10r(s)/r(x) ≤ 20.
   - For distinct s, s' ∈ J(x), step 4 gives |f(s) − f(s')| = |s − s'|/r(x) > r(s)/r(x) ≥ 2/3.
   So f(J(x)) is a subset of B̄(0, 20) whose distinct points are at distance ≥ 2/3. By step 5 it is finite with at most N elements. Since f is injective, J(x) is finite and #J(x) ≤ N.

7. (F3) Local finiteness; (C4). Fix x ∉ A, put ρ := r(x) > 0 and f(c) := (c − x)/ρ.
   - Let s ∈ J'(x), witnessed by z with |z − s| < 10r(s) and |z − x| < ρ. Step 2 at z gives (2/3)r(z) ≤ r(s) ≤ 2r(z). Step 1 gives |r(z) − ρ| ≤ |z − x|/20 < ρ/20, so (19/20)ρ < r(z) < (21/20)ρ.
   - Therefore r(s) > (2/3)(19/20)ρ > ρ/2 and r(s) < 2(21/20)ρ < 3ρ.
   - Hence |s − x| ≤ |s − z| + |z − x| < 10r(s) + ρ < 31ρ, so f(s) ∈ B̄(0, 31).
   - For distinct s, s' ∈ J'(x), step 4 gives |f(s) − f(s')| = |s − s'|/ρ > r(s)/ρ > 1/2.
   By step 5 (with K = B̄(0, 31) and δ = 1/2), f(J'(x)) is finite. Since f is injective, J'(x) is finite.

8. Conclusion. J and N satisfy (C1)-(C4). ∎

Remarks for formalization.
(i) The intended route is the packing argument of steps 5-7. A Lean proof of this exact statement along these lines was kernel-checked during decomposition. For information only, the parent's step 4 also compares Lebesgue measures: the balls B̄(s, r(s)), s ∈ J(x), are pairwise disjoint, lie in B̄(x, 22r(x)) and have radius ≥ (2/3)r(x), so #J(x) ≤ 33ⁿ, and similarly #J'(x) ≤ 68ⁿ.
(ii) Useful Mathlib names:
   - Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall;
   - Metric.totallyBounded_iff, isCompact_closedBall, IsCompact.totallyBounded;
   - lipschitz_infDist_pt, LipschitzWith.const_min, IsClosed.notMem_iff_infDist_pos;
   - Set.Finite.of_finite_image, Set.ncard_image_of_injective, Nat.card_le_card_of_injective.
(iii) The pinned SimonGMT file Poincare/SimonGMT/Chapter02/WhitneyCover.lean implements the same argument in TotallyBounded.exists_uniform_separated_bound and exists_whitneyBallCover_overlap_bound. It uses r = min{1,d}/100 and the open-ball Vitali lemma with τ = 4. Adapt its source to the constants above. Do not import it: its prebuilt .olean files are stale for Lake.

## Key steps

1. Scale r = min{1,d}/20: 0 ≤ r ≤ 1/20, r > 0 off A, |r(x) − r(y)| ≤ |x − y|/20; comparable radii (F1): |x − s| ≤ 10r(s) ⇒ (2/3)r(x) ≤ r(s) ≤ 2r(x).
2. Vitali (closed balls, R = 1/20, τ = 5) on ℝⁿ∖A gives J ⊆ ℝⁿ∖A with pairwise disjoint B̄(s, r(s)) and, for every x ∉ A, some s ∈ J with |x − s| ≤ 5r(s); disjointness gives |s − s'| > r(s) for distinct s, s' ∈ J.
3. Packing lemma: a δ-separated subset of a fixed compact set injects into a finite δ/2-net, so it is finite with uniformly bounded cardinality.
4. Rescaling by r(x): J(x) maps injectively into a (2/3)-separated subset of B̄(0,20), giving the uniform bound N; J'(x) maps injectively into a (1/2)-separated subset of B̄(0,31), giving finiteness.

## Reference use

### local-project

Queries:
- `cat local-references/ff09f3909baeeae7/manifest.json (project 1b1689a8, mathlib 25730c7c)`
- `cmp GMT/Ch02/Contract.lean GMT/Ch02/Submission.lean; cmp GMT/Ch02/Contract.lean local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `sed -n 140,215p mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean (exists_disjoint_subfamily_covering_enlargement_closedBall / _ball)`
- `grep -n -A6 'theorem ContDiff.lipschitzWith_of_hasCompactSupport' mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean; grep -n -A4 'theorem norm_fderiv_le_of_lipschitz' mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `grep -n 'exists_infDist_eq_dist|notMem_iff_infDist_pos|infDist_le_infDist_add_dist|lipschitz_infDist_pt|infDist_le_dist_of_mem' mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `grep -n 'one_of_mem_closedBall|support_eq|nonneg|le_one|protected theorem contDiff|hasCompactSupport' mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `grep -n '^theorem|^def|^structure' simongmt/Poincare/SimonGMT/Chapter02/WhitneyCover.lean; full reads of WhitneyCover.lean, WhitneyPartition.lean, WhitneyJet.lean; grep -n 'dist_near_anchor_le' WhitneyExtension.lean`
- `python3 -I over dag.json (node ids, lean_name); grep -rhoE '"lean_name": *"[^"]*"' and 'whitney[A-Za-z0-9_]*' over run *.json`
- `python3 -I gen.py: gmt-compare.py child_modules(contract mode) + lean_contract.validate_lean_statement -> NodeChallenge_{parent,cover,partition}.lean / NodeSolution_*.lean`
- `lean -R src -o build/GMT/Ch02/Submission.olean (scratch olean of frozen Submission); lean NodeChallenge_{parent,cover,partition}.lean`
- `lean AssemblyCheck.lean; lean CoverCheck.lean; lean PartitionCheck.lean; lean SolutionCheck_{cover,partition}.lean; lean EndToEnd.lean; #print axioms`
- `git status --short (workspace); find simongmt Chapter02 source and build dirs -newer stmts.json (no changes)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/GMT/Ch02/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyPartition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-whitney-extension-a1-whitney-partition-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-whitney-extension-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-whitney-extension-a1/decomposition-scope-v1.json`
- `/tmp/wpou-decomp-check/gen/NodeChallenge_parent.lean`
- `/tmp/wpou-decomp-check/gen/NodeChallenge_cover.lean`
- `/tmp/wpou-decomp-check/gen/NodeChallenge_partition.lean`
- `/tmp/wpou-decomp-check/asm/AssemblyCheck.lean`
- `/tmp/wpou-decomp-check/asm/EndToEnd.lean`
- `/tmp/wpou-decomp-check/truth/CoverCheck.lean`
- `/tmp/wpou-decomp-check/truth/PartitionCheck.lean`
- `/tmp/wpou-decomp-check/gen/SolutionCheck_cover.lean`
- `/tmp/wpou-decomp-check/gen/SolutionCheck_partition.lean`

Contract and library:
- The snapshot Contract.lean is byte-identical to the workspace contract and to Submission.lean.
- Mathlib 25730c7c has no Whitney covering lemma and no Whitney partition-of-unity lemma, but supplies every tool both children use:
  - Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall (Vitali.lean:158);
  - ContDiffBump with one_of_mem_closedBall, support_eq, nonneg, le_one, contDiff and hasCompactSupport (BumpFunction/Basic.lean:137-209);
  - ContDiff.lipschitzWith_of_hasCompactSupport (RCLike.lean:156) and norm_fderiv_le_of_lipschitz (FDeriv/Basic.lean:947);
  - IsClosed.exists_infDist_eq_dist (:615), IsClosed.notMem_iff_infDist_pos (:584), infDist_le_infDist_add_dist (:518) and lipschitz_infDist_pt (:547), all in HausdorffDistance.lean.

SimonGMT:
- WhitneyCover.lean contains TotallyBounded.exists_uniform_separated_bound and exists_whitneyBallCover_overlap_bound.
- WhitneyPartition.lean contains whitneyBump, whitneyBumpSum, whitneyWeight and exists_sum_norm_fderiv_whitneyWeight_bound.
- WhitneyJet.lean (nearest anchor) and WhitneyExtension.lean (dist_near_anchor_le) cover the anchors.
- Together they implement the same construction with constants 1/100, τ = 4 and bump radii 4 < 8. They are templates for the two children, to be ported rather than imported (stale oleans).

Checks on the proposed split:
- Both child statements validate and elaborate in the verifier-generated contract scope.
- AssemblyCheck derives the frozen parent type from them.
- CoverCheck and PartitionCheck give complete kernel-checked proofs of the exact child types, accepted through comparator-style NodeSolution modules.
- EndToEnd proves the frozen parent from these proofs.
- Every check uses only the axioms propext, Classical.choice and Quot.sound.
- Neither proposed name, whitney_cover_finite_overlap or whitney_partition_of_finite_overlap_cover, is reserved anywhere in the run.
- The workspace git status is clean and the shared simongmt tree is untouched.
