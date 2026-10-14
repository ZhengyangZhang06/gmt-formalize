# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.convergence_tools-a1.vague_subseq-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.convergence_tools-a1.vague_subseq-a1.compact_exhaustion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 1, Theorem 4.16 (book/chapter-01.txt lines 1750-1760), first sentence of its proof (line 1763: “Let K_1, K_2, ... be an increasing sequence of compact sets with X = ∪_j K_j”), made explicit in step 1 of the parent proof (node vague_subseq) for X = U open in ℝ^P. The parent uses only the property that every compact subset of U lies in a single K_i, and that property is proved directly here. Monotonicity of the K_i is neither needed nor claimed. Notation: ‖·‖ is the Euclidean norm, dist(x, y) = ‖x − y‖, closedBall(0, r) := {x : ‖x‖ ≤ r}. For r ∈ ℝ and A ⊆ ℝ^P, thickening(r, A) := {x ∈ ℝ^P : ∃ y ∈ A, dist(x, y) < r} (Mathlib Metric.thickening, mem_thickening_iff). thickening(r, A) is open (isOpen_thickening), and thickening(r, ∅) = ∅.

Let P ∈ ℕ and let U ⊆ ℝ^P be open.

1. Definition. For i ∈ ℕ put K_i := closedBall(0, i) ∖ thickening((i+1)⁻¹, ℝ^P ∖ U). In Lean: K := fun i => closedBall (0 : Euclid P) i \ thickening ((i : ℝ) + 1)⁻¹ Uᶜ. No case distinction is needed. If U = ℝ^P, then ℝ^P ∖ U = ∅, its thickening is empty, and K_i = closedBall(0, i).

2. Each K_i is compact. ℝ^P is finite-dimensional, hence a proper metric space, so closedBall(0, i) is compact (Heine–Borel; isCompact_closedBall). The set thickening((i+1)⁻¹, ℝ^P ∖ U) is open by the notation paragraph. A compact set minus an open set is a closed subset of a compact set, hence compact (IsCompact.diff). So K_i is compact.

3. Each K_i ⊆ U. Let x ∈ K_i and suppose x ∉ U. Then x ∈ ℝ^P ∖ U and dist(x, x) = 0 < (i+1)⁻¹, so x ∈ thickening((i+1)⁻¹, ℝ^P ∖ U) (self_subset_thickening). This contradicts x ∈ K_i. Hence x ∈ U.

4. A uniform margin around a compact subset. Let C ⊆ ℝ^P be compact with C ⊆ U. Since C is compact, U is open and C ⊆ U, there is δ > 0 with thickening(δ, C) ⊆ U (IsCompact.exists_thickening_subset_open). Elementary justification: if C = ∅ take δ := 1. Otherwise, for each z ∈ C choose ρ_z > 0 with ball(z, 2ρ_z) ⊆ U, which is possible because U is open. Finitely many balls ball(z_1, ρ_{z_1}), …, ball(z_n, ρ_{z_n}) cover C; put δ := min_k ρ_{z_k} > 0. If y ∈ thickening(δ, C), pick x ∈ C with dist(y, x) < δ and k with dist(x, z_k) < ρ_{z_k}. Then dist(y, z_k) < δ + ρ_{z_k} ≤ 2ρ_{z_k}, so y ∈ U. Moreover C is bounded, because a compact subset of a metric space is bounded (IsCompact.isBounded). So there is R ∈ ℝ with C ⊆ closedBall(0, R) (Bornology.IsBounded.subset_closedBall).

5. Choice of the index. By the Archimedean property choose m ∈ ℕ with m ≥ max(R, δ⁻¹) (exists_nat_ge). Then m ≥ R, and m + 1 > m ≥ δ⁻¹ > 0, so (m+1)⁻¹ < δ.

6. C ⊆ K_m. Let x ∈ C.
   (a) By step 4, ‖x‖ ≤ R ≤ m, so x ∈ closedBall(0, m) (mem_closedBall_zero_iff).
   (b) Suppose x ∈ thickening((m+1)⁻¹, ℝ^P ∖ U). Then there is y ∉ U with dist(x, y) < (m+1)⁻¹ < δ. So dist(y, x) = dist(x, y) < δ with x ∈ C, which gives y ∈ thickening(δ, C) ⊆ U. This contradicts y ∉ U. Hence x ∉ thickening((m+1)⁻¹, ℝ^P ∖ U).
   By (a) and (b), x ∈ K_m.

7. Conclusion. Each K_i is compact (step 2) and contained in U (step 3). Every compact C ⊆ U is contained in K_m for the m chosen in step 5 (step 6). This is the statement, with K := (K_i)_{i∈ℕ}. ∎

## Key steps

1. Define K_i := closedBall(0, i) ∖ thickening((i+1)⁻¹, ℝ^P ∖ U).
2. K_i is compact: a compact closed ball minus an open thickening (isCompact_closedBall, isOpen_thickening, IsCompact.diff).
3. K_i ⊆ U: a point outside U lies in the (i+1)⁻¹-thickening of ℝ^P ∖ U (self_subset_thickening).
4. For compact C ⊆ U pick δ > 0 with thickening(δ, C) ⊆ U (IsCompact.exists_thickening_subset_open) and R with C ⊆ closedBall(0, R).
5. Choose m ∈ ℕ with m ≥ max(R, δ⁻¹), so (m+1)⁻¹ < δ; then each x ∈ C has ‖x‖ ≤ m and no y ∉ U within (m+1)⁻¹ of x, hence C ⊆ K_m.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); diff snapshot project/GMT/Ch07/Submission.lean and Contract.lean against workspace GMT/Ch07/Submission.lean (identical)`
- `rg -n -i 'diagonal|exhaustion|StrictMono|thickening' snapshot project/GMT (only frozen contract statements, no helper lemmas)`
- `rg -n 'theorem extraction|lemma extraction' and rg -n diagonal in snapshot mathlib/Mathlib/Order/Filter, Mathlib/Topology (only Filter.extraction_of_frequently_atTop / extraction_forall_of_* single-predicate extractions; no diagonal-subsequence lemma)`
- `rg -n 'structure CompactExhaustion|theorem exists_superset_of_isCompact|exists_thickening_subset_open' snapshot mathlib (CompactExhaustion in Topology/Compactness/SigmaCompact.lean; IsCompact.exists_thickening_subset_open in Topology/MetricSpace/Thickening.lean)`
- `rg -n -i helly snapshot mathlib (only the convex-geometry Helly theorem in Analysis/Convex/Radon.lean; no measure selection theorem)`
- `grep -rn simon_theorem_4_16 in the pinned simongmt package (Chapter01/CompactMetrizableCompactness.lean simon_theorem_4_16_compact_metrizable; Chapter01/SequentialCompactnessCounterexample.lean simon_theorem_4_16_counterexample); rg diagonal/StrictMono theorems in simongmt (no diagonal lemma)`
- `python3 scan of dag.json: lean_name exact and substring matches for cbr_ct_vs_compact_exhaustion, cbr_ct_vs_compact_piece_subseq, cbr_ct_vs_diagonal_subseq (none); titles, statements and names mentioning diagonal/exhaust/StrictMono (dor_lmbs_tfa_compact_exhaustion decomposing, identical statement to child 1; cmc_fc_cs_diagonal_subseq accepted, different clique-diagonal statement)`
- `git grep -l -E 'cbr_ct_vs_|cbr_vs_' over all git refs in GMT/*.lean, in 400-ref chunks (no match)`
- `verifier/gmt-compare.py contract_scope(contract, 'GMT.Ch07.main_theorem') replay and child_modules challenge layout; verifier/lean_contract.py validate_lean_statement on the three child strings (all pass)`
- `lake env lean /tmp/cbr-vs-decomp-q7k2/lean/{ExactTypes,ExactAssembly,ExactProofs,Avail,Names}.lean (statements elaborate; assembly and full scratch proofs compile; #print axioms: propext, Classical.choice, Quot.sound; every cited lemma and instance exists)`
- `sed -n 1740,1782p book/chapter-01.txt and grep -n for the proof sentences (Simon 1.4.16 statement lines 1750-1760, proof 1763-1778: exhaustion at 1763, single-piece Alaoglu at 1765-1767, diagonal at 1767-1768)`
- `independent reviewer subagent over /tmp/cbr-vs-decomp-q7k2/draft/subproblems.json (verdict ACCEPT; citation line numbers corrected); flow runtime.py _existing_lean_name_problem compares lean_name only`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convex/Radon.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/CompactMetrizableCompactness.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/SequentialCompactnessCounterexample.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-b85187fcb1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-t-86c8782c4f/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/tmp/cbr-vs-decomp-q7k2/lean/ExactTypes.lean`
- `/tmp/cbr-vs-decomp-q7k2/lean/ExactAssembly.lean`
- `/tmp/cbr-vs-decomp-q7k2/lean/ExactProofs.lean`
- `/tmp/cbr-vs-decomp-q7k2/draft/subproblems.json`

No accepted declaration proves this node or any of the three children. The snapshot project contains only frozen contracts. Snapshot Mathlib has no diagonal-subsequence lemma (only the single-predicate Filter.extraction_* lemmas) and no Helly or vague selection theorem. It does provide CompactExhaustion and IsCompact.exists_thickening_subset_open. SimonGMT provides the corrected simon_theorem_4_16_compact_metrizable (compact, metrizable, Borel, no nonemptiness assumption), which child 2 uses. It needs `import Poincare.SimonGMT.Chapter01.CompactMetrizableCompactness`, checked to load with GMT.Ch07.Submission. The DAG node dor_lmbs_tfa_compact_exhaustion (decomposing, other parent) has a statement byte-identical to child 1. It is not reusable because it is unaccepted and under another parent, so child 1 uses the fresh name cbr_ct_vs_compact_exhaustion. The accepted cmc_fc_cs_diagonal_subseq is a different clique-diagonal lemma and does not apply. The three proposed names are unused in dag.json and in all git refs. Every child string elaborates in the replayed contract scope and passes the lexical validator. The hypothesis-only assembly of the exact frozen parent type compiles, and full scratch proofs of all three children compile, with axioms propext, Classical.choice and Quot.sound. Book anchors: Simon 1.4.16 statement at lines 1750-1760 and proof at 1763-1778 (exhaustion 1763, single-piece Alaoglu step 1765-1767, diagonal 1767-1768).
