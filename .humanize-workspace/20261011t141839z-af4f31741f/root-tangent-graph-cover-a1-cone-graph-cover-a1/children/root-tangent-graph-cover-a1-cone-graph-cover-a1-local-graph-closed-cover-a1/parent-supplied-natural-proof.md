# Parent-supplied natural-language proof

- Parent DAG node: `root.tangent_graph_cover-a1.cone_graph_cover-a1`
- Child DAG node: `root.tangent_graph_cover-a1.cone_graph_cover-a1.local_graph_closed_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent proof (closed pieces), i.e. the localization E_j ∩ B_{δ/4}(x_0) and the countable selection after printed (10) in Simon, Ch. 3, Thm 1.6 (p. 74), with closures taken to make the pieces closed. (In the parent it is applied to E := E_{m,k}, a uniform class, with r := 1/(2(k+1)), its hypothesis being the parent's step 4; the pieces are then the closures of E_{m,k} ∩ closedBall(d_j, 1/(4(k+1))).) Notation: p := Grassmannian.project P. By definition p u = P.projectionLinearMap u, so p is ℝ-linear and, being a linear map on the finite-dimensional space ℝ^N = Euclidean N, continuous (LinearMap.continuous_of_finiteDimensional). No hypothesis on L or n is used.

1. A dense sequence. Euclidean N is a finite-dimensional real normed space, hence a separable metric space, and it is nonempty (it contains 0). Hence d := TopologicalSpace.denseSeq (Euclidean N) : ℕ → ℝ^N has dense range (TopologicalSpace.denseRange_denseSeq).

2. The pieces. For j ∈ ℕ put S_j := E ∩ closedBall(d_j, r/2) and Γ_j := closure(S_j). Each Γ_j is closed (isClosed_closure). This is the first conclusion.

3. The graph relation is closed. Let F := {(y, z) ∈ ℝ^N × ℝ^N : ‖(y − z) − p(y − z)‖ ≤ L‖p(y − z)‖}. The maps (y, z) ↦ ‖(y − z) − p(y − z)‖ and (y, z) ↦ L‖p(y − z)‖ are continuous, being built from the continuous maps (y, z) ↦ y − z (continuous_fst.sub continuous_snd), p, vector subtraction, the norm and multiplication by the constant L. Hence F, the set where the first is ≤ the second, is closed (isClosed_le).

4. S_j × S_j ⊆ F. Let y, z ∈ S_j. Then ‖y − d_j‖ ≤ r/2 and ‖z − d_j‖ ≤ r/2 (mem_closedBall, dist_eq_norm), so ‖y − z‖ = ‖(y − d_j) − (z − d_j)‖ ≤ ‖y − d_j‖ + ‖z − d_j‖ ≤ r/2 + r/2 = r (norm_sub_le). Since y, z ∈ E and ‖y − z‖ ≤ r, the hypothesis gives ‖(y − z) − p(y − z)‖ ≤ L‖p(y − z)‖, i.e. (y, z) ∈ F.

5. The graph inequality on Γ_j. Let y, z ∈ Γ_j = closure(S_j). By closure_prod_eq, (y, z) ∈ closure(S_j) × closure(S_j) = closure(S_j × S_j), and by closure_minimal (with step 4 and the closedness of F from step 3) closure(S_j × S_j) ⊆ F. Hence (y, z) ∈ F, i.e. ‖(y − z) − p(y − z)‖ ≤ L‖p(y − z)‖. This is the second conclusion. (Lean note: first `have hmem := closure_minimal hsub hFc hyz` and then close the goal with `exact hmem`, optionally after `rw [Set.mem_ofPred_eq] at hmem`; a one-shot `exact closure_minimal …` can exhaust the heartbeat limit in isDefEq.)

6. Covering. Let x ∈ E. As r/2 > 0, DenseRange.exists_dist_lt (step 1) gives j ∈ ℕ with dist(x, d_j) < r/2. Then x ∈ closedBall(d_j, r/2), so x ∈ S_j ⊆ closure(S_j) = Γ_j (subset_closure). This is the third conclusion with i := j.

7. Hence Γ : ℕ → Set (Euclidean N), j ↦ closure(E ∩ closedBall(d_j, r/2)), satisfies all three conclusions. ∎

## Key steps

1. Take the dense sequence d_j := TopologicalSpace.denseSeq (Euclidean N) of the separable, nonempty space ℝ^N.
2. Define Γ_j := closure(E ∩ closedBall(d_j, r/2)); each Γ_j is closed.
3. The graph relation F = {(y,z) : ‖(y − z) − p(y − z)‖ ≤ L‖p(y − z)‖} is closed, since p is a continuous linear map (isClosed_le).
4. Points of E ∩ closedBall(d_j, r/2) are at distance ≤ r, so the hypothesis puts S_j × S_j inside F.
5. closure(S_j) × closure(S_j) = closure(S_j × S_j) ⊆ F gives the graph inequality on Γ_j.
6. Density gives, for each x ∈ E, some j with dist(x, d_j) < r/2, so x ∈ Γ_j.

## Reference use

### local-project

Queries:
- `cat local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum snapshot project/GMT/Ch08/Contract.lean, workspace GMT/Ch08/Contract.lean and GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487); sha256 of snapshot vs workspace .lake/packages/mathlib for Topology/Bases.lean, Basic/ENNReal/Inv.lean, Topology/Order/LeftRightNhds.lean, Topology/Constructions/SumProd.lean (identical); git rev-parse .lake/packages/mathlib (25730c7c…) and .lake/packages/simongmt (2b366308…)`
- `rg -c 'tgc_local_graph_closed_cover|tgc_eventual_density_bounds_uniform' local-references/5a882a57db723346 (exit 1: no match); grep of run dag.json and nodes/ (no match)`
- `rg -n '^theorem (exists_nat_one_div_lt|closure_prod_eq|isClosed_le|DenseRange.exists_dist_lt)\b|theorem exists_inv_nat_lt|theorem mem_nhdsGT_iff_exists_Ioo_subset|theorem ofReal_inv_of_pos|^def denseSeq|theorem denseRange_denseSeq|theorem closure_minimal' mathlib/Mathlib`
- `rg -n 'exists_nat_one_div_lt|DenseRange.exists_dist_lt|theorem continuous_of_finiteDimensional|theorem ofReal_mul |theorem ofReal_pow|theorem ofReal_le_ofReal_iff |theorem unpair_pair' mathlib/Mathlib`
- `grep -n 'abbrev Grassmannian|def projectionLinearMap|def project' simongmt Poincare/SimonGMT/Chapter08/Varifold.lean; rg -n 'Lipschitz graph|LipschitzGraph|lipschitz_graph|graph_cover' simongmt Chapter03 (no match); rg -n 'denseSeq|closure_prod_eq|exists_inv_nat_lt' simongmt`
- `grep -n 'Egoroff|(10)|graph|closure' book/sources/chapter-03-source.txt; sed -n 180,262p (printed (7)-(10) and the localization E_j ∩ B_{δ/4}(x_0), pp. 73-74)`
- `python3: contract_scope/child_modules from verifier/gmt-compare.py (replayed child scope and NodeChallenge generation); validate_lean_statement from verifier/lean_contract.py on both statements (pass)`
- `lake env lean /tmp/cgc-decomp/Probe.lean, Check.lean, Parent.lean, Full.lean, challenges/c1_NodeChallenge.lean, challenges/c2_NodeChallenge.lean (all exit 0; #print axioms = [propext, Classical.choice, Quot.sound])`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Constructions/SumProd.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Closure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Order/LeftRightNhds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Algebra/Order/Archimedean/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Data/Nat/Pairing.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-03-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-tangent-graph-cover-a1-cone-graph-cover-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-tangent-graph-cover-a1-cone-linear-algebra-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/cgc-decomp/Full.lean`
- `/tmp/cgc-decomp/Parent.lean`

The snapshot is project 63436ae6 plus Mathlib 25730c7c. Its Contract is byte-identical to the workspace Contract and Submission, and the cited Mathlib files are byte-identical to the workspace packages.

Neither tgc_local_graph_closed_cover nor tgc_eventual_density_bounds_uniform exists in the snapshot, in dag.json or in the run's nodes. SimonGMT has no Lipschitz-graph covering lemma, so neither child duplicates library or DAG content.

Mathlib supplies every tool the children and the parent assembly use:
- TopologicalSpace.denseSeq and denseRange_denseSeq (Topology/Bases.lean:373,378)
- DenseRange.exists_dist_lt (Topology/MetricSpace/Pseudo/Defs.lean:930)
- closure_prod_eq (Topology/Constructions/SumProd.lean:529)
- closure_minimal (Topology/Closure.lean:199)
- isClosed_le (Topology/Order/OrderClosed.lean:447)
- LinearMap.continuous_of_finiteDimensional (Topology/Algebra/Module/FiniteDimension.lean:284)
- ENNReal.exists_inv_nat_lt and ENNReal.ofReal_inv_of_pos (Basic/ENNReal/Inv.lean:650,945)
- ENNReal.ofReal_le_ofReal_iff, ofReal_mul and ofReal_pow (Basic/ENNReal/Real.lean:147,297,306)
- mem_nhdsGT_iff_exists_Ioo_subset (Topology/Order/LeftRightNhds.lean:104)
- exists_nat_one_div_lt (Algebra/Order/Archimedean/Basic.lean:211)
- Nat.unpair_pair (Data/Nat/Pairing.lean:60)

SimonGMT Chapter08/Varifold.lean:82-106 defines Grassmannian.project S x := S.projectionLinearMap x, which is linear and therefore continuous.

Both statements validate and elaborate in the comparator's replayed scope. Scratch proofs of both children with their exact frozen types compile. So does the exact frozen parent, proved from the two children plus the frozen sibling type tgc_tilted_cone_inclusion. All use only the axioms propext, Classical.choice and Quot.sound.
