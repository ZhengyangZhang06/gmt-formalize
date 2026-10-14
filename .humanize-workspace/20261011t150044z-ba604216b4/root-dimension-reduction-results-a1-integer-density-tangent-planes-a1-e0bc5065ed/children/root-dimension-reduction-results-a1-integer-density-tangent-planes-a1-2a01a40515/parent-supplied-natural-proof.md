# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.class_reduction-a1.nonflat_usc-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.class_reduction-a1.nonflat_usc-a1.flat_point_persists-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 5, 6, 7 and 8 of the supplied proof of idtp_fons_cr_nonflat_usc. This is Simon's claim in 7.3.3, proof of 3.3(2) (chapter-07.txt lines 539–541): if y ∈ R_β(S), y_j ∈ spt S_j and y_j → y, then y_j ∈ R_β(S_j) for all large j. Here it is stated for an arbitrary sequence v_i → w along a strictly increasing σ. Step 7 is the sibling lemma flat_eventually.

Notation. B_r(x) is the open ball; q_Q(u) := u − p_Q(u), with p_Q = Q.starProjection.

Sibling lemma used (flat_eventually, i.e. Submission.idtp_fons_cr_nusc_flat_eventually). Assume (H). Suppose:
- w ∈ ℝ^P, ρ, ρ', s, τ ∈ ℝ and Q is a linear subspace;
- ρ' < ρ, B_ρ(w) ⊆ D, s < τ, and |q_Q(y − w)| ≤ s for every y ∈ S ∩ B_ρ(w);
- σ : ℕ → ℕ is strictly increasing and v_i → w.
Then for all sufficiently large i, |q_Q(y − v_i)| ≤ τ for every y ∈ S_{σ(i)} ∩ B_{ρ'}(v_i).

1. (Witness at w.) Fix ρ > 0 with B_ρ(w) ⊆ D, a linear subspace Q with dim Q = n, and s < βρ with |q_Q(y − w)| ≤ s for every y ∈ S ∩ B_ρ(w).
2. (Parameters.)
   - Since β > 0, s < βρ gives s/β < ρ (div_lt_iff₀). As also 0 < ρ, m := max(s/β, 0) < ρ.
   - Put ρ' := (ρ + m)/2. Then m < ρ' < ρ. Since m ≥ 0, ρ' > 0. Since s/β ≤ m < ρ', s/β < ρ', hence s < βρ'.
   - Put τ := (s + βρ')/2, so s < τ < βρ'.
   - Put η := (ρ − ρ')/2 > 0. Then ρ' + η = (ρ + ρ')/2 < ρ.
3. (Domains for large i.) Let K := closedBall w (ρ' + η).
   - K is compact (isCompact_closedBall). As ρ' + η < ρ, K ⊆ B_ρ(w) ⊆ D (closedBall_subset_ball).
   - By (E), K ⊆ D_k for all sufficiently large k. Since σ is strictly increasing, σ(i) → ∞ (StrictMono.tendsto_atTop), so K ⊆ D_{σ(i)} for all sufficiently large i (Tendsto.eventually).
   - Since v_i → w and η > 0, |v_i − w| < η for all sufficiently large i (Metric.tendsto_nhds).
   - Take any i with both properties and any x ∈ B_{ρ'}(v_i). Then |x − w| ≤ |x − v_i| + |v_i − w| < ρ' + η, so x ∈ K ⊆ D_{σ(i)}.
   Hence B_{ρ'}(v_i) ⊆ D_{σ(i)} for all sufficiently large i.
4. (Flatness for large i.) Apply flat_eventually to S, D, (S_k), (H), w, ρ, ρ', s, τ, Q, σ, v. Its hypotheses hold:
   - ρ' < ρ (step 2) and B_ρ(w) ⊆ D (step 1);
   - s < τ (step 2) and |q_Q(y − w)| ≤ s on S ∩ B_ρ(w) (step 1);
   - σ is strictly increasing and v_i → w.
   It gives: for all sufficiently large i, |q_Q(y − v_i)| ≤ τ for every y ∈ S_{σ(i)} ∩ B_{ρ'}(v_i).
5. (Conclusion.) The set of i satisfying the conclusions of both step 3 and step 4 is again eventual, being the intersection of two eventually-true properties (filter_upwards). For each such i take ρ_i := ρ', Q_i := Q and s_i := τ:
   - ρ' > 0 (step 2) and B_{ρ'}(v_i) ⊆ D_{σ(i)} (step 3);
   - dim Q = n (step 1) and τ < βρ' (step 2);
   - |(y − v_i) − p_Q(y − v_i)| ≤ τ for every y ∈ S_{σ(i)} ∩ B_{ρ'}(v_i) (step 4).
   Hence v_i is β-flat for (S_{σ(i)}, D_{σ(i)}) for all sufficiently large i. ∎

## Key steps

1. Take the witness (ρ, Q, s) at w. Choose ρ' = (ρ + max(s/β, 0))/2 ∈ (0, ρ) with s < βρ', τ = (s + βρ')/2 ∈ (s, βρ'), and η = (ρ − ρ')/2.
2. Compact exhaustion applied to K = closedBall w (ρ' + η) ⊆ B_ρ(w) ⊆ D, together with σ(i) → ∞ and |v_i − w| < η, gives B_{ρ'}(v_i) ⊆ D_{σ(i)} for large i.
3. The sibling flat_eventually gives |q_Q(y − v_i)| ≤ τ on S_{σ(i)} ∩ B_{ρ'}(v_i) for large i.
4. For large i, (ρ', Q, τ) witnesses that v_i is β-flat for (S_{σ(i)}, D_{σ(i)}).

## Reference use

### local-project

Queries:
- `python3 -I json.load of nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-e0bc5065ed/parent-child-handoff.json (subproblem.lean_statement, natural_proof, audit) and dag.json (selected node depth 5 status decomposing; siblings under ...class_reduction-a1; lean_name list; lean_statement equality search for both child types; nodes whose lean_statement mentions starProjection)`
- `sed -n 512,583p book/chapter-07.txt; sed -n 1,60p book/chapter-A.txt; grep -n 'A.3(3)' nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-ff027afbd6/parent-supplied-natural-proof.md`
- `grep -rn 'theorem extraction_of_frequently_atTop|theorem IsCompact.tendsto_subseq|StrictMono.tendsto_atTop|def starProjection|class HasOrthogonalProjection|instance.*HasOrthogonalProjection|isCompact_closedBall' over local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -c idtp_fons_cr_nusc dag.json; rg -l idtp_fons_cr_nusc nodes decomposition-reopenings operator-dependency-edits; ls .swarm-worktrees/*/gmt-ch07/GMT/Ch07/*.lean | xargs -P 16 grep -l idtp_fons_cr_nusc (662 dirs, exit 123 = no match)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD`
- `lake env lean /tmp/nusc-split-ch07/check/Probe.lean; lake env lean /tmp/nusc-split-ch07/check/Full.lean; lake env lean /tmp/nusc-split-ch07/check/Full2.lean; lake env lean /tmp/nusc-split-ch07/check/Layout.lean (with set_option pp.explicit true #check of Q.starProjection)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Tendsto.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/ProperSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-e0bc5065ed/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-e0bc5065ed/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-ff027afbd6/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-ff027afbd6/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-A.txt`
- `/tmp/nusc-split-ch07/gen/statements.json`
- `/tmp/nusc-split-ch07/check/Probe.lean`
- `/tmp/nusc-split-ch07/check/Full2.lean`
- `/tmp/nusc-split-ch07/check/Layout.lean`

Pins match.
- The manifest records project b4d606db, which is the workspace HEAD, and Mathlib 25730c7c, which is the checkout under .lake/packages.
- The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

No existing declaration can be reused.
- No DAG node has either proposed child type.
- The prefix idtp_fons_cr_nusc has no hits in dag.json, in nodes/, or in any worktree GMT/Ch07 Lean file, so both names are fresh.
- Related nodes exist but are different: the sibling nonflat_closed and nonflat_affine_preimage.

Library facts used, all from the snapshot Mathlib:
- Filter.extraction_of_frequently_atTop (AtTopBot/Basic.lean:114);
- IsCompact.tendsto_subseq (Topology/Sequences.lean:298);
- StrictMono.tendsto_atTop (AtTopBot/Tendsto.lean:84);
- ProperSpace.isCompact_closedBall (ProperSpace.lean:39–41);
- Submodule.starProjection, a continuous linear map E →L[𝕜] E (Projection/Basic.lean:131);
- HasOrthogonalProjection is a Prop class (line 48), found via ofCompleteSpace (line 53), so instance choice cannot change meaning.

The book confirms that Simon's claim, 'y ∈ R_β(S), y_j ∈ spt S_j, y_j → y ⇒ y_j ∈ R_β(S_j) for large j' (chapter-07.txt 539–541), is a separately stated step. That step is the child flat_point_persists.

Lean results:
- Both child types and the frozen parent type elaborate (Probe.lean and Layout.lean).
- Layout.lean exits 0. It kernel-checks the children and the exact frozen parent type: the parent uses only child 2, and child 2 uses only child 1.
- Every declaration in it depends only on propext, Classical.choice and Quot.sound.
- An independent reviewer reproduced these checks and an axiom-assembly check.
