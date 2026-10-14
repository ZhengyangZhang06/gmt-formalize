# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.class_reduction-a1.nonflat_usc-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.class_reduction-a1.nonflat_usc-a1.flat_eventually-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 7 of the supplied proof of idtp_fons_cr_nonflat_usc (Simon 7.3.3, proof of 3.3(2), chapter-07.txt lines 539–541; Appendix A.3(3)). Here it is stated for an arbitrary sequence v_i → w along an arbitrary strictly increasing σ. The supplied step bounded the bad points y_l using |v_i| < 1. No such bound is assumed here, so the bounded displacements d_l = y_l − v_{ψ(l)} are used instead.

Notation. B_r(x) is the open ball. For u ∈ ℝ^P put q_Q(u) := u − p_Q(u) and g(u) := |q_Q(u)|. Since p_Q = Q.starProjection is a continuous linear map ℝ^P → ℝ^P, q_Q is continuous (continuous_id.sub Q.starProjection.continuous), and hence so is g : ℝ^P → ℝ (Continuous.norm).

1. (Contradiction hypothesis.) Suppose the conclusion fails.
   - By Filter.not_eventually, the property 'g(y − v_i) ≤ τ for every y ∈ S_{σ(i)} ∩ B_{ρ'}(v_i)' fails for frequently many i (∃ᶠ i in atTop).
   - By Filter.extraction_of_frequently_atTop there is a strictly increasing ψ : ℕ → ℕ such that the property fails at i = ψ(l) for every l ∈ ℕ.
   - Pushing the negation and choosing, for every l we get y_l with y_l ∈ S_{σ(ψ(l))}, y_l ∈ B_{ρ'}(v_{ψ(l)}) (i.e. |y_l − v_{ψ(l)}| < ρ') and τ < g(y_l − v_{ψ(l)}).
2. (Compactness of the displacements.) Put d_l := y_l − v_{ψ(l)}.
   - Then |d_l| < ρ', so d_l ∈ closedBall 0 ρ' for every l.
   - Closed balls in ℝ^P are compact (proper space; isCompact_closedBall).
   - So IsCompact.tendsto_subseq gives d ∈ closedBall 0 ρ' and a strictly increasing χ : ℕ → ℕ with d_{χ(m)} → d as m → ∞. In particular |d| ≤ ρ'.
3. (The limit point.)
   - ψ ∘ χ is strictly increasing (StrictMono.comp), so it tends to ∞ (StrictMono.tendsto_atTop).
   - Composing with v_i → w gives u_m := v_{ψ(χ(m))} → w.
   - Since y_{χ(m)} = u_m + d_{χ(m)} for every m, Tendsto.add gives y_{χ(m)} → w + d =: y'.
4. (y' ∈ D.) |y' − w| = |d| ≤ ρ' < ρ, so y' ∈ B_ρ(w) ⊆ D.
5. (y' ∈ S.) Apply hypothesis (H) with sub = σ', z = (z_m) and x = y', where:
   - σ' := σ ∘ ψ ∘ χ is strictly increasing;
   - z_m := y_{χ(m)} ∈ S_{σ(ψ(χ(m)))} = S_{σ'(m)} for every m, by step 1;
   - z_m → y' by step 3, and y' ∈ D by step 4.
   This gives y' ∈ S.
6. (Flatness at the limit.) By steps 4 and 5, y' ∈ S ∩ B_ρ(w). Since y' − w = d, the flatness hypothesis at w gives g(d) = |(y' − w) − p_Q(y' − w)| ≤ s.
7. (Contradiction.)
   - By continuity of g and step 2, g(d_{χ(m)}) → g(d).
   - Since τ < g(d_{χ(m)}) for every m (step 1), the limit satisfies τ ≤ g(d) (ge_of_tendsto).
   - With step 6, τ ≤ g(d) ≤ s < τ, which is impossible.
   Hence the conclusion holds. ∎

## Key steps

1. Assume eventual τ-flatness fails. Extract a strictly increasing ψ and points y_l ∈ S_{σ(ψ(l))} ∩ B_{ρ'}(v_{ψ(l)}) with |q_Q(y_l − v_{ψ(l)})| > τ.
2. The displacements d_l = y_l − v_{ψ(l)} lie in the compact closedBall 0 ρ'. A strictly increasing χ gives d_{χ(m)} → d with |d| ≤ ρ', so y_{χ(m)} → y' := w + d ∈ B_ρ(w) ⊆ D.
3. The support hypothesis along the strictly increasing σ ∘ ψ ∘ χ gives y' ∈ S, so flatness at w gives |q_Q(d)| ≤ s.
4. Continuity of u ↦ |u − p_Q u| gives |q_Q(d)| ≥ τ > s, a contradiction.

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
