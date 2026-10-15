# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.growth_dimension-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.growth_dimension-a1.pow_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 ("Conclusion") of the parent proof, where a = m₀ > 0 and b = C(3√r)^n; the divergence M^{r−n} → ∞ used there is realized by a single explicit Archimedean choice of M.
1. Suppose, for contradiction, that r > n, i.e. n + 1 ≤ r.
2. By the Archimedean property of ℝ choose N ∈ ℕ with N > b/a, and put M := N + 1. Then M is an integer with M ≥ 1, and M > N > b/a; multiplying by a > 0 gives a·M > b.
3. As a real number M ≥ 1, and n + 1 ≤ r, so M^{n+1} ≤ M^r, i.e. M^n·M ≤ M^r. Multiplying by a > 0 and applying the hypothesis at this M: a·M·M^n = a·(M^n·M) ≤ a·M^r ≤ b·M^n.
4. Since M ≥ 1 > 0, M^n > 0, and cancelling M^n in step 3 gives a·M ≤ b, contradicting step 2. Hence r ≤ n. ∎

## Key steps

1. Assume n + 1 ≤ r for contradiction.
2. Choose an integer M ≥ 1 with a·M > b (Archimedean property, a > 0).
3. M^{n+1} ≤ M^r gives a·M·M^n ≤ a·M^r ≤ b·M^n; cancelling M^n > 0 yields a·M ≤ b, a contradiction.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git rev-parse HEAD = b4d606db…; git -C <snapshot>/mathlib rev-parse HEAD = 25730c7c…`
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `cat nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-15e43615f0/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.md}`
- `rg -n 'cbr_ci_cp_gd_' <snapshot>/project <snapshot>/mathlib GMT/ and grep -rl 'cbr_ci_cp_gd_' nodes/ (no match); python3 -I scan of dag.json lean_name values (1563 nodes): cbr_ci_cp_gd_subspace_lattice_packing, cbr_ci_cp_gd_translated_ball_count, cbr_ci_cp_gd_le_of_pow_bound and the prefix cbr_ci_cp_gd_ are unused`
- `python3 -I /tmp/gd-decomp/scan.py dag.json with substrings 'PairwiseDisjoint', '2 ≤ dist', 'packing', 'Archimedean', '(M : ℝ) ^', 'growth', 'Finset.card', '→ ℤ', 'Fin r →', 'OrthonormalBasis', 'stdOrthonormalBasis', 'finrank ℝ V ≤', 'Finset (Euclid P)', '.card', '(fun x => v + x) ⁻¹', 'ball 0 (ρ + 1)', 'exists_nat_gt' (closest accepted: idtp_tdc_nipp_disjoint_packing, dorag_aa_finite_separated_net, cbrldvc_exists_disjoint_closedBall_cover, codim1_rdo_dg_vdl_discrete_growth; none has a needed child type, so no identical-type reuse)`
- `grep -rn in <snapshot>/mathlib/Mathlib: 'lemma card_piFinset' (Data/Fintype/BigOperators.lean:123), 'theorem card_Icc' (Data/Int/Interval.lean:96), 'theorem measure_biUnion_finset' (MeasureTheory/Measure/Basic.lean:150), 'theorem EuclideanSpace.norm_eq' (Analysis/InnerProductSpace/PiL2.lean:145), 'sum_repr_symm' (PiL2.lean:503), 'stdOrthonormalBasis' (PiL2.lean:1073), 'theorem norm_coe' / deprecated 'coe_norm' (Analysis/Normed/Group/Submodule.lean:28,35), "norm_le_norm_add_norm_sub'" (Analysis/Normed/Group/Basic.lean:201), 'theorem dist_triangle_left' (Topology/MetricSpace/Pseudo/Defs.lean:213), 'def piFinset' (Data/Fintype/Pi.lean:31)`
- `sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_decompose: node.depth 5 < max_depth 6), prompts.py (DECOMPOSE, DECOMPOSITION_AUDIT), leaf_verification.py check_source_delta (a leaf appends one theorem Submission.X), parent_verification.py; git diff 0e39207b..a0fcc157 -- GMT/Ch07/Submission.lean (accepted leaves are appended after the contract section's end inside namespace GMT.Ch07)`
- `lake env lean /tmp/gd-decomp/Elab.lean (3 child types elaborate; pp.coercions/pp.numericTypes check instances), /tmp/gd-decomp/ChildA.lean, ChildB.lean, ChildC.lean (complete scratch proofs), /tmp/gd-decomp/Assembly.lean`
- `python3 -I /tmp/gd-build/gen.py dag.json: verifier/lean_contract.py validate_lean_statement passes on all 3 strings, key/lean_name regexes, freshness, parent type read from dag.json; then lake env lean /tmp/gd-build/Final.lean: Submission.cbr_ci_cp_gd_* proved, gd_assembly_final (hypotheses = the 3 child types verbatim, conclusion = exact frozen parent type) and gd_parent_from_children compile; #print axioms gives propext, Classical.choice, Quot.sound for all five`
- `independent reviewer agent: /tmp/gd-review/Elab.lean, Assembly.lean (review_gd_assembly; author re-ran it: propext, Classical.choice, Quot.sound), Children.lean, E2E.lean (children inserted into a copy of Submission.lean), scripts/dagcheck.py, validate.py, delta_and_e2e.py (re-implemented check_source_delta: pass), final_checks.py; verdict ACCEPT`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-15e43615f0/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-15e43615f0/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-15e43615f0/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fintype/BigOperators.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Int/Interval.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Submodule.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fintype/Pi.lean`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/prompts.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/parent_verification.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/gd-build/Final.lean`
- `/tmp/gd-decomp/Assembly.lean`
- `/tmp/gd-review/Assembly.lean`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean (project b4d606db, Mathlib 25730c7c). No accepted DAG declaration or snapshot lemma has any of the three needed child types. The closest are idtp_tdc_nipp_disjoint_packing (infinitely many disjoint sets), dorag_aa_finite_separated_net (a maximal net) and codim1_rdo_dg_vdl_discrete_growth (a different growth law). So all three children are new, and their names cbr_ci_cp_gd_* are fresh in the DAG, the snapshot and the workspace. Every Mathlib tool cited in the child proofs exists in the snapshot and is reachable from import GMT.Ch07.Submission: stdOrthonormalBasis, OrthonormalBasis.repr, Submodule.norm_coe, EuclideanSpace.norm_eq, Fintype.piFinset/card_piFinset, Int.card_Icc, Finset.card_image_of_injective, measure_biUnion_finset, norm_le_norm_add_norm_sub' and dist_triangle_left. The three frozen types elaborate in the contract namespace/opens with the intended coercions and pass validate_lean_statement. Complete scratch proofs of all three children compile, as does a hypothesis-only assembly proving the exact frozen parent type, with axioms propext, Classical.choice and Quot.sound only. An independent reviewer reproduced these checks and accepted.
