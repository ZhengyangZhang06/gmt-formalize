# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.density_gap-a1`
- Child DAG node: `root.dimension_reduction_results-a1.density_gap-a1.high_degree_zero-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 0 of the parent proof ("If j > P, every j-covector on ℝ^P is zero, so every C ∈ 𝒟_j(ℝ^P) is 0"), stated for an arbitrary domain U. Notation: a j-covector α ∈ Covector (Euclid P) j is a continuous alternating j-linear map (ℝ^P)^j → ℝ (SimonGMT: Covector E n := E [⋀^Fin n]→L[ℝ] ℝ); a test form ω ∈ 𝒟^j(U) = TestFormOn U j is an element of a submodule of the forms ℝ^P → Covector (Euclid P) j and is determined by its underlying form.
1. Every j-covector on ℝ^P is zero. Let α be a j-covector and v : Fin j → ℝ^P. If v were linearly independent over ℝ, then j = card(Fin j) ≤ finrank_ℝ ℝ^P = P (LinearIndependent.fintype_card_le_finrank, Fintype.card_fin, finrank_euclideanSpace_fin), contradicting P < j. So v is not linearly independent, and an alternating multilinear map over the field ℝ vanishes on every family that is not linearly independent (AlternatingMap.map_linearDependent, applied to α.toAlternatingMap). Hence α(v) = 0 for every v, i.e. α = 0 by extensionality.
2. Every test form vanishes. Let ω ∈ 𝒟^j(U). For every x ∈ ℝ^P, ω(x) is a j-covector, so ω(x) = 0 by step 1. Hence the underlying form of ω is the zero function, and ω = 0 in TestFormOn U j (Subtype.ext, funext).
3. T = 0. For every ω ∈ 𝒟^j(U), step 2 and linearity of the underlying functional give T(ω) = T(0) = 0 (map_zero), while (0 : GeometricCurrentOn U j)(ω) = 0 (GeometricCurrentOn.zero_apply). Geometric currents that agree on every test form are equal (GeometricCurrentOn.ext), so T = 0. ∎
Formalization note (this exact statement was proved outright, for this revision, in the scratch file /tmp/dg8/lean/HighDegreeZero.lean, theorem dg8_high_degree_zero, compiled with lake env lean against the frozen GMT.Ch07.Submission; axioms propext, Classical.choice, Quot.sound): step 1 by `ext v`, `hli.fintype_card_le_finrank`, `rw [Fintype.card_fin, finrank_euclideanSpace_fin]`, `omega`, then `α.toAlternatingMap.map_linearDependent v hdep`; step 3 by `GeometricCurrentOn.ext` and `rw [hω, map_zero, GeometricCurrentOn.zero_apply]`.

## Key steps

1. For P < j every family of j vectors in ℝ^P is linearly dependent, so every alternating j-covector vanishes.
2. Hence every test j-form supported in U is the zero form.
3. T(ω) = T(0) = 0 for every test form, so T = 0 by extensionality of geometric currents.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -l -e 'dimred_cdg_(eq_zero_of_lt_degree|im_cone_ball_mass|c1_diffeo_pushforward_im|pushforward_massOn_le_first_variation|harmonic_affine_approximation|allard_bounded_curvature_graph|minimizing_origin_regular)' -g '*.lean' local-references/123e8435b4a2469b lake-packages-25730c7c/simongmt/Poincare lake-packages-25730c7c/mathlib/Mathlib workspaces/gmt-ch07/GMT (exit 1: no match)`
- `grep -c -E '<same pattern>' dag.json (0); grep -l -E '<same pattern>' over the 780 workspaces/.swarm-worktrees/*/gmt-ch07/GMT/Ch07/Submission.lean (no match); git log --all --oneline -S dimred_cdg_ (only bbbfd3b8, which mentions dimred_cdg_weak_limit_cone, not a proposed name)`
- `python3 -I /tmp/dg8scripts/check_candidates.py dag.json (git show <candidate>:GMT/Ch07/Submission.lean for e183b985, d49dda91, 36b2d372, 2fd8f6ff, 8a6855aa, 4d9f2899, 01ae2c59, 428db72e: each declares theorem Submission.<lean_name> : <frozen type> := verbatim)`
- `python3 -I /tmp/dg8scripts/name_check.py <run> <decomposition> for v6, v7 and v8 (replay of Runtime._existing_lean_name_problem on dag.json) and replay of Runtime._topological`
- `python3 inspection of dag.json: statuses, candidate commits and frozen types of every node whose lean_statement equals a child type (including the fvmb_* children of first_variation_mass_bound-a1 and the codim1_ldr_ duplicates); this node's record (decomposing, attempt 8, children [])`
- `sed -n '1440,1560p;2355,2385p;6585,6660p' /runtime/flows/gmt-claude-b731e326000c/_recursive_lean/runtime.py; sed -n '60,260p' /runtime/flows/gmt-claude-b731e326000c/_recursive_lean/store.py (_decompose, _accepted_checkpoint, _existing_lean_name_problem, _reference_use_problem, Store.refresh, Store.update)`
- `cat cluster-state/logs/gmt-ch07/e39b4162870940da8110ef2d3c8bdbfa.log; ls nodes/root-minimizing-implies-stationary-a1-first-variation-mass-bound-a1/ (accepted-candidate.json at 07:57Z)`
- `python3 diff of nodes/root-dimension-reduction-results-a1-density-gap-a1/decomposition-v6.json and decomposition-v7.json; cat decomposition-audit-v1..v6.json`
- `sed -n '620,635p;25,62p' book/chapter-07.txt (Simon 7.1.2 and the use of Allard 5.2 in 7.4.3)`
- `PATH=<toolchain lean-4.35.0-rc3>/bin:$PATH lake env lean /tmp/dg8/lean/{Types,Linked,Assembly,HighDegreeZero,ConeBallMass,OriginRegular,HarmonicConclusion}.lean (each with #print axioms); python3 -I /tmp/dg8scripts/check_frozen.py dag.json`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-density-gap-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-density-gap-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-density-gap-a1/decomposition-v6.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-density-gap-a1/decomposition-v7.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-density-gap-a1/decomposition-audit-v6.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-density-gap-a1/decomposition-review-receipt-v5.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-first-variation-mass-bound-a1/accepted-candidate.json`
- `/runtime/flows/gmt-claude-b731e326000c/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b731e326000c/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/cluster-state/logs/gmt-ch07/e39b4162870940da8110ef2d3c8bdbfa.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/dg8/lean/Types.lean`
- `/tmp/dg8/lean/Linked.lean`
- `/tmp/dg8/lean/Assembly.lean`
- `/tmp/dg8/lean/HighDegreeZero.lean`
- `/tmp/dg8/lean/ConeBallMass.lean`
- `/tmp/dg8/lean/OriginRegular.lean`
- `/tmp/dg8/lean/HarmonicConclusion.lean`
- `/tmp/dg8scripts/check_frozen.py`
- `/tmp/dg8scripts/check_candidates.py`
- `/tmp/dg8scripts/name_check.py`

Pins match: the manifest records project b4d606d and Mathlib 25730c7c, which equal the workspace HEAD and the snapshot and package Mathlib; simongmt is at 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.
- Reuse: cone_current_imrep_measure_smul_image (e183b985), dor_imrep_massOn_eq_measure_and_support (d49dda91), imrep_approxTangent_starProjection_aesm (36b2d372), covectorEuclideanNorm_gram_bounds (2fd8f6ff) and dor_graph_supported_cycle_regular (8a6855aa) are accepted. Each has a character-identical frozen type and is declared verbatim in its candidate commit. The resolved dependencies dimred_im_mass_measure (01ae2c59) and dimred_regular_point_density (428db72e) are also accepted and declared verbatim.
- pushforward_action_massOn_le_first_variation (4d9f2899) is accepted with the identical type, but the runtime refused it for this parent. The child therefore uses the fresh name dimred_cdg_pushforward_massOn_le_first_variation, and its six fvmb_* helpers are cited only as a formalization aid.
- Names: the seven fresh dimred_cdg_ names occur nowhere in the snapshot, SimonGMT, Mathlib, the workspace GMT sources, dag.json, the 780 swarm-worktree Submission files or git history. Replaying the runtime name check and the topological sort on v8 reports no problem.
- Lean: all fifteen types elaborate. Linked.lean proves Submission.dimred_cone_density_gap from the actual child declarations, with sorry only in the eleven leaf stubs. The conditional checks (assembly, high_degree_zero, cone_ball_mass, origin_regularity and harmonic_affine's Conclusion) depend only on propext, Classical.choice and Quot.sound. They do not discharge the seven new children.
