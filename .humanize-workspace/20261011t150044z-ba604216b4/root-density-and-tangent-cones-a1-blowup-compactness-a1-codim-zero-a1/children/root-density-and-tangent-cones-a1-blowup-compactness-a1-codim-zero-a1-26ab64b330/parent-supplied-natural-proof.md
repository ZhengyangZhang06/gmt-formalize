# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1.minimizing-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 9 of the parent proof of dtc_bc_codim_zero (minimality of C: a competitor differs from C by a compactly supported integer multiplicity cycle, which the Constancy Theorem forces to vanish), stated for an arbitrary integer multiplicity C and an arbitrary A (the argument never uses spt(S − C) ⊆ A ∩ W). Siblings used: top_constancy (Cst), im_sub (G = the accepted declaration dtc_isIntegerMultiplicity_sub) and vanish_off_support (V = the accepted declaration dtc_vanish_off_support).
1. Write n = m + 1. The first conjunct of IsMinimizingIn C A is IsIntegerMultiplicity C, a hypothesis.
2. Let W be open with CompactlyContained W univ, and let S ∈ GeometricCurrentOn univ n be integer multiplicity with SameBoundary S C (for n = m + 1 this unfolds to S.boundary = C.boundary), IsCompact (S − C).support and (S − C).support ⊆ A ∩ W. Put X := S − C; by the definition of subtraction of currents (toCurrent := S.toCurrent − C.toCurrent), X(ω) = S(ω) − C(ω) for every ω.
3. X is integer multiplicity by G (univ is open, n > 0, S and C are integer multiplicity).
4. ∂X = 0: for β ∈ TestFormOn univ m, X.boundary β = X(dβ) = S(dβ) − C(dβ) = S.boundary β − C.boundary β = 0 (GeometricCurrentOn.boundary_apply).
5. Apply Cst with V := B := univ (open; preconnected since ℝⁿ is convex, convex_univ.isPreconnected), X (step 3) and the hypothesis of step 4: there is c' ∈ ℤ with X(ω) = c'·∫ ω(y)(e) dy for every ω ∈ TestFormOn univ n (the condition tsupport ω ⊆ univ is automatic).
6. c' = 0. The set spt X = (S − C).support is compact, hence bounded: spt X ⊆ closedBall(0, r₀) for some r₀ ∈ ℝ (IsCompact.isBounded, Bornology.IsBounded.subset_closedBall). Let p := (|r₀| + 2)·e₁ (n ≥ 1; ‖p‖ = |r₀| + 2 since ‖e₁‖ = 1), and let a be the smooth bump function centred at p with inner radius 1/2 and outer radius 1 (ContDiffBump p): a is C^∞ (ContDiffBump.contDiff), a ≥ 0, HasCompactSupport a, tsupport a = closedBall(p, 1) (ContDiffBump.tsupport_eq), and ∫ a > 0 (ContDiffBump.integral_pos, from Mathlib.Analysis.Calculus.BumpFunction.Normed). Let e* be the n-covector v ↦ D(v), D := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det (continuous because D(v) is the determinant of the coordinate matrix of v: Module.Basis.det_apply, Continuous.matrix_det; e*(e) = 1 by Module.Basis.det_self), and ω(y) := a(y)·e*. Then ω is smooth with compact support, so ω ∈ TestFormOn univ n, and tsupport ω ⊆ tsupport a = closedBall(p, 1) (tsupport_smul_subset_left). For y ∈ closedBall(p, 1), ‖y‖ ≥ ‖p‖ − ‖y − p‖ ≥ |r₀| + 1 > r₀, so tsupport ω is disjoint from closedBall(0, r₀) ⊇ spt X, and V gives X(ω) = 0. By step 5, X(ω) = c'·∫ a(y)·e*(e) dy = c'·∫ a. Since ∫ a > 0, c' = 0.
7. Hence X(ω) = 0, i.e. S(ω) = C(ω), for every ω ∈ TestFormOn univ n; so S = C (GeometricCurrentOn.ext), C.massOn W = S.massOn W, and in particular C.massOn W ≤ S.massOn W. This proves IsMinimizingIn C A. ∎
Implementation note (not part of the proof): name every auxiliary Lean declaration introduced for this child with the prefix dtc_bc_cz_isMinimizingIn_ (for example dtc_bc_cz_isMinimizingIn_aux), because the candidates of sibling children are merged into one Submission.lean and only byte-identical duplicate declarations are dropped during that merge. ContDiffBump.integral_pos needs `import Mathlib.Analysis.Calculus.BumpFunction.Normed`, which is outside the frozen import closure.

## Key steps

1. A competitor S gives the integer multiplicity cycle X = S − C (im_sub; ∂X = ∂S − ∂C = 0) with compact support.
2. top_constancy on V = B = ℝⁿ gives X = c'[[ℝⁿ]].
3. Testing X with a·e*, a ≥ 0 a bump supported away from spt X with ∫a > 0, gives 0 = X(a e*) = c'∫a (vanish_off_support), so c' = 0, S = C and M_W(C) = M_W(S).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d); cmp snapshot project/GMT/Ch07/Contract.lean against workspace GMT/Ch07/Contract.lean and GMT/Ch07/Submission.lean (identical)`
- `python3 -I over dag.json: this node's record (status decomposing, attempts 3, children [], depends_on measure_locality-a1); lean_name inventory (902 nodes); reuse candidates dtc_vanish_off_support, dtc_isIntegerMultiplicity_sub, dgcr_smooth_tests_to_C1_tests (status accepted, byte-identical lean_statement, candidate commits); MEAS dtc_bc_measure_restrict_eq_of_eqOn (status comparing); keyword scan of accepted nodes (onstancy, blowUp, currentEval, basisFun, IMRep univ) for further reuse`
- `Read this node's decomposition-v1.json, decomposition-review-receipt-v1/v2.json, decomposition-audit-v1.json, decomposition-scope-v1.json, parent-child-handoff.json, and the accepted handoffs of vanish_off_support-a1, im_sub-a1 and graph-cycle-d2f9caa6a3 (dgcr)`
- `grep -n '_overlay_accepted_children|_existing_lean_name_problem|_install_parent_supplied_child_handoff|_solve_children|max_nodes|def _solve' /runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/runtime.py; store.py ensure; swarm-project.json (max_depth 6, max_children 12, max_nodes 1000)`
- `git merge-base --is-ancestor {44ef61f,77fcc7d,c1d6084} e34a71c (all fail); git show <accepted candidate>:GMT/Ch07/Submission.lean import tally over 570 accepted nodes`
- `sed/grep simongmt/Poincare/SimonGMT/Chapter06/{Forms,Currents,CurrentLocalEquality}.lean (IsTestForm, TestFormOn, GeometricCurrentOn, boundary_apply, exteriorDerivative_apply, zeroRegion, support) and Chapter08/DistributionalConstancy.lean (ae_eq_const_of_weak_coordinate_derivatives_zero)`
- `rg -n 'theorem map_insertNth|theorem curryLeft_apply_apply|theorem integral_comp_inv_smul_of_nonneg|theorem exists_mem_of_measure_ne_zero_of_ae|theorem integral_pos' local-references/123e8435b4a2469b/mathlib/Mathlib; rg 'continuous_of_finiteDimensional' (linear version only)`
- `rg -c 'dtc_bc_cz_' snapshot project, workspace GMT, simongmt/Poincare, dag.json (no match, exit 1); rg -l in nodes/ (only this node's v1 artifacts)`
- `python3 -I /tmp/cz0-v2/scripts/gen_challenges.py (verifier gmt-compare.py child_modules contract mode + lean_contract.validate_lean_statement) on the 9 child types, the parent type and the MEAS type`
- `lake env lean /tmp/cz0-v2/check/{Challenge_*.lean (11 files), Assembly.lean, IfaceDgcr.lean, Names.lean, Closure.lean, Closure2.lean} with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-codim-zero-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-codim-zero-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-codim-zero-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-vanish-off-support-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-im-sub-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-d2f9caa6a3/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/tmp/cz0-v2/check/Assembly.lean`
- `/tmp/cz0-v2/check/IfaceDgcr.lean`
- `/tmp/cz0-v2/check/Names.lean`
- `/tmp/cz0-v2/check/Closure2.lean`
- `/tmp/cz0-v2/check/Challenge_parent.lean`

Snapshot pin and contract: the snapshot (project b4d606d, Mathlib 25730c7c) contract is byte-identical to the workspace Contract.lean and Submission.lean used for compilation.

Library support:
- The pinned SimonGMT library supplies the APIs the children use: currents, boundary, support/zeroRegion, affine push-forward/pullback, rectifiability and approximate tangent spaces.
- It also supplies Chapter08.ae_eq_const_of_weak_coordinate_derivatives_zero (standard axioms). Its hypothesis is verbatim the conclusion of the accepted dgcr_smooth_tests_to_C1_tests.
- Every cited Mathlib/SimonGMT lemma exists at the pin. Only ContDiffBump.integral_pos and the Chapter08 theorem need imports beyond the frozen closure.

Lean checks:
- All 11 types elaborate in comparator scope.
- A conditional Lean assembly derives the exact selected type from six child types plus MEAS, using only propext, Classical.choice and Quot.sound.

Reuse and dependencies:
- V, G and dgcr are accepted with byte-identical types and are absent from this node's dispatch base, so they are reused as children.
- MEAS is not accepted, so it enters local_agreement as a hypothesis.

Names: no dtc_bc_cz_ name occurs in the DAG, the snapshot or the library.
