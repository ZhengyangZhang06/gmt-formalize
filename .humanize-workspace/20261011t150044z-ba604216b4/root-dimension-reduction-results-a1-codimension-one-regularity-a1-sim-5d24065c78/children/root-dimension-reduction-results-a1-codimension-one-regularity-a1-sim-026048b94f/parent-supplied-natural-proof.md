# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.submanifold_approx_tangent-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.submanifold_approx_tangent-a1.approx_tangent_locality-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent step 4, (4.1)–(4.2). For f supported in B_R(0) and 0 < r < δ/R, the blow-up η_{x,r}(N ∩ W) meets B_R(0) only in the image of the part of N ∩ W inside B_δ(x). So the integrals of f over η_{x,r}(N ∩ W) and over the blown-up chart piece coincide. Here this is proved for arbitrary sets. The restriction identity of step 3 replaces the parent's use of setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, which needed Borel measurability of η_{x,r}(N ∩ W).
Notation:
- μ := H^n = μHE[n].
- η_r := η_{x,r} (SimonGMT blowUpMap x r), η_r(t) = r^{-1}(t − x).
- For a set T, ∫_T f dμ is the Bochner integral of f against the restricted measure μ⌞T (Lean: ∫ y in T, f y ∂μ). It is defined for every set T.
1. (Dimension.) The first conjunct, dim Q = n, does not involve the set. It holds by the hypothesis on S'.
2. (Support radius.) Fix f ∈ C_c(ℝ^P). Its topological support is compact, hence bounded, so there is R₀ with spt f ⊆ B_{R₀}(0). Put R := max(R₀, 1) > 0. Then spt f ⊆ B_R(0), so f(y) = 0 for every y ∉ B_R(0).
3. (Cut-off of the integral.) For every set T ⊆ ℝ^P, ∫_T f dμ = ∫_{B_R(0) ∩ T} f dμ.
 - f vanishes outside B_R(0), so the integral of f against μ⌞T equals its integral against (μ⌞T)⌞B_R(0) (Mathlib setIntegral_eq_integral_of_forall_compl_eq_zero, valid for any set and any measure).
 - B_R(0) is open, hence Borel, so (μ⌞T)⌞B_R(0) = μ⌞(B_R(0) ∩ T) (Mathlib Measure.restrict_restrict, which only needs measurability of B_R(0)).
4. (Only the part near x matters.) Let 0 < r < δ/R. For every set T, B_R(0) ∩ η_r(T) = B_R(0) ∩ η_r(T ∩ B_δ(x)).
 - ⊇: η_r(T ∩ B_δ(x)) ⊆ η_r(T).
 - ⊆: let y = η_r(t) = r^{-1}(t − x) with t ∈ T and |y| < R. Then |t − x| = r|y| < rR < (δ/R)R = δ. So t ∈ T ∩ B_δ(x) and y ∈ η_r(T ∩ B_δ(x)).
5. (Equal blown-up integrals.) Let 0 < r < δ/R. By steps 3 and 4 and the hypothesis S ∩ B_δ(x) = S' ∩ B_δ(x):
 ∫_{η_r(S')} f dμ = ∫_{B_R(0) ∩ η_r(S')} f dμ = ∫_{B_R(0) ∩ η_r(S' ∩ B_δ(x))} f dμ = ∫_{B_R(0) ∩ η_r(S ∩ B_δ(x))} f dμ = ∫_{B_R(0) ∩ η_r(S)} f dμ = ∫_{η_r(S)} f dμ.
6. (Limit.) δ/R > 0, so the interval (0, δ/R) belongs to the filter 𝓝[>] 0 of r ↓ 0. Hence r ↦ ∫_{η_r(S')} f dμ and r ↦ ∫_{η_r(S)} f dμ agree eventually along r ↓ 0. The first tends to ∫_Q f dμ by the hypothesis on S', so the second does too (Filter.Tendsto.congr').
7. (Conclusion.) f ∈ C_c(ℝ^P) was arbitrary. With step 1 this is HasApproximateTangentSpaceAt n S x Q. ∎

## Key steps

1. The dimension conjunct does not involve the set.
2. For f ∈ C_c(ℝ^P) choose R > 0 with spt f ⊆ B_R(0); then ∫_T f dH^n = ∫_{B_R(0) ∩ T} f dH^n for every set T (restriction to the Borel ball).
3. For 0 < r < δ/R, B_R(0) ∩ η_{x,r}(T) = B_R(0) ∩ η_{x,r}(T ∩ B_δ(x)), so the blown-up integrals over S and S' agree.
4. They agree eventually along r ↓ 0, so the limit ∫_Q f dH^n transfers from S' to S.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `sed -n 215,270p GMT/Ch07/Contract.lean (IsEmbeddedSubmanifold, tangentSpace, approxTangentPlane)`
- `sed -n 1,160p SimonGMT/Chapter03/Rectifiable.lean (blowUpMap, HasApproximateTangentSpaceAt, hasApproximateTangentSpaceAt_submodule)`
- `python3 scans of dag.json (1512 nodes): lean_statement containing HasApproximateTangentSpaceAt together with IsEmbeddedSubmanifold/ContDiffOn/ψ; accepted nodes containing normDet or ∫ … '' … fderiv; status, candidate_commit, children and depends_on of chart_tangentSpace_eq_range_fderiv, dsmc_chart_inverse_continuity, codim1_rdo_c1cov_local_lower_lipschitz, codim1_rdo_c1_piece_approxTangent and the codim1_rdo_c1pt_* subtree`
- `git show <commit>:GMT/Ch07/Submission.lean for 9ff76906722d, 12e74edc2f87, 5e4b21584624, d626082a69a0 and the proof base 785373c28002 (imports, declarations, sorry count); git merge-base --is-ancestor 5e4b2158 d626082a`
- `runtime.py: _decompose (max_depth gate), _existing_lean_name_problem, _solve_children, _install_parent_supplied_child_handoff, _accepted_checkpoint, _overlay_accepted_children, _merge_candidate_history; store.py ensure; decomposition_scope.py; models.py Subproblem; swarm-project.json max_depth 6, max_children 12`
- `grep in snapshot mathlib: ContDiffBump one_of_mem_closedBall / zero_of_le_dist / hasContDiffBump_of_innerProductSpace, setIntegral_eq_integral_of_forall_compl_eq_zero, theorem restrict_restrict, Filter.EventuallyEq.fderiv_eq, Ioo_mem_nhdsGT, isBounded_iff_subset_ball, image_eq_one_of_notMem_mulTSupport`
- `xargs -n 200 sh -c 'git grep -l -e codim1_ac_sat_ "$@" -- GMT/Ch07/Submission.lean' over all 2578 distinct ref commits (0 hits; control codim1_rdo_c1_piece_approxTangent: 5 hits); grep -c codim1_ac_sat_ dag.json GMT SimonGMT (0)`
- `lake env lean -DautoImplicit=false /tmp/sat-split/check/TypesAssembly.lean; /tmp/sat-split/check/AssemblyAx.lean; /tmp/sat-split/combined/Combined.lean`
- `book: sed -n 60,130p chapter-03.txt (Remark 1.3, Definition 1.4, Remarks 1.5, proof of Theorem 1.6 '⇒')`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/InnerProduct.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/LeftRightNhds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-5d24065c78/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-chart-tangent-space-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ch-0f11358db9/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-ec0e4b9204/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-18e8208cd7/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-f448992aee/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-f448992aee/decomposition-audit-v1.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/decomposition_scope.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/models.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/sat-split/check/TypesAssembly.lean`
- `/tmp/sat-split/check/AssemblyAx.lean`
- `/tmp/sat-split/combined/Combined.lean`

Pins match.
- The manifest records project b4d606db and Mathlib 25730c7c. These equal workspace HEAD and .lake/packages/mathlib.
- The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).
Library.
- SimonGMT Chapter03/Rectifiable.lean defines blowUpMap and HasApproximateTangentSpaceAt (C_c test functions, 𝓝[>] 0).
- It proves only the flat case (hasApproximateTangentSpaceAt_submodule) and uniqueness. It has no existence theorem for C¹ submanifolds.
DAG.
- Four declarations are accepted with candidate commits and byte-identical frozen types:
  - chart_tangentSpace_eq_range_fderiv (d626082a69a0);
  - dsmc_chart_inverse_continuity (5e4b21584624, an ancestor of d626);
  - codim1_rdo_c1cov_local_lower_lipschitz (12e74edc2f87);
  - codim1_rdo_c1_piece_approxTangent (9ff76906722d), which also carries its 4 accepted codim1_rdo_c1pt_* prerequisites.
- All four candidates keep the contract's 8 imports. Their only sorry is main_theorem.
- dtc_bc_lc_sl_c1_tangent and dor_lmbsf_c1_image_approxTangent are related but unaccepted (decomposing), so they are not reused.
- This node's proof base 785373c28002 is the bare contract (457 lines), so the accepted lemmas are reachable only as children.
Snapshot Mathlib supplies:
- ContDiffBump: BumpFunction/Basic.lean (one_of_mem_closedBall, zero_of_le_dist) and InnerProduct.lean (hasContDiffBump_of_innerProductSpace);
- setIntegral_eq_integral_of_forall_compl_eq_zero (Bochner/Set.lean:486, no measurability hypothesis);
- Measure.restrict_restrict (Restrict.lean:205);
- Filter.EventuallyEq.fderiv_eq (FDeriv/Congr.lean:260);
- image_eq_zero_of_notMem_tsupport (to_additive of Support.lean:111);
- Ioo_mem_nhdsGT and isBounded_iff_subset_ball.
Names. The 4 new codim1_ac_sat_ names are free in dag.json, GMT/, SimonGMT and all 2578 ref commits.
Lean.
- TypesAssembly.lean (8 child types plus the parent assembly) exits 0.
- The AssemblyAx.lean axioms are as stated in the rationale.
- Combined.lean (base, real accepted code, new proofs) proves the selected theorem with only propext, Classical.choice and Quot.sound.
Runtime.
- max_depth is 6, so the children (depth 6) are leaves.
- Accepted reuse passes _existing_lean_name_problem and is skipped by _install_parent_supplied_child_handoff.
- Children and depends_on are overlaid by _overlay_accepted_children.
