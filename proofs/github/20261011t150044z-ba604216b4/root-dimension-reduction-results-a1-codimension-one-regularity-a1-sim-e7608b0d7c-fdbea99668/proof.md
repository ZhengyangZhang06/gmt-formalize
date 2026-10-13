# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.submanifold_approx_tangent-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.submanifold_approx_tangent-a1.chart_localization-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent step 3, (3.1) (localization), together with the inclusion ψ(B_{ρ₀}(v₀)) ∩ B_δ(x) ⊆ N ∩ W used in the "⊇" half of (4.1). Parent step 3 derives (3.1) from properness and injectivity of the chart by a compactness argument. That argument is the content of the accepted sibling chart_inverse_continuity (ψ^{-1} is continuous at ψ(v₀) along ψ(V); Simon Ch. 2, (4.1)–(4.2)), which is used here instead.
Notation: x := ψ(v₀); B_s(c) is the open ball; distances are Euclidean.
1. (ψ(V) ⊆ W₀.) ψ(V) = W₀ ∩ N ⊆ W₀. Since v₀ ∈ V, x = ψ(v₀) ∈ W₀.
2. (Inverse continuity.) Apply chart_inverse_continuity to V, W₀ (in the role of W there) and ψ, with the point v₀ ∈ V and ε := ρ > 0. Its hypotheses hold: ψ is continuous and injective on V, ψ(V) ⊆ W₀ by step 1, and V ∩ ψ^{-1}(K) is compact for every compact K ⊆ W₀. It gives δ₁ > 0 such that every v ∈ V with |ψ(v) − ψ(v₀)| < δ₁ satisfies |v − v₀| < ρ.
3. (Room in W ∩ W₀.) x ∈ W by hypothesis and x ∈ W₀ by step 1. W ∩ W₀ is open, so there is δ₂ > 0 with B_{δ₂}(x) ⊆ W ∩ W₀.
4. (Choice of δ.) Put δ := min(δ₁, δ₂) > 0. Then B_δ(x) ⊆ B_{δ₂}(x) ⊆ W ∩ W₀.
5. (⊆.) Let y ∈ N ∩ W with |y − x| < δ. By step 4, y ∈ W₀, so y ∈ W₀ ∩ N = ψ(V): y = ψ(v) for some v ∈ V. Then |ψ(v) − ψ(v₀)| = |y − x| < δ ≤ δ₁, so |v − v₀| < ρ by step 2, i.e. v ∈ B_ρ(v₀). Hence y ∈ ψ(B_ρ(v₀)) ∩ B_δ(x).
6. (⊇.) Let y = ψ(v) with v ∈ B_ρ(v₀) and |y − x| < δ. Since B_ρ(v₀) ⊆ V, y ∈ ψ(V) = W₀ ∩ N, so y ∈ N. Also y ∈ B_δ(x) ⊆ W by step 4. Hence y ∈ (N ∩ W) ∩ B_δ(x).
7. (Conclusion.) By steps 5 and 6, (N ∩ W) ∩ B_δ(x) = ψ(B_ρ(v₀)) ∩ B_δ(x), with δ > 0. ∎

## Key steps

1. chart_inverse_continuity (ψ(V) ⊆ W₀, properness, injectivity) gives δ₁ > 0: v ∈ V and |ψ(v) − ψ(v₀)| < δ₁ imply |v − v₀| < ρ.
2. Choose δ₂ > 0 with B_{δ₂}(ψ(v₀)) ⊆ W ∩ W₀ and put δ := min(δ₁, δ₂).
3. ⊆: a point of N ∩ W ∩ B_δ(ψ(v₀)) lies in W₀ ∩ N = ψ(V), so it is ψ(v) with v ∈ B_ρ(v₀).
4. ⊇: ψ(B_ρ(v₀)) ⊆ ψ(V) ⊆ N and B_δ(ψ(v₀)) ⊆ W.

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
