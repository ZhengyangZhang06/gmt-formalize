# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.submanifold_approx_tangent-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.submanifold_approx_tangent-a1.c1_local_extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. A technical step needed to apply the accepted sibling c1_piece_tangent, which is stated for globally C¹ maps, to the chart ψ of parent step 1, which is C¹ only on the open set V. The parent-supplied proof avoids this step by integrating against the indicator 1_{G_r} of the chart domain (parent steps 4–6). The argument is the standard cut-off by a smooth bump function.
Notation: B_s(c) is the open ball, B̄_s(c) the closed ball, |·| the Euclidean norm.
1. (Room in V.) V is open and v₀ ∈ V, so there is ε > 0 with B_ε(v₀) ⊆ V.
2. (Bump function.) Choose a C^∞ function φ : ℝ^m → ℝ with φ(v) = 1 whenever |v − v₀| ≤ ε/4 and φ(v) = 0 whenever |v − v₀| ≥ ε/2. In Mathlib this is a bump function φ : ContDiffBump v₀ with rIn = ε/4 < rOut = ε/2, available on the inner-product space Euclid m. The three properties are ContDiffBump.contDiff, ContDiffBump.one_of_mem_closedBall and ContDiffBump.zero_of_le_dist.
3. (Definition.) Put g(v) := φ(v)·ψ(v) for v ∈ ℝ^m, and ρ := ε/4 > 0. Then B_ρ(v₀) ⊆ B_ε(v₀) ⊆ V.
4. (g = ψ on B_ρ(v₀).) If |v − v₀| < ρ = ε/4, then φ(v) = 1 by step 2, so g(v) = ψ(v).
5. (g is C¹ at every point.) A map is C¹ on ℝ^m iff it is C¹ at every point (Mathlib contDiff_iff_contDiffAt). Fix v ∈ ℝ^m.
 (a) Case |v − v₀| < ε. Then v ∈ V by step 1, and V, being open, is a neighbourhood of v. ψ is C¹ on V, hence C¹ at v (ContDiffOn.contDiffAt). φ is C^∞, in particular C¹ at v. Hence the product g = φ·ψ of a scalar C¹ function and a vector C¹ function is C¹ at v (ContDiffAt.smul).
 (b) Case |v − v₀| ≥ ε. The set O := {w ∈ ℝ^m : |w − v₀| > ε/2} is open, as the preimage of the open ray (ε/2, ∞) under the continuous map w ↦ |w − v₀|. It contains v, because |v − v₀| ≥ ε > ε/2. For w ∈ O we have φ(w) = 0 by step 2, so g(w) = 0. Thus g coincides with the constant map 0 on a neighbourhood of v. The constant map is C¹, so g is C¹ at v (ContDiffAt.congr_of_eventuallyEq).
 So g is C¹ at every point, i.e. ContDiff ℝ 1 g.
6. (Conclusion.) By steps 3–5, 0 < ρ, B_ρ(v₀) ⊆ V, g is C¹ on ℝ^m, and g = ψ on B_ρ(v₀). ∎

## Key steps

1. Choose ε > 0 with B_ε(v₀) ⊆ V and a C^∞ bump φ equal to 1 on B̄_{ε/4}(v₀) and to 0 outside B_{ε/2}(v₀).
2. Put g := φ·ψ and ρ := ε/4; then B_ρ(v₀) ⊆ V and g = ψ on B_ρ(v₀).
3. g is C¹ at points of B_ε(v₀) ⊆ V (product of C¹ maps) and at points with |v − v₀| ≥ ε (g = 0 on the open set |w − v₀| > ε/2), hence C¹ on ℝ^m.

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
