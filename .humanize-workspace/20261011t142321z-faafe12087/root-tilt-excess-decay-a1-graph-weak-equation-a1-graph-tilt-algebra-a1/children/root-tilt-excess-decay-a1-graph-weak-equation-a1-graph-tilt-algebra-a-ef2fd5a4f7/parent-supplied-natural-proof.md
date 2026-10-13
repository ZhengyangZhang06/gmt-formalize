# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_tilt_algebra-a1`
- Child DAG node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_tilt_algebra-a1.graph_row_orthogonal-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Context. This is Simon 4.5 (7) ('e_{n+j} - (grad f^j, 0) is normal to the graph'), step 4 of the parent proof. The parent applies it with D = Df(x') and r the j-th row of D. Prerequisite: graph_coords (GA, Submission.any_radius_gr_la_graphPoint_algebra): (L2) graphPoint (a - a') (b - b') = graphPoint a b - graphPoint a' b'; (IP) <graphPoint a b, graphPoint a' b'> = <a, a'> + <b, b'>.

Notation. Fix n, l, q, D, j and r with <r, v> = (D v)_j for every v in R^n. d_j := EuclideanSpace.single j 1 in R^l, e'_j := q(graphPoint 0 d_j), g := q(graphPoint r 0), S := span_R{q(graphPoint v (D v)) : v in R^n} and p := S.starProjection (it exists since R^{n+l} is finite-dimensional).

1. The difference. Put x := e'_j - g. Since q is linear, x = q(graphPoint 0 d_j - graphPoint r 0), and by (L2) (read from right to left with a = 0, a' = r, b = d_j, b' = 0), graphPoint 0 d_j - graphPoint r 0 = graphPoint (0 - r) (d_j - 0). So x = q(graphPoint (0 - r) (d_j - 0)) = q(graphPoint (-r) d_j).
2. x is orthogonal to every generator of S. Let v be in R^n. The linear isometry equivalence q preserves inner products (LinearIsometryEquiv.inner_map_map), so by (IP)
 <x, q(graphPoint v (D v))> = <graphPoint (-r) d_j, graphPoint v (D v)> = <-r, v> + <d_j, D v>.
 Here <-r, v> = -<r, v> = -(D v)_j by the hypothesis on r, and <d_j, y> = y_j for every y in R^l (EuclideanSpace.inner_single_left with the scalar 1). Hence <x, q(graphPoint v (D v))> = -(D v)_j + (D v)_j = 0.
3. x lies in S-perp. The set of vectors y with <x, y> = 0 is the subspace (R x)-perp (Submodule.mem_orthogonal_singleton_iff_inner_right). By step 2 it contains every generator q(graphPoint v (D v)), so it contains their span S (Submodule.span_le). Thus <x, y> = 0 for every y in S, i.e. x lies in S-perp (Submodule.mem_orthogonal').
4. Conclusion. The orthogonal projection onto S vanishes exactly on S-perp (Submodule.starProjection_apply_eq_zero_iff), so p x = 0. By linearity, 0 = p x = p e'_j - p g, i.e. p(q(graphPoint 0 d_j)) = p(q(graphPoint r 0)). QED

Remark (verified Lean realization; not part of the mathematical argument). Placed inside `namespace Submission` of the Submission file (within namespace GMT.Ch05 with the contract's opens; Lean v4.35.0-rc3, Mathlib 25730c7c) as `theorem gwe_gta_graph_row_orthogonal : <frozen type> := by` followed by the body below, it compiled with sorry stubs of the sibling theorem(s) any_radius_gr_la_graphPoint_algebra in scope. The same tactic body with the sibling propositions as hypotheses has #print axioms [propext, Classical.choice, Quot.sound].
  have hGA := any_radius_gr_la_graphPoint_algebra
  intro n ℓ q D j r hr
  have hdiff : q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ))) - q (graphPoint r 0) =
      q (graphPoint (0 - r) (EuclideanSpace.single j (1 : ℝ) - 0)) := by
    rw [← map_sub, (hGA n ℓ).2.2.2.1]
  have hgen : ∀ v : Rn n, inner ℝ (q (graphPoint (0 - r) (EuclideanSpace.single j (1 : ℝ) - 0))) (q (graphPoint v (D v))) = 0 := by
    intro v
    rw [LinearIsometryEquiv.inner_map_map, (hGA n ℓ).2.2.2.2.2.2, zero_sub, sub_zero, inner_neg_left,
      hr v, EuclideanSpace.inner_single_left]
    simp
  have hmem : q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ))) - q (graphPoint r 0) ∈
      (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v))))ᗮ := by
    rw [hdiff]
    have hle : Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v))) ≤
        (ℝ ∙ q (graphPoint (0 - r) (EuclideanSpace.single j (1 : ℝ) - 0)))ᗮ := by
      rw [Submodule.span_le]
      rintro _ ⟨v, rfl⟩
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (hgen v)
    refine (Submodule.mem_orthogonal' _ _).mpr (fun u hu => ?_)
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hle hu)
  have h0 := (Submodule.starProjection_apply_eq_zero_iff _).mpr hmem
  rw [map_sub, sub_eq_zero] at h0
  exact h0

## Key steps

1. By linearity of q and (L2), x := q(graphPoint 0 d_j) - q(graphPoint r 0) = q(graphPoint (-r) d_j)
2. q preserves inner products and (IP) gives <x, q(graphPoint v (D v))> = -<r, v> + (D v)_j = 0 for every v
3. Orthogonality to all generators gives x in S-perp (span_le into (R x)-perp)
4. p vanishes on S-perp, so p(q(graphPoint 0 d_j)) = p(q(graphPoint r 0))

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp GMT/Ch05/Contract.lean GMT/Ch05/Submission.lean; cmp GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Contract.lean; git rev-parse HEAD; python3 -I (lake-manifest.json package revs); git -C lake-packages-25730c7c/{mathlib,simongmt} rev-parse HEAD`
- `python3 -I dag.json census: nodes whose lean_statement mentions graphPoint / rotatedPlane / horizontalPlane / starProjection (with finrank or inner); full records (status, depends_on, candidate_commit, parent_handoff) of hsNorm_starProjection_trace_identities, lip_approx_graph_coordinates, any_radius_gr_linear_algebra_basics, any_radius_gr_la_graphPoint_algebra, any_radius_gr_la_rotatedPlane_facts, tdo_gpd_graph_plane_finrank, rsod_graphPoint_eq_finAddEquivProd_symm`
- `python3 -I lean_name / lean_statement census in dag.json for gwe_gta_proj_inner_defect, gwe_gta_vertical_trace_sum, gwe_gta_graph_row_orthogonal, gwe_gta_row_bounds; grep -rl gwe_gta_ nodes dag.json; grep -rn gwe_gta_ GMT`
- `python3 -I reuse-pattern scan of nodes/*/decomposition-v*.json against dag.json children (root-tilt-excess-decay-a1-graph-weak-equation-a1 decomposition-v1/v2; root-density-one-regularity-a1-tangent-ae-a1-density-from-tangent-a1 decomposition-v2)`
- `python3 -I: subproblem.natural_proof / proof_key_steps of the reused nodes' parent-child-handoff.json files`
- `git show 164f08e449a3:GMT/Ch05/Submission.lean (and 600de562dfc2, b1a6014f632b, 154e53341598, e2915745b92c): imports and the accepted trace computation`
- `grep -n 'starProjection_inner_eq_zero|starProjection_orthogonal_val|starProjection_eq_self_iff|starProjection_norm_le|inner_starProjection_left_eq_right|starProjection_isSymmetric|starProjection_apply_eq_zero_iff' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `grep -n 'mem_orthogonal|mem_orthogonal_singleton_iff_inner_right' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Orthogonal.lean`
- `grep -rn trace_eq_sum_inner <snapshot>/mathlib/Mathlib; grep -n 'theorem trace_eq_matrix_trace ' <snapshot>/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `grep -n toDual_symm_apply Analysis/InnerProductSpace/Dual.lean; grep -n 'norm_sq_eq|real_norm_sq_eq|single_apply|inner_single_left|inner_single_right|orthonormal_single|basisFun|finrank_euclideanSpace_fin' Analysis/InnerProductSpace/PiL2.lean; sed -n 580,592p Analysis/InnerProductSpace/PiL2.lean (OrthonormalBasis.map, map_apply)`
- `grep -n 'norm_apply_le|norm_sq_eq_of_L2|def proj' Analysis/Normed/Lp/PiLp.lean; grep -n natAdd_inj Order/Fin/Basic.lean; grep -rn LinearIsometryEquiv.inner_map_map Analysis/InnerProductSpace; grep -rn abs_real_inner_le_norm Analysis/InnerProductSpace; grep -n 'theorem le_opNorm' Analysis/Normed/Operator/Basic.lean (all under <snapshot>/mathlib/Mathlib)`
- `sed -n 540,612p verifier/gmt-compare.py (contract_scope / child_modules; CHILD_TARGET = HumanizeNodeComparator.target)`
- `lean -o /tmp/gta-decomp-20261012/olean/GMT/Ch05/Submission.olean Submission.lean (contract-only copy)`
- `python3 -I scripts/build.py dag.json <run> out/children.json gen/Realize.lean.bodies.json; python3 -I scripts/gen_checks.py verifier/gmt-compare.py GMT/Ch05/Contract.lean out/children.json gen; python3 -I scripts/gen_realize.py out/children.json scripts/gen_checks.py gen/Realize.lean`
- `lean gen/challenge/*.lean, gen/solution/*.lean, gen/TypesSubmission.lean, gen/Assembly.lean (#print axioms parent_check), gen/ChildProofs.lean (#print axioms *_check), gen/Inst.lean, gen/Realize.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-graph-tilt-algebra-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1-tangent-ae-a1-density-from-tangent-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-height-estimate-a1-projection-algebra-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1-la-basics-a1-graph-coords-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1-la-basics-a1-rotated-plane-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-c1-submanifold-graph-ball-a1-graph-poi-152c2738dc/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-graph-plane-dist-a1-grap-f97a789982/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Orthogonal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Order/Fin/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/gta-decomp-20261012/scripts/build.py`
- `/tmp/gta-decomp-20261012/scripts/gen_checks.py`
- `/tmp/gta-decomp-20261012/scripts/gen_realize.py`
- `/tmp/gta-decomp-20261012/gen/Assembly.lean`
- `/tmp/gta-decomp-20261012/gen/ChildProofs.lean`
- `/tmp/gta-decomp-20261012/gen/Inst.lean`
- `/tmp/gta-decomp-20261012/gen/TypesSubmission.lean`
- `/tmp/gta-decomp-20261012/gen/Realize.lean`

Revisions. Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd, which is the workspace HEAD, and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d.
- The snapshot's project/GMT/Ch05/Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.
- lake-manifest.json pins simongmt 2b3663083f3fe399b6296fb8eaee52169170e197.
- The lake-packages used for compilation are at the same Mathlib and simongmt commits.

Reuse. The five reused declarations are all 'accepted' in dag.json. Each is reused with byte-identical lean_statement, title and statement:
- hsNorm_starProjection_trace_identities (164f08e, deps []);
- any_radius_gr_la_graphPoint_algebra (600de56, deps []);
- any_radius_gr_la_rotatedPlane_facts (b1a6014, deps [graph_coords node]);
- rsod_graphPoint_eq_finAddEquivProd_symm (18a457c, deps []);
- tdo_gpd_graph_plane_finrank (154e533, deps [graph_point_linear_equiv node]).
Earlier accepted decompositions (graph_weak_equation-a1, density_from_tangent-a1 v2) register reused keys as the existing node ids, with sibling dependencies mirrored. The natural proofs are copied from those nodes' handoffs. The accepted candidate commits add no imports.

No-match results.
- None of the names gwe_gta_proj_inner_defect, gwe_gta_vertical_trace_sum, gwe_gta_graph_row_orthogonal or gwe_gta_row_bounds occurs in dag.json, in any node JSON, or in the project sources, so all four are free.
- No accepted node already states the projection defect inequality, the vertical trace sum, graph-row orthogonality or the row bounds.
- any_radius_gr_linear_algebra_basics and lip_approx_graph_coordinates overlap (L5)/(L7) and GC(i),(ii),(iv), but they are not needed.

Mathlib items located in the snapshot.
- Projection/Basic.lean:
  - starProjection_inner_eq_zero (164);
  - starProjection_orthogonal_val (203);
  - starProjection_eq_self_iff (290);
  - starProjection_norm_le (386);
  - inner_starProjection_left_eq_right (652);
  - starProjection_isSymmetric (658);
  - starProjection_apply_eq_zero_iff (689, with K explicit).
- Orthogonal.lean: mem_orthogonal' (57) and mem_orthogonal_singleton_iff_inner_right (86).
- LinearMap.trace_eq_sum_inner is in Analysis/InnerProductSpace/Trace.lean:25. The contract does not import that file, so the trace child uses LinearMap.trace_eq_matrix_trace (LinearAlgebra/Trace.lean:87) with an OrthonormalBasis, as the accepted 164f08e proof does.
- InnerProductSpace.toDual_symm_apply (Dual.lean:178).
- PiL2.lean:
  - EuclideanSpace.norm_sq_eq / real_norm_sq_eq (149/153);
  - EuclideanSpace.single_apply (308; deprecated in favour of PiLp.single_apply);
  - inner_single_left / inner_single_right (318/322);
  - orthonormal_single (349);
  - OrthonormalBasis.map / map_apply (581/586);
  - EuclideanSpace.basisFun (802);
  - finrank_euclideanSpace_fin (205).
- PiLp.norm_apply_le (PiLp.lean:713).
- Fin.natAdd_inj (Order/Fin/Basic.lean:210).
- LinearIsometryEquiv.inner_map_map (LinearMap.lean:117).
- abs_real_inner_le_norm (InnerProductSpace/Basic.lean:471).
- ContinuousLinearMap.le_opNorm (Normed/Operator/Basic.lean:234).

Lean checks. All of these were generated from the exact strings and compiled against a fresh contract-only olean.
- 9 NodeChallenge files and 9 NodeSolution files elaborate (exit 0).
- TypesSubmission elaborates all 9 as Submission.X.
- Assembly proves the frozen parent type from the child propositions, sorry-free, using only [propext, Classical.choice, Quot.sound].
- ChildProofs proves all four new children from their declared siblings, using only [propext, Classical.choice, Quot.sound].
- Inst passes its rfl / simp instance checks.
- Realize compiles the four attached tactic bodies inside namespace Submission against sibling stubs, with no deprecation warnings.
