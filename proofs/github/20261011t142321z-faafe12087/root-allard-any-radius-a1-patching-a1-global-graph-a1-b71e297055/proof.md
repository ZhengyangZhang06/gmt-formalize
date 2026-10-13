# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_any_radius-a1.patching-a1`
- Child DAG node: `root.allard_any_radius-a1.patching-a1.global_graph-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation: B_r(x) is the closed ball and B°_r(x) the open ball; T0 := rotatedPlane q0; E := EuclideanSpace.finAddEquivProd. 'The hypothesis at y with (c, d)' means the local-graph hypothesis. The sibling arp_rotatedPlane_graphPoint_coords n l supplies:
- (i) graphPoint a b = E^{-1}(a, b);
- (ii) |graphPoint a b|^2 = |a|^2 + |b|^2;
- (iii) infDist(q0(graphPoint a b), T0) = |b|.
0. Coordinates and parameters. For z in R^{n+l} let pi z := (E(q0^{-1} z)).1 and sigma z := (E(q0^{-1} z)).2. Both are continuous linear maps.
By (i): z = q0(graphPoint (pi z) (sigma z)); pi(q0(graphPoint a b)) = a; sigma(q0(graphPoint a b)) = b.
By (ii) and since q0 is an isometry, |z|^2 = |pi z|^2 + |sigma z|^2, so |pi z| <= |z| and |z| <= |pi z| + |sigma z|.
By (iii), infDist(z, T0) = |sigma z|.
Parameter facts:
- 1 - kappa > 0;
- A > 0, since otherwise (1 - kappa) A <= 0 < R;
- t >= s + 2 kappa A > 0;
- A <= A + t <= B;
- R <= (1 - kappa) A <= A.
1. The cone in coordinates. For z in S cap B_B(0): |sigma z| <= kappa |z|, so |z| <= |pi z| + kappa |z|, i.e. (1 - kappa)|z| <= |pi z|.
Put K := S cap B_A(0), which is contained in S cap B_B(0). Then |sigma z| <= kappa |z| <= kappa A for every z in K.
2. Distance estimate. If z, y are in K and |pi z - pi y| <= s, then |z - y| <= |pi(z - y)| + |sigma(z - y)| <= s + |sigma z| + |sigma y| <= s + 2 kappa A <= t.
3. pi is injective on K. Let y1, y2 be in K with pi y1 = pi y2 =: c. Since y1 = q0(graphPoint c (sigma y1)), the hypothesis at y1 with d := sigma y1 gives some f. As s > 0, c lies in B°_s(c).
First, y1 is in S cap B_t(y1) because t >= 0, so the uniqueness clause gives sigma y1 = f(c).
Second, step 2 gives |y2 - y1| <= t, so q0(graphPoint c (sigma y2)) = y2 is in S cap B_t(y1), and sigma y2 = f(c).
Thus sigma y1 = sigma y2, and y1 = q0(graphPoint c (sigma y1)) = y2.
4. Compactness. K is closed (hypothesis) and contained in the compact ball B_A(0) of the finite-dimensional space (isCompact_closedBall). So K is compact (IsCompact.of_isClosed_subset), and D := pi(K) is compact (IsCompact.image) and closed (IsCompact.isClosed). Also 0 is in K (0 is in S and A >= 0), and pi(0) = 0.
5. U := D cap B°_R(0) is open. Let w0 be in U, with w0 = pi y for some y in K. The hypothesis at y with (c, d) := (w0, sigma y) gives some f.
Let w' be in B°_s(w0) cap B°_R(0) and put x' := q0(graphPoint w' (f w')). By the existence clause, x' is in S cap B_t(y), so |x'| <= |y| + t <= A + t <= B and x' is in S cap B_B(0).
By step 1, (1 - kappa)|x'| <= |pi x'| = |w'| < R <= (1 - kappa) A, so |x'| < A. Hence x' is in K and w' = pi x' is in U.
Thus U contains the open neighbourhood B°_s(w0) cap B°_R(0) of each of its points, so U is open (isOpen_iff_mem_nhds).
6. B°_R(0) is contained in D. B°_R(0) is convex, hence preconnected (Convex.isPreconnected). U is open by step 5. B°_R(0) cap U contains 0 (step 4 and R > 0). Since D is closed, closure(U) cap B°_R(0) ⊆ closure(D) cap B°_R(0) = D cap B°_R(0) = U. By IsPreconnected.subset_of_closure_inter_subset, B°_R(0) ⊆ U ⊆ D.
7. Definition of u. For x in B°_R(0), use step 6 and choice to pick z_x in K with pi z_x = x, and set u(x) := sigma z_x. For x outside B°_R(0) set u(x) := 0. Then for x in B°_R(0), q0(graphPoint x (u x)) = q0(graphPoint (pi z_x) (sigma z_x)) = z_x, which is in K.
8. Uniqueness clause. Let x be in B°_R(0) and b in R^l with q0(graphPoint x b) in S cap B_A(0) = K. This point and z_x both lie in K and have pi-coordinate x, so they are equal by step 3. Applying sigma gives b = sigma z_x = u(x).
9. Membership clause. For x in B°_R(0), z_x is in S cap B_B(0). By step 1, (1 - kappa)|z_x| <= |pi z_x| = |x| < R <= (1 - kappa) A, so |z_x| < A. Hence q0(graphPoint x (u x)) = z_x is in S cap B°_A(0).
10. Reverse inclusion. Let z be in S cap B°_R(0). Since |z| < R <= A, z is in K. Put w := pi z; then |w| <= |z| < R. Since z = q0(graphPoint w (sigma z)) is in K, step 8 gives sigma z = u(w). So z = q0(graphPoint w (u w)) with w in B°_R(0), i.e. z is in q0 '' graphOver u (B°_R(0)).
11. Regularity and slope. Fix x0 in B°_R(0) and put y := z_{x0} = q0(graphPoint x0 (u x0)), which is in K. The hypothesis at y with (c, d) := (x0, u x0) gives f, C^1 on B°_s(x0) with |fderiv f| <= L there.
For w in B°_s(x0) cap B°_R(0): z_w is in K and |pi z_w - pi y| = |w - x0| <= s, so |z_w - y| <= t by step 2. Thus q0(graphPoint w (u w)) = z_w is in S cap B_t(y), and the uniqueness clause gives u(w) = f(w).
So u = f on the open neighbourhood B°_s(x0) cap B°_R(0) of x0. f is C^1 at x0, since it is C^1 on the open ball B°_s(x0), which contains x0. Hence u is C^1 at x0 (ContDiffAt.congr_of_eventuallyEq), and fderiv u x0 = fderiv f x0 (Filter.EventuallyEq.fderiv_eq), so |fderiv u x0| <= L.
Since x0 was arbitrary, u is C^1 on B°_R(0) (each ContDiffAt gives ContDiffWithinAt) with |fderiv u x| <= L there. Together with steps 8-10, this proves all five conclusions.

## Key steps

1. Coordinates pi, sigma; the cone becomes |sigma z| <= kappa|z|, hence (1 - kappa)|z| <= |pi z| and |sigma| <= kappa A on K = S cap B_A(0)
2. Distance estimate: points of K with |pi z - pi y| <= s are within t of each other
3. pi is injective on K, via the uniqueness clause at the centre c
4. K compact, so D = pi(K) is closed; U = D cap B°_R(0) is open by the existence clause plus the cone bound; connectedness of the disc gives B°_R(0) ⊆ D
5. Define u by choice; uniqueness, membership and reverse inclusion follow from injectivity and the cone bound
6. Locally u = f (uniqueness clause plus distance estimate), so u is C^1 with |Du| <= L

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp <snapshot>/project/{GMT/Ch05/Contract.lean,GMT/Ch05/Submission.lean,lakefile.toml,lean-toolchain,lake-manifest.json} against the workspace copies`
- `python3 -I reads of dag.json (node root.allard_any_radius-a1.patching-a1: status, message, attempts, retry_operation; all node statuses) and issue-workers.json (Counter of error fields; this node's worker records)`
- `python3 -I sha256 comparison of decomposition-v1..v4.json subproblem fields (key/lean_name/lean_statement/depends_on, natural_proof, proof_key_steps, statement, title) and summary of decomposition-audit-v1..v4.json verdicts`
- `python3 -I sha256 of parent-child-handoff.json subproblem.natural_proof versus decomposition-scope-v4.json proof_sha256; lean_statement equality between handoff and scope`
- `grep -n '^open|^namespace|^end|^theorem|^def|^abbrev' GMT/Ch05/Submission.lean (scope at main_theorem); head -120 GMT/Ch05/Contract.lean (Amb, Rn, hsNormSq, hsNorm, graphPoint, graphOver, horizontalPlane, rotatedPlane)`
- `grep -n 'finAddEquivProd|sumEquivProd|theorem EuclideanSpace.norm_eq|norm_sq_eq' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `grep -n 'theorem opNorm_le_bound |sum_mul_le_sqrt_mul_sqrt|le_infDist|theorem infDist_image|theorem infDist_le_dist_of_mem|norm_image_sub_le_of_norm_fderivWithin_le|surjOn_closedBall_of_nonlinearRightInverse|HasFDerivAt.of_local_left_inverse|theorem inverse_continuousAt|contDiffAt_succ_iff_hasFDerivAt|theorem contDiffAt_zero|ContDiffOn.differentiableOn|IsPreconnected.subset_of_closure_inter_subset|def ofInjectiveEndo|fderivWithin_of_mem_nhds|Filter.EventuallyEq.fderiv_eq|pow_le_pow_left₀|pow_le_pow_iff_left₀|div_le_iff₀|mul_le_of_le_one_left|eventually_of_mem' in the snapshot Mathlib`
- `python3 -I recursive scan of every lean_name in dag.json and nodes/*/*.json for arp_opNorm_le_hsNorm, arp_rotatedPlane_graphPoint_coords, arp_tilt_le_of_slab, arp_regraph_over_rotatedPlane, arp_global_graph_of_local_graphs (plus duplicate check)`
- `git for-each-ref --format='%(objectname)' | sort -u | xargs -n 50 git grep -l -E 'arp_(opNorm_le_hsNorm|rotatedPlane_graphPoint_coords|tilt_le_of_slab|regraph_over_rotatedPlane|global_graph_of_local_graphs)|any_radius_patching' -- '*.lean'; grep -rn 'arp_|any_radius_patching' --include=*.lean GMT <snapshot>/project`
- `python3 -I scan of dag.json lean_statements for types identical to the five children or mentioning hsNorm/‖A‖, graphPoint a b, infDist (q₀ (graphPoint`
- `ls/grep theorem names in lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter05`
- `lake build GMT.Ch05.Submission (fresh scratch /tmp/arp5-patching-vSXJof/proj, .lake/packages symlinked to lake-packages-25730c7c)`
- `python3 -I /tmp/arp5-scripts/gen_challenges.py (verifier gmt-compare.py layout/contract_scope/child_modules and lean_contract.validate_lean_statement); lake env lean Checks/Challenge_{op_norm_le_hs_norm,rotated_coords,tilt_of_slab,regraph,global_graph,parent}.lean`
- `lake env lean Checks/Skeleton5.lean (exact parent type proved from sorry stubs of the five exact child types)`
- `lake env lean Checks/SkeletonAx5.lean (children as axioms; #print axioms Submission.any_radius_patching)`
- `lake env lean Checks/Avail5.lean (#check of 39 cited lemmas; env.contains for ContractingWith, ContractingWith.fixedPoint, ContDiffAt.to_localInverse, HasStrictFDerivAt.to_localInverse, HasStrictFDerivAt.localInverse)`
- `lake env lean Checks/Inst5.lean (pp.explicit norm instances; opNorm rfl to the sInf formula)`
- `python3 -I diff of hand-typed /tmp/arp5-scripts/typed.json (keys, names, dependencies, lean_statements) against decomposition-v4.json`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Real/Sqrt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ApproximatesLinearOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/OfCompLeft.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Connected/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Order/Filter/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-patching-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-patching-a1/decomposition-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-patching-a1/decomposition-audit-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-patching-a1/decomposition-scope-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter05`
- `/tmp/arp5-patching-vSXJof/proj/Checks/Challenge_op_norm_le_hs_norm.lean`
- `/tmp/arp5-patching-vSXJof/proj/Checks/Challenge_rotated_coords.lean`
- `/tmp/arp5-patching-vSXJof/proj/Checks/Challenge_tilt_of_slab.lean`
- `/tmp/arp5-patching-vSXJof/proj/Checks/Challenge_regraph.lean`
- `/tmp/arp5-patching-vSXJof/proj/Checks/Challenge_global_graph.lean`
- `/tmp/arp5-patching-vSXJof/proj/Checks/Challenge_parent.lean`
- `/tmp/arp5-patching-vSXJof/proj/Checks/Skeleton5.lean`
- `/tmp/arp5-patching-vSXJof/proj/Checks/SkeletonAx5.lean`
- `/tmp/arp5-patching-vSXJof/proj/Checks/Avail5.lean`
- `/tmp/arp5-patching-vSXJof/proj/Checks/Inst5.lean`
- `/tmp/arp5-scripts/gen_challenges.py`
- `/tmp/arp5-scripts/typed.json`

Snapshot and target
- The manifest pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d.
- Contract.lean, Submission.lean and the Lake inputs are byte-identical to the workspace copies.
- The handoff proof hash and frozen parent type match decomposition-scope-v4.json.

Scope
- The comparator's child scope at main_theorem is: open MeasureTheory Metric Set Filter Topology; open scoped ENNReal NNReal; namespace GMT.Ch05; open RectifiableVarifold.
- All five child types and the parent type pass validate_lean_statement and elaborate there after import GMT.Ch05.Submission, with only the expected sorry warning.

Sufficiency
- Skeleton5.lean compiles a complete proof of the exact parent type from sorry stubs of the five exact child types.
- SkeletonAx5.lean (children as axioms) gives #print axioms = propext, Classical.choice, Quot.sound plus exactly the five child declarations. Every child is used, and no other gap remains.

Cited library results, all present at the stated lines
- opNorm_le_bound, Operator/Basic.lean:196
- Real.sum_mul_le_sqrt_mul_sqrt, Real/Sqrt.lean:499
- EuclideanSpace.norm_eq, PiL2.lean:145; finAddEquivProd, PiL2.lean:378
- le_infDist :508, infDist_le_dist_of_mem :500 and infDist_image :596, in HausdorffDistance.lean
- norm_image_sub_le_of_norm_fderivWithin_le, MeanValue.lean:484
- surjOn_closedBall_of_nonlinearRightInverse, ApproximatesLinearOn.lean:143
- HasFDerivAt.of_local_left_inverse, OfCompLeft.lean:165
- NormedRing.inverse_continuousAt, Units.lean:183
- contDiffAt_succ_iff_hasFDerivAt :1018 and contDiffAt_zero :1129, in ContDiff/Defs.lean
- IsPreconnected.subset_of_closure_inter_subset, Connected/Basic.lean:434
- LinearEquiv.ofInjectiveEndo, FiniteDimensional/Basic.lean:412

Availability and instances
- All 39 #check-ed lemmas resolve after the import.
- ContractingWith and ContDiffAt.to_localInverse are not in scope, as regraph's proof states. HasStrictFDerivAt.to_localInverse is in scope but not needed.
- Norm instances are ContinuousLinearMap.hasOpNorm and PiLp.instNorm. No Matrix or IsUnit construction occurs.

Names and reuse
- The five arp_* names occur only in this node's own v1-v4 proposals.
- They are absent from all 217 DAG lean_names (no duplicates), from GMT/ and the snapshot project, and from every .lean file on 667 git refs.
- No DAG declaration has an identical type; the closest, lip_approx_graph_coordinates, differs. Nothing is reused.
- SimonGMT Chapter05 contains only graph-area lemmas and is not imported by Submission, so it has no relevant match.

No network sources were needed; the mathematics is the parent-supplied proof (step 6 of the any-radius proof).
