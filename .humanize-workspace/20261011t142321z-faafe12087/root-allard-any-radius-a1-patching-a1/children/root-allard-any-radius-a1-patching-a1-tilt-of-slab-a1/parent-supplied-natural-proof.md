# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_any_radius-a1.patching-a1`
- Child DAG node: `root.allard_any_radius-a1.patching-a1.tilt_of_slab-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation: T0 := rotatedPlane q0, E := EuclideanSpace.finAddEquivProd, B_s(0) is the closed ball in R^n. The sibling arp_rotatedPlane_graphPoint_coords n l supplies:
- (i) graphPoint a b = E^{-1}(a, b);
- (ii) |graphPoint a b|^2 = |a|^2 + |b|^2;
- (iii) infDist(q0(graphPoint a b), T0) = |b|.
0. Vertical coordinate. For z in R^{n+l} let sigma z := (E(q0^{-1} z)).2. sigma is continuous linear: it composes q0^{-1}, E and the second projection.
By (i) and E^{-1} E = id, z = q0(graphPoint (E(q0^{-1} z)).1 (sigma z)). So by (iii), infDist(z, T0) = |sigma z| for every z.
Since 0 is in T0, |sigma z| = infDist(z, T0) <= dist(z, 0) = |z| (Metric.infDist_le_dist_of_mem).
By (i), graphPoint is linear in the pair (a, b), since E^{-1} is linear. By (ii), |graphPoint 0 b| = |b|.
1. Case e = 0. graphPoint 0 0 = E^{-1}(0, 0) = 0, so q(graphPoint 0 0) = 0. Then infDist(0, T0) = |sigma 0| = 0 = (h/s + eps) |0|.
2. Case e != 0. Put t := s/|e| > 0, x+ := t e and x- := (-t) e. Then |x+| = |x-| = t |e| = s, so x+, x- lie in B_s(0), and x+ - x- = (2t) e.
3. Identity. By linearity of graphPoint and of q:
q(graphPoint ((2t) e) 0) = [y + q(graphPoint x+ (v x+))] - [y + q(graphPoint x- (v x-))] - q(graphPoint 0 (v x+ - v x-)).
This holds because graphPoint x+ (v x+) - graphPoint x- (v x-) = graphPoint (x+ - x-) (v x+ - v x-) = graphPoint ((2t) e) 0 + graphPoint 0 (v x+ - v x-).
4. Estimate. Apply sigma (linear) and the triangle inequality:
|sigma(q(graphPoint ((2t) e) 0))| <= |sigma(y + q(graphPoint x+ (v x+)))| + |sigma(y + q(graphPoint x- (v x-)))| + |sigma(q(graphPoint 0 (v x+ - v x-)))|.
By step 0 the first two terms are infDists to T0 of slab points, so each is <= h by the slab hypothesis at x+ and x-.
The third term is <= |q(graphPoint 0 (v x+ - v x-))| = |graphPoint 0 (v x+ - v x-)| = |v x+ - v x-|, by step 0 and because q is an isometry.
By the Lipschitz hypothesis, |v x+ - v x-| <= eps |x+ - x-| = eps * 2t|e| = 2 eps s.
Hence |sigma(q(graphPoint ((2t) e) 0))| <= 2h + 2 eps s.
5. By linearity, graphPoint ((2t) e) 0 = (2t) • graphPoint e 0, so sigma(q(graphPoint ((2t) e) 0)) = (2t) • sigma(q(graphPoint e 0)). Hence 2t |sigma(q(graphPoint e 0))| <= 2h + 2 eps s. Dividing by 2t = 2s/|e| > 0 gives |sigma(q(graphPoint e 0))| <= (h + eps s)|e|/s = (h/s + eps)|e|.
6. By step 0, infDist(q(graphPoint e 0), T0) = |sigma(q(graphPoint e 0))| <= (h/s + eps)|e|.

## Key steps

1. Vertical coordinate sigma(z) = (E(q0^{-1} z)).2 is linear with infDist(z, T0) = |sigma z| <= |z|
2. Trivial case e = 0
3. Test the slab at x+- = +-(s/|e|) e, both in B_s(0)
4. Linear identity: q(graphPoint(2te, 0)) = difference of slab points minus q(graphPoint(0, v x+ - v x-))
5. Triangle inequality and the Lipschitz bound give 2t |sigma(q(graphPoint e 0))| <= 2h + 2 eps s; divide by 2t

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
