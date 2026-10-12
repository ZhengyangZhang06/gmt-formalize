# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_any_radius-a1.graph_rate-a1.plane_projections-a1`
- Child DAG node: `root.allard_any_radius-a1.graph_rate-a1.plane_projections-a1.hs_ideal-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation.
- e_i (i < m), f_j (j < k), g_r (r < p) are the standard basis vectors EuclideanSpace.single _ 1 of R^m, R^k, R^p.
- z_j is the j-th coordinate of a vector z, <.,.> the real Euclidean inner product, ||.|| the operator norm.
- o is composition of continuous linear maps (∘L).

1. Coordinates. For z in R^k:
- |z|^2 = sum_{j<k} z_j^2 (EuclideanSpace.real_norm_sq_eq);
- <z, f_j> = z_j = <f_j, z> (EuclideanSpace.inner_single_right and inner_single_left with a = 1).
The same holds in R^m and R^p.

2. (H1). Fix i < m and j < k. By step 1 and the hypothesis with u = e_i, v = f_j:
(X e_i)_j = <X e_i, f_j> = <e_i, Y f_j> = (Y f_j)_i.
Hence, by step 1 and exchanging the two finite sums:
hsNormSq X = sum_{i<m} |X e_i|^2
= sum_{i<m} sum_{j<k} (X e_i)_j^2
= sum_{i<m} sum_{j<k} (Y f_j)_i^2
= sum_{j<k} sum_{i<m} (Y f_j)_i^2
= sum_{j<k} |Y f_j|^2
= hsNormSq Y.

3. (H2). Fix i < m.
- (Y o X) e_i = Y(X e_i), and |Y(X e_i)| <= ||Y|| |X e_i| by the definition of the operator norm (ContinuousLinearMap.le_opNorm).
- Both sides are >= 0, so |Y(X e_i)|^2 <= ||Y||^2 |X e_i|^2.
Summing over i < m: hsNormSq (Y o X) <= ||Y||^2 sum_{i<m} |X e_i|^2 = ||Y||^2 hsNormSq X.

4. Adjoints. Every continuous linear T : R^a -> R^b has a continuous linear adjoint T* : R^b -> R^a with <T u, v> = <u, T* v> for all u, v, and ||T*|| <= ||T||.
- Construction: T* v := sum_{i<a} <T e_i, v> e_i. It is linear in v, hence continuous (finite dimension). For u = sum_i u_i e_i, linearity of T gives <u, T* v> = sum_i u_i <T e_i, v> = <T u, v>.
- Bound: by the identity with u = T* v and Cauchy-Schwarz, |T* v|^2 = <T* v, T* v> = <T(T* v), v> <= ||T|| |T* v| |v|. So |T* v| <= ||T|| |v| (trivial if T* v = 0), i.e. ||T*|| <= ||T||.
- In Lean this is Mathlib's ContinuousLinearMap.adjoint, used with ContinuousLinearMap.adjoint_inner_right. It is a linear isometric equivalence, so even ||T*|| = ||T|| (LinearIsometryEquiv.norm_map).
- The frozen contract does not import it, so the proof adds import Mathlib.Analysis.InnerProductSpace.Adjoint. The statement itself mentions no adjoint.

5. (H3). Let X* : R^k -> R^m and W* : R^m -> R^p be adjoints of X and W as in step 4.
(a) For u in R^p and v in R^k:
<(X o W) u, v> = <X(W u), v> = <W u, X* v> = <u, W*(X* v)> = <u, (W* o X*) v>.
By (H1) for the pair (X o W, W* o X*), maps R^p -> R^k and R^k -> R^p: hsNormSq (W* o X*) = hsNormSq (X o W).
(b) By (H1) for the pair (X, X*): hsNormSq X* = hsNormSq X.
(c) By (H2) with Y := W* : R^m -> R^p and X* : R^k -> R^m in place of X: hsNormSq (W* o X*) <= ||W*||^2 hsNormSq X*.
(d) Since 0 <= ||W*|| <= ||W||, we have ||W*||^2 <= ||W||^2. Also hsNormSq X* >= 0 (a sum of squares).
Combining (a)-(d):
hsNormSq (X o W) = hsNormSq (W* o X*) <= ||W*||^2 hsNormSq X* <= ||W||^2 hsNormSq X* = ||W||^2 hsNormSq X.

6. Steps 2, 3 and 5 prove (H1), (H2) and (H3) for all m, k, p, which is the stated conjunction.

## Key steps

1. Coordinates in Euclidean space: |z|^2 = sum_j z_j^2 and z_j = <z, f_j>
2. (H1): (X e_i)_j = <X e_i, f_j> = <e_i, Y f_j> = (Y f_j)_i, then exchange the finite double sum
3. (H2): |Y(X e_i)| <= ||Y|| |X e_i|, square and sum over i
4. Every T has an adjoint T* with <T u, v> = <u, T* v> and ||T*|| <= ||T|| (explicit transpose, or Mathlib ContinuousLinearMap.adjoint)
5. (H3): X o W has adjoint W* o X*, so by (H1), (H2), (H1): hsNormSq(X o W) = hsNormSq(W* o X*) <= ||W*||^2 hsNormSq X* <= ||W||^2 hsNormSq X

## Reference use

### local-project

Queries:
- `cat <run>/nodes/root-allard-any-radius-a1-graph-rate-a1-plane-projections-a1/parent-child-handoff.json and parent-supplied-plan.md; python3 -I dump of <run>/nodes/root-allard-any-radius-a1-graph-rate-a1-la-basics-a1/parent-child-handoff.json (la_basics frozen type and proof)`
- `python3 -I scans of <run>/dag.json: status and lean_name of the graph_rate, patching and allard_regularity graph_plane_algebra nodes; every depth>=4 node with its depends_on; accepted nodes whose lean_statement mentions hsNormSq, starProjection or graphPoint; full types of lip_approx_graph_coordinates, rsod_norm_graphPoint_sq, rsod_graphPoint_eq_finAddEquivProd_symm, lgc_hsNormSq_bounds`
- `python3 -I dump of <run>/nodes/root-allard-any-radius-a1-graph-rate-a1/decomposition-v2.json (rationale and child deps) and <run>/nodes/root-allard-regularity-a1-density-bounds-a1-annular-monotonicity-a1/decomposition-v1.json and decomposition-scope-v1.json (reuse precedent)`
- `git show <commit>:GMT/Ch05/Submission.lean | grep -n '^import' for accepted candidates ddc8e5e2, 86e951f4, 5fe5660c, e3412456`
- `grep -n 'starProjection_apply_mem|starProjection_eq_self_iff|isIdempotentElem_starProjection|starProjection_orthogonal'|norm_sq_eq_add_norm_sq_starProjection|inner_starProjection_left_eq_right|HasOrthogonalProjection instances' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `grep -n '^def adjoint :|^theorem adjoint_inner_right|^theorem adjoint_comp ' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean; grep -c 'InnerProductSpace.Adjoint' <snapshot>/project/GMT/Ch05/Contract.lean`
- `grep -n 'EuclideanSpace.real_norm_sq_eq|EuclideanSpace.inner_single_left|EuclideanSpace.inner_single_right' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean; grep -n '^theorem coe_range' <snapshot>/mathlib/Mathlib/Algebra/Module/Submodule/Range.lean; grep -n '^theorem le_sqrt_of_sq_le|^theorem sqrt_le_sqrt |^theorem sqrt_sq ' <snapshot>/mathlib/Mathlib/Analysis/Real/Sqrt.lean`
- `name scan for any_radius_gr_pp_ (and each of the 4 proposed names) over dag.json, nodes/*/*.json, <snapshot>/project, lake-packages simongmt and Mathlib, plus git grep over all 1275 local refs (*.lean)`
- `lake build GMT.Ch05.Submission in /tmp/pp-decomp-scratch/proj (copy of <snapshot>/project; .lake/packages -> lake-packages-25730c7c)`
- `lake env lean Checks/Types.lean, Checks/Types2.lean, Checks/HSIdeal.lean, Checks/HSSplit.lean, Checks/Graph.lean, Checks/Key.lean, Checks/Parent.lean (with #print axioms)`
- `python3 -I /tmp/pp-decomp-scratch/scripts/numcheck2.py (pure-Python random check of the key inequality, (S2) and (P4))`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Algebra/Module/Submodule/Range.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Real/Sqrt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1-plane-projections-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1-plane-projections-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1-la-basics-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1-annular-monotonicity-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1-annular-monotonicity-a1/decomposition-scope-v1.json`
- `/tmp/pp-decomp-scratch/proj/Checks/Types.lean`
- `/tmp/pp-decomp-scratch/proj/Checks/Types2.lean`
- `/tmp/pp-decomp-scratch/proj/Checks/HSIdeal.lean`
- `/tmp/pp-decomp-scratch/proj/Checks/HSSplit.lean`
- `/tmp/pp-decomp-scratch/proj/Checks/Graph.lean`
- `/tmp/pp-decomp-scratch/proj/Checks/Key.lean`
- `/tmp/pp-decomp-scratch/proj/Checks/Parent.lean`
- `/tmp/pp-decomp-scratch/scripts/numcheck2.py`

Snapshot
- Pinned at project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d.
- Snapshot Submission.lean is byte-identical to the workspace copy and to Contract.lean.
- The contract does not import Mathlib.Analysis.InnerProductSpace.Adjoint (grep count 0). ContinuousLinearMap.adjoint is an unknown constant after import GMT.Ch05.Submission (Checks/Types.lean).
  - So no frozen child type mentions adjoints; (HS1) is stated in hypothesis form.
  - Accepted candidates add imports to Submission.lean (e.g. ddc8e5e2 adds 6), so child proofs may import Adjoint.lean, whose def adjoint is at :112 and adjoint_inner_right at :125.

Mathlib facts used by the child proofs (snapshot paths)
- Projection/Basic.lean:
  - starProjection_apply_mem :156;
  - starProjection_orthogonal' :223, giving Kᗮ.starProjection = 1 - K.starProjection;
  - starProjection_eq_self_iff :290;
  - isIdempotentElem_starProjection :298;
  - norm_sq_eq_add_norm_sq_starProjection :607;
  - inner_starProjection_left_eq_right :652;
  - HasOrthogonalProjection instances ofCompleteSpace :53, Kᗮ :61, map_linearIsometryEquiv :68.
- PiL2.lean: EuclideanSpace.real_norm_sq_eq :153, inner_single_left :318, inner_single_right :322.
- Submodule/Range.lean: LinearMap.coe_range :60.
- Real/Sqrt.lean: sqrt_sq :180, sqrt_le_sqrt :208, le_sqrt_of_sq_le :257.

DAG findings
- A grandchild's base holds only the frozen contract plus its declared siblings (graph_rate decomposition-v2). So no child may use la_basics, and every la_basics application (steps 3 and 6) stays in the parent.
- Reuse requires an identical type with an accepted declaration (precedent: aal_curvature_pairing_holder_bound in annular_monotonicity decomposition-v1). No accepted declaration has any of the four child types.
- Accepted lip_approx_graph_coordinates, rsod_norm_graphPoint_sq and rsod_graphPoint_eq_finAddEquivProd_symm cover parts of the graphPoint algebra. The needed coordinate facts are about 25 lines, so graph_param re-derives them inline (verified) and adds no reuse child.
- The allard_regularity graph_plane_algebra children (graph_normal_bound, graph_proj_bilipschitz, hs_norm_bounds, isometry_conj) are decomposing and have different types.

No-match results
- 'any_radius_gr_pp_' and each proposed name occur in 0 files of dag.json, nodes/*/*.json, the snapshot project, simongmt and Mathlib.
- They also occur in 0 .lean files across all 1275 local git refs.

Lean (every theorem reports only propext, Classical.choice, Quot.sound)
- Types2: the four child types, the parent type and la_basics' type elaborate. ∘L is ContinuousLinearMap.comp (rfl), and inner ℝ is the Euclidean inner product.
- HSIdeal and Graph: complete proofs of hs_ideal and graph_param.
- HSSplit: hs_proj_split from hs_ideal's type.
- Key: key_ineq from the types of hs_ideal, hs_proj_split and graph_param.
- Parent: the exact frozen parent type from la_basics' frozen type plus graph_param and key_ineq.
