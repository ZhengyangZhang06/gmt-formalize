# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_any_radius-a1.graph_rate-a1.plane_projections-a1`
- Child DAG node: `root.allard_any_radius-a1.graph_rate-a1.plane_projections-a1.hs_proj_split-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation.
- f_j (j < k) is the standard basis of R^k, <.,.> the Euclidean inner product, o composition (∘L).
- For a subspace K of R^m, P_K := K.starProjection. K is finite-dimensional, hence complete, so P_K exists.
- (H1) is the first conjunct of the sibling hs_ideal: if X : R^a -> R^b and Y : R^b -> R^a are continuous linear with <X u, v> = <u, Y v> for all u, v, then hsNormSq Y = hsNormSq X.

0. Facts for any subspace K of R^m (Mathlib, Projection/Basic.lean):
(a) P_K u lies in K, and P_K u = u iff u is in K (starProjection_apply_mem, starProjection_eq_self_iff). Hence P_K(P_K u) = P_K u.
(b) P_K is self-adjoint: <P_K u, v> = <u, P_K v> (inner_starProjection_left_eq_right). This also applies to K^perp, which has an orthogonal projection too.
(c) P_{K^perp} = I - P_K (starProjection_orthogonal').
(d) Pythagoras: |u|^2 = |P_K u|^2 + |P_{K^perp} u|^2 (norm_sq_eq_add_norm_sq_starProjection).
(e) Every continuous linear X : R^m -> R^k has a continuous linear adjoint X* : R^k -> R^m with <X u, v> = <u, X* v> for all u, v.
- Explicitly X* v = sum_{i<m} <X e_i, v> e_i; then <u, X* v> = sum_i u_i <X e_i, v> = <X u, v> by linearity.
- In Lean this is Mathlib's ContinuousLinearMap.adjoint with adjoint_inner_right, imported from Mathlib.Analysis.InnerProductSpace.Adjoint. The statement does not mention it.

1. (S1). Fix X and K and let X* be as in 0(e).
(i) By (H1) for the pair (X, X*): hsNormSq X* = hsNormSq X.
(ii) For u in R^m and v in R^k, by 0(e) and 0(b): <(X o P_K) u, v> = <P_K u, X* v> = <u, P_K(X* v)>. So by (H1) for the pair (X o P_K, P_K o X*): hsNormSq (P_K o X*) = hsNormSq (X o P_K).
(iii) The same argument with K^perp in place of K gives hsNormSq (P_{K^perp} o X*) = hsNormSq (X o P_{K^perp}).
(iv) Apply 0(d) to u = X* f_j and sum over j < k:
hsNormSq (P_K o X*) + hsNormSq (P_{K^perp} o X*) = sum_{j<k} (|P_K(X* f_j)|^2 + |P_{K^perp}(X* f_j)|^2) = sum_{j<k} |X* f_j|^2 = hsNormSq X*.
Combining (i)-(iv): hsNormSq (X o P_K) + hsNormSq (X o P_{K^perp}) = hsNormSq X* = hsNormSq X. This is (S1).

2. (S2). Let P := P_K and Q := P_L.
(i) By (S1) with k = m, X := P - Q and the subspace K:
hsNormSq (P - Q) = hsNormSq ((P - Q) o P) + hsNormSq ((P - Q) o P_{K^perp}).
It remains to show hsNormSq ((P - Q) o P_{K^perp}) = hsNormSq ((P - Q) o Q).
(ii) Put X' := (P - Q) o P_{K^perp} and Y := (P - Q) o Q, both maps R^m -> R^m. By (H1) for the pair (X', Y), it suffices to check <X' u, v> = <u, Y v> for all u, v in R^m.
(iii) By 0(c), P_{K^perp} u = u - P u. By linearity and 0(a), P(P u) = P u and Q(Q v) = Q v. So
<X' u, v> = <P u - P(P u) - Q u + Q(P u), v> = <P u, v> - <P u, v> - <Q u, v> + <Q(P u), v> = -<Q u, v> + <Q(P u), v>.
(iv) By 0(b) for Q, <Q u, v> = <u, Q v>. By 0(b) for Q and then P, <Q(P u), v> = <P u, Q v> = <u, P(Q v)>. Hence <X' u, v> = <u, P(Q v)> - <u, Q v>.
(v) On the other side, <u, Y v> = <u, P(Q v) - Q(Q v)> = <u, P(Q v)> - <u, Q v>.
The two agree, so hsNormSq ((P - Q) o P_{K^perp}) = hsNormSq ((P - Q) o Q). Substituting into (i) gives (S2).

## Key steps

1. Orthogonal projection facts: idempotent, self-adjoint, P_{K^perp} = I - P_K, Pythagoras |u|^2 = |P_K u|^2 + |P_{K^perp} u|^2
2. (S1): by (H1), hsNormSq(X P_K) = hsNormSq(P_K X*) and hsNormSq(X P_{K^perp}) = hsNormSq(P_{K^perp} X*); Pythagoras on each X* f_j sums to hsNormSq X* = hsNormSq X
3. (S2): apply (S1) to X = P - Q and K; a direct inner-product computation shows (P - Q)Q is an adjoint of (P - Q)P_{K^perp}, so (H1) identifies their Hilbert-Schmidt norms

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
