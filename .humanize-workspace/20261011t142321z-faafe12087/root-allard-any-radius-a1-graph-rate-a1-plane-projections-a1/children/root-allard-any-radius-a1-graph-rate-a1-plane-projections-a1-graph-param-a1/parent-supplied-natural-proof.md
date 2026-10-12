# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_any_radius-a1.graph_rate-a1.plane_projections-a1`
- Child DAG node: `root.allard_any_radius-a1.graph_rate-a1.plane_projections-a1.graph_param-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation.
- N := n + l, so Amb n l = R^N. Every index of Fin N is exactly one of Fin.castAdd l i (i < n) or Fin.natAdd n j (j < l).
- By definition graphPoint a b = toLp(Fin.append a b), so (graphPoint a b)_{castAdd l i} = a_i and (graphPoint a b)_{natAdd n j} = b_j.
- q is linear and |q z| = |z| for all z. ||.|| is the operator norm.
- This proof uses only the frozen contract, not la_basics. Steps 1-2 re-derive the coordinate facts it needs.

1. Coordinate algebra. Two vectors of R^N are equal iff their coordinates agree at every castAdd l i and every natAdd n j (Fin.addCases). Comparing coordinates (a_i + a'_i, b_j + b'_j, and so on):
(G1) graphPoint(a + a', b + b') = graphPoint(a, b) + graphPoint(a', b');
(G2) graphPoint(a - a', b - b') = graphPoint(a, b) - graphPoint(a', b');
(G3) graphPoint(t a, t b) = t graphPoint(a, b) for real t.
(G4) Split the sum in |z|^2 = sum_k z_k^2 over Fin (n + l) into its castAdd and natAdd parts (Fin.sum_univ_add):
|graphPoint(a, b)|^2 = sum_{i<n} a_i^2 + sum_{j<l} b_j^2 = |a|^2 + |b|^2.

2. The graph map. Fix A and define g_A : R^n -> R^N by g_A(v) := graphPoint(v, A v).
- g_A is linear: g_A(v + v') = graphPoint(v + v', A v + A v') = g_A(v) + g_A(v') by linearity of A and (G1), and g_A(t v) = graphPoint(t v, t A v) = t g_A(v) by (G3).
- So its range is a linear subspace. The span of a subspace is itself: span(range g_A) = range g_A (Submodule.span_eq with LinearMap.coe_range).
- Consequently every element of G_A = q(range g_A) has the form q(graphPoint(v, A v)) for some v in R^n.

3. (P1). graphPoint(x, A x) = g_A(x) lies in range g_A, which is contained in its span. So q(graphPoint(x, A x)) lies in G_A (Submodule.mem_map_of_mem). An orthogonal projection fixes exactly the vectors of its subspace (starProjection_eq_self_iff), so P_A(q(graphPoint(x, A x))) = q(graphPoint(x, A x)).

4. (P2). Let y := q(graphPoint(0, w)).
(i) P_A y lies in G_A (starProjection_apply_mem), so by step 2 P_A y = q(graphPoint(v, A v)) for some v in R^n.
(ii) By linearity of q and (G2): y - P_A y = q(graphPoint(0, w) - graphPoint(v, A v)) = q(graphPoint(0 - v, w - A v)).
(iii) By the isometry property and (G4): |y - P_A y|^2 = |-v|^2 + |w - A v|^2 = |v|^2 + |w - A v|^2, i.e. |y - P_A y| = (|v|^2 + |w - A v|^2)^(1/2).
(iv) Put a := |w - A v|, b := |v|, c := ||A||, all >= 0. By the triangle inequality and |A v| <= ||A|| |v|: |w| = |(w - A v) + A v| <= a + |A v| <= a + c b.
(v) Cauchy-Schwarz in R^2: (1 + c^2)(a^2 + b^2) - (a + c b)^2 = (c a - b)^2 >= 0. Since a + c b >= 0, taking square roots gives a + c b <= ((1 + c^2)(b^2 + a^2))^(1/2) = (1 + c^2)^(1/2) (b^2 + a^2)^(1/2).
By (iii)-(v), |w| <= (1 + ||A||^2)^(1/2) |y - P_A y|, which is (P2).

5. (W). Let W := q o g_A : R^n -> R^N.
- W is linear (a composition of linear maps). It is continuous because R^n is finite-dimensional (LinearMap.toContinuousLinearMap) and q is continuous.
- W v = q(graphPoint(v, A v)) by definition.
- For every v, by the isometry property, (G4), |A v| <= ||A|| |v| and monotonicity of the square root:
|W v| = |graphPoint(v, A v)| = (|v|^2 + |A v|^2)^(1/2) <= ((1 + ||A||^2)|v|^2)^(1/2) = (1 + ||A||^2)^(1/2) |v|.
- Since (1 + ||A||^2)^(1/2) >= 0, the definition of the operator norm (ContinuousLinearMap.opNorm_le_bound) gives ||W|| <= (1 + ||A||^2)^(1/2).

6. (D). By linearity of q, (G2), v - v = 0 and (A - B) v = A v - B v:
q(graphPoint(v, A v)) - q(graphPoint(v, B v)) = q(graphPoint(v, A v) - graphPoint(v, B v)) = q(graphPoint(v - v, A v - B v)) = q(graphPoint(0, (A - B) v)).

7. Steps 3-6 prove the four conjuncts for all n, l, q and every A (and B).

## Key steps

1. Coordinate algebra of graphPoint: additivity, subtraction, homogeneity, and |graphPoint(a, b)|^2 = |a|^2 + |b|^2
2. v -> graphPoint(v, A v) is linear, so span(range) = range and G_A = {q(graphPoint(v, A v)) : v}
3. (P1): q(graphPoint(x, A x)) lies in G_A and is fixed by P_A
4. (P2): P_A y = q(graphPoint(v, A v)), |y - P_A y|^2 = |v|^2 + |w - A v|^2, then the triangle inequality and (a + c b)^2 <= (1 + c^2)(a^2 + b^2)
5. (W): W = q o g_A is continuous linear with |W v|^2 = |v|^2 + |A v|^2 <= (1 + ||A||^2)|v|^2
6. (D): linearity of q and graphPoint subtraction

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
