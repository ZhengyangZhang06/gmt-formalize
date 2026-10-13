# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_any_radius-a1.graph_rate-a1.la_basics-a1`
- Child DAG node: `root.allard_any_radius-a1.graph_rate-a1.la_basics-a1.rotated_plane-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation. N := n + l; eps_k (k in Fin N) are the standard basis vectors of R^N = Amb n l and e_i (i in Fin n) those of R^n. horizontalPlane = span{eps_{castAdd l i} : i in Fin n}, and T_0 = rotatedPlane q = {q(h) : h in horizontalPlane}. From the sibling theorem graph_coords (Submission.any_radius_gr_la_graphPoint_algebra) at n, l we use: (C1) for all a in R^n, b in R^l and i in Fin n, (graphPoint a b)_{castAdd l i} = a_i; (C2) for all a in R^n, b in R^l and j in Fin l, (graphPoint a b)_{natAdd n j} = b_j; and for all a, a' in R^n, b, b' in R^l and t in R: (L1) graphPoint(a + a', b + b') = graphPoint a b + graphPoint a' b'; (L2) graphPoint(a - a', b - b') = graphPoint a b - graphPoint a' b'; (L3) graphPoint(t a, t b) = t graphPoint a b; (L4) |graphPoint a b|^2 = |a|^2 + |b|^2; (IP) <graphPoint a b, graphPoint a' b'> = <a, a'> + <b, b'>.

1. eps_{castAdd l i} = graphPoint(e_i, 0) for every i in Fin n. Compare coordinates; every index of Fin N is castAdd l i' (i' in Fin n) or natAdd n j (j in Fin l) (Fin.addCases). At castAdd l i' the left side is 1 if castAdd l i' = castAdd l i, i.e. i' = i (castAdd l is injective, Fin.castAdd_injective), and 0 otherwise; the right side is (e_i)_{i'} by (C1), which is also 1 if i' = i and 0 otherwise. At natAdd n j the left side is 0, because natAdd n j is not castAdd l i (their values satisfy n + j >= n > i); the right side is the j-th coordinate of 0 in R^l, i.e. 0, by (C2).

2. The map G : R^n -> R^N, G(c) := graphPoint(c, 0), is linear: G(c + c') = graphPoint(c + c', 0 + 0) = G(c) + G(c') by (L1), and G(t c) = graphPoint(t c, t 0) = t G(c) by (L3), using 0 + 0 = 0 and t 0 = 0 in R^l.

3. horizontalPlane = {graphPoint(c, 0) : c in R^n}.
(a) For c in R^n write c = sum_i c_i e_i. By step 2 and step 1, graphPoint(c, 0) = G(c) = sum_i c_i G(e_i) = sum_i c_i eps_{castAdd l i}, a linear combination of the spanning vectors; hence graphPoint(c, 0) lies in horizontalPlane.
(b) Every h in horizontalPlane, the span of the finite family (eps_{castAdd l i})_{i in Fin n}, is a linear combination h = sum_i c_i eps_{castAdd l i} for some reals c_i (Submodule.mem_span_range_iff_exists_fun). By step 1 and step 2, h = sum_i c_i G(e_i) = G(sum_i c_i e_i) = graphPoint(sum_i c_i e_i, 0).
(For n = 0 both sets are {0}: the span of the empty family is {0}, and the empty sums give h = 0 = G(0).)

4. Orthogonality. For every b in R^l and every h in horizontalPlane, <graphPoint(0, b), h> = 0: by step 3(b), h = graphPoint(c, 0) for some c in R^n, and by (IP), <graphPoint(0, b), graphPoint(c, 0)> = <0, c> + <b, 0> = 0 + 0 = 0.

5. q preserves inner products: <q x, q y> = <x, y> for all x, y in R^N. Indeed q is linear and preserves norms, so by the polarization identity 4<x, y> = |x + y|^2 - |x - y|^2 we get 4<q x, q y> = |q(x + y)|^2 - |q(x - y)|^2 = |x + y|^2 - |x - y|^2 = 4<x, y> (Mathlib: LinearIsometryEquiv.inner_map_map).

6. (L5). Fix a in R^n, b in R^l and put v := q(graphPoint(a, b)), k := q(graphPoint(a, 0)).
(i) k lies in T_0, because graphPoint(a, 0) lies in horizontalPlane by step 3(a).
(ii) v - k = q(graphPoint(a, b) - graphPoint(a, 0)) by linearity of q, and graphPoint(a, b) - graphPoint(a, 0) = graphPoint(a - a, b - 0) = graphPoint(0, b) by (L2); so v - k = q(graphPoint(0, b)).
(iii) Every w in T_0 is w = q(h) with h in horizontalPlane, and <v - k, w> = <q(graphPoint(0, b)), q(h)> = <graphPoint(0, b), h> = 0 by (ii), step 5 and step 4.
(iv) T_0 is a subspace of the finite-dimensional space R^N, hence finite-dimensional and complete, so its orthogonal projection P_{T_0} exists; P_{T_0} v lies in T_0 and v - P_{T_0} v is orthogonal to T_0. Characterization: if k lies in T_0 and <v - k, w> = 0 for all w in T_0, then P_{T_0} v = k. Proof: d := P_{T_0} v - k lies in T_0, and d = (v - k) - (v - P_{T_0} v), so |d|^2 = <v - k, d> - <v - P_{T_0} v, d> = 0 - 0 = 0, whence d = 0 (Mathlib: Submodule.eq_starProjection_of_mem_of_inner_eq_zero).
By (i), (iii) and (iv), P_{T_0}(q(graphPoint(a, b))) = q(graphPoint(a, 0)).

7. Distance to a complete subspace. Let K be a complete subspace of R^N with orthogonal projection P := P_K, and let v be in R^N. For every k in K, v - Pv is orthogonal to K and Pv - k lies in K, so by Pythagoras |v - k|^2 = |(v - Pv) + (Pv - k)|^2 = |v - Pv|^2 + |Pv - k|^2 >= |v - Pv|^2, i.e. |v - k| >= |v - Pv|. Since Pv itself lies in K, the infimum infDist(v, K) = inf_{k in K} |v - k| equals |v - Pv| = dist(v, Pv) (Mathlib: Submodule.dist_starProjection_eq_infDist).

8. (L6). Fix a, b and let v := q(graphPoint(a, b)). By step 7 with K = T_0 (complete by step 6(iv)) and by (L5) from step 6, infDist(v, T_0) = |v - P_{T_0} v| = |q(graphPoint(a, b)) - q(graphPoint(a, 0))| = |q(graphPoint(0, b))| by step 6(ii), and this equals |graphPoint(0, b)| because q is an isometry. By (L4), |graphPoint(0, b)|^2 = |0|^2 + |b|^2 = |b|^2, and both norms are >= 0, so |graphPoint(0, b)| = |b|. Hence infDist(q(graphPoint(a, b)), T_0) = |b|.

9. (L7). The standard basis (eps_k)_{k in Fin N} is orthonormal (EuclideanSpace.orthonormal_single), hence linearly independent; composing with the injective map castAdd l : Fin n -> Fin N (Fin.castAdd_injective; LinearIndependent.comp), the family (eps_{castAdd l i})_{i in Fin n} is linearly independent. The span of a linearly independent family indexed by a finite type has finrank equal to the number of indices (finrank_span_eq_card), so finrank horizontalPlane = card(Fin n) = n. T_0 is the image of horizontalPlane under the linear equivalence underlying q, which restricts to a linear isomorphism from horizontalPlane onto T_0; linear isomorphisms preserve finrank (LinearEquiv.finrank_map_eq). Hence finrank T_0 = n.

Every step is valid for all n, l >= 0, including n = 0 (where horizontalPlane = T_0 = {0}, finrank 0) and l = 0.

## Key steps

1. eps_{castAdd l i} = graphPoint(e_i, 0) by coordinates (C1), (C2); c -> graphPoint(c, 0) is linear by (L1), (L3); hence horizontalPlane = {graphPoint(c, 0) : c in R^n}
2. (IP) gives <graphPoint(0, b), graphPoint(c, 0)> = 0, so graphPoint(0, b) is orthogonal to horizontalPlane; the linear isometry q preserves inner products
3. q(graphPoint(a, 0)) lies in T_0 and q(graphPoint(a, b)) - q(graphPoint(a, 0)) = q(graphPoint(0, b)) (by (L2)) is orthogonal to T_0, so the characterization of the orthogonal projection gives (L5)
4. Pythagoras gives infDist(v, K) = |v - P_K v| for complete K; with (L5), the isometry q and (L4) this is |graphPoint(0, b)| = |b| (L6)
5. The standard basis vectors at the distinct indices castAdd l i are orthonormal, hence independent, so finrank horizontalPlane = n, preserved by the linear equivalence q (L7)

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean; cmp <snapshot>/project/GMT/Ch05/Submission.lean GMT/Ch05/Submission.lean; diff <snapshot>/project/GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Submission.lean`
- `sed -n 30,116p GMT/Ch05/Contract.lean (Amb, Rn, hsNormSq, hsNorm, graphPoint, horizontalPlane, rotatedPlane)`
- `python3 -I scan of <run>/dag.json (353 nodes: id, lean_name, lean_statement, status) for related nodes lip_approx_graph_coordinates, rsod_norm_graphPoint_sq, rsod_graphPoint_eq_finAddEquivProd_symm, lgc_hsNormSq_bounds, hsNorm_starProjection_trace_identities, aal_l1th_projection_algebra, arp_opNorm_le_hsNorm, allard52_gpa_hsNorm_bounds, arp_rotatedPlane_graphPoint_coords, tdo_graph_plane_dist`
- `python3 -I dump of <run>/nodes/root-allard-any-radius-a1-graph-rate-a1/decomposition-v2.json and of this node's parent-child-handoff.json and parent-supplied-plan.md`
- `grep -n -i helper <run>/problem.md (line 477: every new named helper must have its own theorem node)`
- `git show humanize-recursive/gmt-ch05/20261011t142321z-faafe12087/root-lipschitz-approximation-a1-graph-coordinates-a1-a1:GMT/Ch05/Submission.lean; git show humanize-recursive/gmt-ch05/20261011t142321z-faafe12087/root-lipschitz-graph-corollary-a1-hole-estimate-a1-hs-norm-bounds-a1-a1:GMT/Ch05/Submission.lean`
- `rg -n 'theorem (eq_starProjection_of_mem_of_inner_eq_zero|starProjection_minimal|norm_starProjection_apply_le|starProjection_norm_le|sub_starProjection_mem_orthogonal|...)' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/; sed -n 160,240p and 380,420p of Projection/Basic.lean`
- `rg -n 'theorem finrank_span_eq_card|theorem finrank_map_eq|finrank_range_of_inj' <snapshot>/mathlib/Mathlib; rg -n 'inner_map_map' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean; rg -n 'orthonormal_single|inner_single_right|norm_single' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean; rg -n 'mem_span_range_iff_exists_fun|sum_mul_sq_le_sq_mul_sq' <snapshot>/mathlib/Mathlib`
- `grep -rl any_radius_gr_la_ <run> (all artifacts); rg -l any_radius_gr_la_ <snapshot>/project; git grep -l any_radius_gr_la_ over all refs/heads and refs/remotes -- '*.lean'`
- `python3 -I: contract_scope(Contract.lean, 'GMT.Ch05.main_theorem') from verifier/gmt-compare.py to replay the comparator's child scope`
- `lake build GMT.Ch05.Submission in /tmp/la-basics-split-xQ1XeA/proj (fresh copy of the pinned snapshot project, .lake/packages symlinked to lake-packages-25730c7c)`
- `lake env lean Checks/Types.lean, Checks/Coords.lean, Checks/Rotated.lean, Checks/HS.lean, Checks/All.lean, Checks/CmpForm.lean (+ reviewer's review/AllAx.lean, review/Interface.lean)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1-la-basics-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1-la-basics-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/la-basics-split-xQ1XeA/proj/Checks/Types.lean`
- `/tmp/la-basics-split-xQ1XeA/proj/Checks/Coords.lean`
- `/tmp/la-basics-split-xQ1XeA/proj/Checks/Rotated.lean`
- `/tmp/la-basics-split-xQ1XeA/proj/Checks/HS.lean`
- `/tmp/la-basics-split-xQ1XeA/proj/Checks/All.lean`
- `/tmp/la-basics-split-xQ1XeA/proj/Checks/CmpForm.lean`
- `/tmp/la-basics-split-xQ1XeA/review/AllAx.lean`
- `/tmp/la-basics-split-xQ1XeA/review/Interface.lean`

Snapshot
- Pinned at project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d.
- The snapshot's Contract.lean and Submission.lean are byte-identical to the workspace copies, and Submission equals Contract.

Definitions that shape the split
- graphPoint x y = toLp(Fin.append x y).
- horizontalPlane = span of single (castAdd ℓ i) 1.
- rotatedPlane q = the map of horizontalPlane under q.toLinearEquiv.
- hsNormSq A = Σ_i ‖A (single i 1)‖^2, and hsNorm = sqrt hsNormSq.

Mathlib facts behind the child proofs (all used in the compiled proofs)
- Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Projection/Basic.lean:180)
- Submodule.dist_starProjection_eq_infDist (:234)
- Submodule.norm_starProjection_apply_le (:411)
- LinearIsometryEquiv.inner_map_map (InnerProductSpace/LinearMap.lean:117)
- finrank_span_eq_card (Dimension/Constructions.lean:463)
- LinearEquiv.finrank_map_eq (Dimension/Finrank.lean:120)
- EuclideanSpace.orthonormal_single (PiL2.lean:349)
- Also: Submodule.mem_span_range_iff_exists_fun, Fin.sum_univ_add, EuclideanSpace.norm_sq_eq, PiLp.inner_apply, Finset.sum_mul_sq_le_sq_mul_sq, ContinuousLinearMap.le_opNorm / opNorm_le_bound.

Related DAG nodes in other branches
- Accepted: lip_approx_graph_coordinates, rsod_norm_graphPoint_sq, lgc_hsNormSq_bounds, hsNorm_starProjection_trace_identities.
- Their frozen types differ from every proposed child, so no identical declaration is reusable.
- Their accepted proofs confirmed the coordinate and Cauchy-Schwarz idioms used here.

Policy
- problem.md:477: every new named helper needs its own node, so a leaf is a single declaration.

No-match results
- 'any_radius_gr_la_' occurs in no run artifact, no snapshot project file, and no *.lean file on any git ref. The 3 proposed names are free.

Lean
- The 3 children and the assembled parent compile with only propext, Classical.choice and Quot.sound.
- All 4 statements elaborate in the exact comparator child scope replayed from gmt-compare.py, and each closes by `exact Submission.<lean_name>`.
