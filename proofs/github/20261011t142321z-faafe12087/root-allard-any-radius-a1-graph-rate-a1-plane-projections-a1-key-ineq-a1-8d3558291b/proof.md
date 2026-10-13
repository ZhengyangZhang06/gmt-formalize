# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_any_radius-a1.graph_rate-a1.plane_projections-a1`
- Child DAG node: `root.allard_any_radius-a1.graph_rate-a1.plane_projections-a1.key_ineq-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation.
- N := n + l, so Amb n l = R^N = Rn N, and hsNormSq of a map of R^N is computed in the standard basis of R^N.
- For continuous linear C : R^n -> R^l, P_C is the orthogonal projection onto G_C := q(span{graphPoint(v, C v) : v in R^n}).
- e_i (i < n) is the standard basis of R^n; o is composition.

Cited sibling results:
- hs_ideal (H3): for continuous linear X : R^a -> R^b and W : R^c -> R^a, hsNormSq(X o W) <= ||W||^2 hsNormSq X.
- hs_proj_split (S2): for subspaces K, L of R^a, hsNormSq(P_K - P_L) = hsNormSq((P_K - P_L) o P_K) + hsNormSq((P_K - P_L) o P_L).
- graph_param, for this q and all continuous linear C, D:
  - (P1) P_C(q(graphPoint(x, C x))) = q(graphPoint(x, C x));
  - (P2) |w| <= (1 + ||C||^2)^(1/2) |q(graphPoint(0, w)) - P_C q(graphPoint(0, w))|;
  - (W) there is a continuous linear W : R^n -> R^N with W v = q(graphPoint(v, C v)) and ||W|| <= (1 + ||C||^2)^(1/2);
  - (D) q(graphPoint(v, C v)) - q(graphPoint(v, D v)) = q(graphPoint(0, (C - D) v)).

0. Elementary facts.
(a) hsNormSq M >= 0 for every M (a sum of squares).
(b) hsNormSq(-M) = hsNormSq M, since |(-M) e_i| = |M e_i|.

1. One-sided estimate. For every ordered pair (C, D) of continuous linear maps R^n -> R^l:
hsNormSq(C - D) <= (1 + ||C||^2)(1 + ||D||^2) hsNormSq((P_C - P_D) o P_C).
Proof. Put Z := P_C - P_D and choose W for C by (W). Since 0 <= ||W|| <= (1 + ||C||^2)^(1/2), we have ||W||^2 <= 1 + ||C||^2.
(i) Fix i < n and put e := e_i and y := q(graphPoint(0, (C - D) e)).
- By (D), W e = q(graphPoint(e, C e)) = q(graphPoint(e, D e)) + y.
- By (P1) for C, P_C(W e) = W e.
- By (P1) for D and linearity of P_D, P_D(W e) = q(graphPoint(e, D e)) + P_D y.
Hence (Z o W) e = P_C(W e) - P_D(W e) = q(graphPoint(e, D e)) + y - q(graphPoint(e, D e)) - P_D y = y - P_D y.
(ii) By (P2) for D with w := (C - D) e:
|(C - D) e| <= (1 + ||D||^2)^(1/2) |y - P_D y| = (1 + ||D||^2)^(1/2) |(Z o W) e|.
Both sides are >= 0, so squaring gives |(C - D) e_i|^2 <= (1 + ||D||^2) |(Z o W) e_i|^2. Summing over i < n:
hsNormSq(C - D) <= (1 + ||D||^2) hsNormSq(Z o W).
(iii) By (P1) for C, P_C(W v) = W v for every v, so Z o W = (Z o P_C) o W. Apply (H3) with X := Z o P_C (a map R^N -> R^N) and W : R^n -> R^N, then use ||W||^2 <= 1 + ||C||^2 and 0(a):
hsNormSq(Z o W) = hsNormSq((Z o P_C) o W) <= ||W||^2 hsNormSq(Z o P_C) <= (1 + ||C||^2) hsNormSq(Z o P_C).
(iv) Multiply (iii) by 1 + ||D||^2 >= 0 and combine with (ii):
hsNormSq(C - D) <= (1 + ||D||^2)(1 + ||C||^2) hsNormSq(Z o P_C) = (1 + ||C||^2)(1 + ||D||^2) hsNormSq((P_C - P_D) o P_C).

2. Put c := (1 + ||A||^2)(1 + ||B||^2). Step 1 for (C, D) = (A, B) gives hsNormSq(A - B) <= c hsNormSq((P_A - P_B) o P_A).

3. Step 1 for (C, D) = (B, A) gives hsNormSq(B - A) <= (1 + ||B||^2)(1 + ||A||^2) hsNormSq((P_B - P_A) o P_B).
- B - A = -(A - B) and (P_B - P_A) o P_B = -((P_A - P_B) o P_B).
- So fact 0(b) and commutativity of the product give hsNormSq(A - B) <= c hsNormSq((P_A - P_B) o P_B).

4. By (S2) with a = N, K := G_A, L := G_B:
hsNormSq(P_A - P_B) = hsNormSq((P_A - P_B) o P_A) + hsNormSq((P_A - P_B) o P_B).
Adding the inequalities of steps 2 and 3:
2 hsNormSq(A - B) <= c (hsNormSq((P_A - P_B) o P_A) + hsNormSq((P_A - P_B) o P_B)) = (1 + ||A||^2)(1 + ||B||^2) hsNormSq(P_A - P_B).

## Key steps

1. One-sided estimate for an ordered pair (C, D): with W from (W), (P1) and (D) give (P_C - P_D)(W e_i) = y_i - P_D y_i, where y_i = q(graphPoint(0, (C - D) e_i))
2. (P2) for D gives |(C - D) e_i|^2 <= (1 + ||D||^2) |(P_C - P_D)(W e_i)|^2; sum over i
3. (P_C - P_D) o W = ((P_C - P_D) o P_C) o W, and (H3) with ||W||^2 <= 1 + ||C||^2 gives the factor 1 + ||C||^2
4. Apply to (A, B) and (B, A); hsNormSq is invariant under negation
5. (S2): hsNormSq(P_A - P_B) = hsNormSq((P_A - P_B) o P_A) + hsNormSq((P_A - P_B) o P_B); add the two one-sided bounds

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
