# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_regularity-a1.graph_plane_algebra-a1`
- Child DAG node: `root.allard_regularity-a1.graph_plane_algebra-a1.graph_normal_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 5 ((Nor)). The parent bounds |y - A x| by (1 + ||A||^2)^(1/2) |graphPoint (x - v) (y - A v)| for every v and takes the infimum over v; here the same estimate is applied at the minimizing point v given by the orthogonal projection, so no infimum is needed.

0. Facts about graphPoint. By definition graphPoint x y = toLp 2 (Fin.append (ofLp x) (ofLp y)), so its coordinate at Fin.castAdd l i is x_i and its coordinate at Fin.natAdd n j is y_j (Fin.append_left, Fin.append_right), and every index of Fin (n+l) has one of these two forms (Fin.addCases). Consequently:
 (a) graphPoint is jointly linear: graphPoint (x + x') (y + y') = graphPoint x y + graphPoint x' y' and graphPoint (c x) (c y) = c graphPoint x y; in particular graphPoint x y - graphPoint x' y' = graphPoint (x - x') (y - y') (compare coordinates);
 (b) ||graphPoint x y||^2 = sum_i x_i^2 + sum_j y_j^2 = ||x||^2 + ||y||^2 (EuclideanSpace.norm_eq together with Fin.sum_univ_add).

1. Let J : R^n -> R^(n+l), J v := graphPoint v (A v). By 0(a) and the linearity of A, J is linear. Hence its range is a subspace, and Gamma_A = span(range J) = range J (Submodule.span_eq applied to LinearMap.range J, whose underlying set is range J by LinearMap.coe_range). So every element of Gamma_A has the form graphPoint v (A v) for some v in R^n.

2. Let w := q(graphPoint x y) and K := Gamma_A.map q; K is finite-dimensional, so its orthogonal projection P exists. P w lies in K (it is the coercion of the element orthogonalProjectionOnto w of K). By the definition of Submodule.map, P w = q z for some z in Gamma_A, and by step 1 z = graphPoint v (A v) for some v in R^n. Fix this v.

3. Then w - P w = q(graphPoint x y) - q(graphPoint v (A v)) = q(graphPoint (x - v) (y - A v)) by linearity of q and 0(a). Since q is an isometry, ||w - P w|| = ||graphPoint (x - v) (y - A v)|| =: d, and by 0(b) d^2 = ||x - v||^2 + ||y - A v||^2, d >= 0.

4. Put a := ||x - v|| >= 0 and c := ||y - A v|| >= 0. Since y - A x = (y - A v) + A(v - x), the triangle inequality and ||A(v - x)|| <= ||A|| ||v - x|| <= ||v - x|| = a (using ||A|| <= 1) give ||y - A x|| <= c + a.

5. (c + a)^2 = a^2 + 2ac + c^2 <= 2(a^2 + c^2) = 2 d^2 <= 4 d^2, because 2ac <= a^2 + c^2 (as (a - c)^2 >= 0). Since c + a >= 0 and 2d >= 0, this gives c + a <= 2 d. (This is the parent's Cauchy-Schwarz estimate (1 + ||A||^2)^(1/2) d <= sqrt 2 d <= 2 d at the point v.)

6. Combining steps 3, 4 and 5: ||y - A x|| <= c + a <= 2 d = 2 ||w - P w||, which is the claim (with w = q(graphPoint x y) and P the starProjection of (span{graphPoint v (A v)}).map q).

## Key steps

1. graphPoint is jointly linear and ||graphPoint x y||^2 = ||x||^2 + ||y||^2
2. span{graphPoint v (A v)} is the range of the linear map v |-> graphPoint v (A v), so P w = q(graphPoint v (A v)) for some v
3. ||w - P w|| = ||graphPoint (x - v) (y - A v)|| because q is an isometry
4. ||y - A x|| <= ||y - A v|| + ||x - v|| <= sqrt 2 ||w - P w|| <= 2 ||w - P w|| using ||A|| <= 1

## Reference use

### local-project

Queries:
- `diff GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Contract.lean; diff GMT/Ch05/Submission.lean <snapshot>/project/GMT/Ch05/Submission.lean`
- `rg -c 'allard52_gpa' <snapshot>/project; grep -c allard52_gpa <run>/dag.json`
- `python: list dag.json nodes with lean_name, status, lean_statement (name reservation; reuse candidates aetp_starProjection_range_continuousOn, hsNorm_starProjection_trace_identities, rsod_graphPoint_eq_finAddEquivProd_symm, rsod_norm_graphPoint_sq)`
- `rg -n 'exists_orthonormalBasis_extension_of_card_eq|starProjection_map|orthogonalProjection_map_apply' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace`
- `rg -n 'theorem ContDiffOn.exists_lipschitzOnWith|theorem Convex.norm_image_sub_le_of_norm_fderiv_le|lipschitzOnWith_of_nnnorm_fderiv_le' <snapshot>/mathlib/Mathlib/Analysis`
- `grep -rn 'theorem contDiffAt_ringInverse\|theorem hasFDerivAt_ringInverse' <snapshot>/mathlib/Mathlib/Analysis/Calculus/`
- `grep -n 'class HasOrthogonalProjection\|theorem eq_starProjection_of_mem_of_inner_eq_zero\|theorem starProjection_map_apply' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `grep -n 'repr_symm_single\|sum_sq_inner_right\|finrank_euclideanSpace_fin\|stdOrthonormalBasis' PiL2.lean; grep finrank_add_finrank_orthogonal Projection/FiniteDimensional.lean; grep 'ContDiff.fderiv_right' ContDiff/Comp.lean; grep 'HasFDerivAt.clm_comp' FDeriv/CompCLM.lean; grep opNorm_le_bound Normed/Operator/Basic.lean; grep norm_eq_of_L2 Normed/Lp/PiLp.lean`
- `git show 9f89be4c6f3781e8d518dff64e552c3d1263533e -- GMT/Ch05/Submission.lean; git show --stat 164f08e449a335e8b0962c8f511579e3e102246a 18a457c495d0ee5b9257b1656886d4da963c6fd8`
- `lean GMT/Ch05/Submission.lean -o /tmp/gpa-decomp-3B7ONF/build/lib/lean/GMT/Ch05/Submission.olean; lean Probe.lean and Probe2.lean (#check of every cited lemma; ContinuousLinearMap.adjoint and LinearMap.adjoint; instance probes)`
- `lean Assembly.lean (7 child types by sorry + parent frozen type proved); lean BilipFromSiblings.lean (child 7 proved from children 1 and 6); lean_contract.validate_lean_statement on all 7 statements`
- `sed -n 1015,1180p book/sources/chapter-05-source.txt (Simon 5.2 proof, p. 123)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-plane-algebra-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/swarm-configs/1240ad3fa3ef4b348796c806151f8f30.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-05-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/gpa-decomp-3B7ONF/check/Probe.lean`
- `/tmp/gpa-decomp-3B7ONF/check/Probe2.lean`
- `/tmp/gpa-decomp-3B7ONF/check/Assembly.lean`
- `/tmp/gpa-decomp-3B7ONF/check/BilipFromSiblings.lean`
- `/tmp/gpa-scripts/check.py`

Snapshot pins: project ea5607598f3133b40a13241f2e51517a8c6423cd, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace Contract.lean and Submission.lean are byte-identical to the snapshot copies.

Names.
- 'allard52_gpa' has no match in the snapshot project or in dag.json (214 nodes), so the seven bare names are globally unique.
- Accepted precedents: aetp_starProjection_range_continuousOn (commit 9f89be4c builds the projection formula with a hand-made transpose), hsNorm_starProjection_trace_identities (164f08e4) and rsod_graphPoint_eq_finAddEquivProd_symm (18a457c4). None is reused, because none removes a child.
- rsod_norm_graphPoint_sq is still decomposing under another parent, so it cannot be shared.

Mathlib lemmas found, all inside the import closure:
- Orthonormal.exists_orthonormalBasis_extension_of_card_eq (PiL2.lean:1044), OrthonormalBasis.repr_symm_single (PiL2.lean:430), OrthonormalBasis.sum_sq_inner_right (PiL2.lean:528), finrank_euclideanSpace_fin (PiL2.lean:205), stdOrthonormalBasis (PiL2.lean:1073);
- HasOrthogonalProjection, a Prop class (Projection/Basic.lean:48), eq_starProjection_of_mem_of_inner_eq_zero (Projection/Basic.lean:180), starProjection_map_apply (Projection/Basic.lean:358), finrank_add_finrank_orthogonal (Projection/FiniteDimensional.lean:110);
- ContDiffOn.exists_lipschitzOnWith (ContDiff/RCLike.lean:149), ContDiff.fderiv_right (ContDiff/Comp.lean:750), contDiffAt_ringInverse (ContDiff/Operations.lean:772), hasFDerivAt_ringInverse (FDeriv/Mul.lean:661), HasFDerivAt.clm_comp (FDeriv/CompCLM.lean:61);
- Convex.norm_image_sub_le_of_norm_fderiv_le (MeanValue.lean:499), opNorm_le_bound (Normed/Operator/Basic.lean:196), PiLp.norm_eq_of_L2 (PiLp.lean:780).

Import gaps and instances.
- ContinuousLinearMap.adjoint and LinearMap.adjoint are Unknown constants after `import GMT.Ch05.Submission`, so the transposes are built by hand.
- These instances are inferred: IsCompact (closedBall 0 1) and FiniteDimensional in Rn n ->L Rn l, and HasSummableGeomSeries (Rn n ->L Rn n).

Lean checks.
- Assembly.lean proves the parent's exact frozen type from the 7 child types, with no other sorry.
- BilipFromSiblings.lean proves child 7 from children 1 and 6.

Simon's printed text (p. 123) gives P = [[I, Df],[Df^t, O]] + F(Df) with F(0) = 0, DF(0) = 0 and |F(p1) - F(p2)| <= C(|p1| + |p2|)|p1 - p2|. This matches children 6-7.

Numeric check: |DPi(0)H|^2 / |H|^2 = 2, and the Gp ratio lies in [1.77, 1.96] for |A|, |B| <= 1/4.
