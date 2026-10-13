# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_tilt_algebra-a1`
- Child DAG node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_tilt_algebra-a1.vertical_trace_sum-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Context. This is the trace identity of Simon 4.4 in the form used in Simon 4.5 (13): step 6 of the parent proof, for an arbitrary n-dimensional subspace S. The parent applies it to the graph plane S = span{q(graphPoint v (D v)) : v in R^n}, whose dimension n is supplied by the sibling graph_plane_finrank. Prerequisites:
- projection_algebra (PA, Submission.hsNorm_starProjection_trace_identities), part (iii): for every m and all subspaces P', T' of R^m with finrank P' = finrank T', trace(T'-perp.starProjection o P'.starProjection) = hsNormSq(P'.starProjection - T'.starProjection) / 2 (LinearMap.trace of the composite of the underlying linear maps). It is applied with m = n + l; Amb n l is by definition Rn (n + l).
- graph_coords (GA, Submission.any_radius_gr_la_graphPoint_algebra): (C1) (graphPoint a b)_{castAdd l i} = a_i; (C2) (graphPoint a b)_{natAdd n j} = b_j; (L3) graphPoint (t a) (t b) = t graphPoint a b.
- rotated_plane (RP, Submission.any_radius_gr_la_rotatedPlane_facts): (L5) P(q(graphPoint a b)) = q(graphPoint a 0); (L7) finrank (rotatedPlane q) = n.

Notation. Fix n, l, q and S with finrank S = n. N := n + l; eps_k := EuclideanSpace.single k 1 in R^N (k in Fin N); e_i := EuclideanSpace.single i 1 in R^n; d_j := EuclideanSpace.single j 1 in R^l; e'_j := q(graphPoint 0 d_j); T := rotatedPlane q; p := S.starProjection, P := T.starProjection, Q := T-perp.starProjection. All three projections exist since R^N is finite-dimensional.

1. Index facts. Every k in Fin N is castAdd l i for some i in Fin n or natAdd n j for some j in Fin l (Fin.addCases). castAdd l and natAdd n are injective, and castAdd l i' is never natAdd n j', because the values satisfy i' < n <= n + j'.
2. Basis vectors as graph points: eps_{castAdd l i} = graphPoint e_i 0 and eps_{natAdd n j} = graphPoint 0 d_j. Compare coordinates (ext, then the two cases of step 1). The coordinate of eps_k at k' is 1 if k' = k and 0 otherwise (EuclideanSpace.single_apply / PiLp.single_apply).
 - At castAdd l i': eps_{castAdd l i} has 1 iff i' = i (injectivity); graphPoint e_i 0 has (e_i)_{i'} by (C1), also 1 iff i' = i. eps_{natAdd n j} has 0 there (step 1); graphPoint 0 d_j has 0_{i'} = 0 by (C1).
 - At natAdd n j': eps_{castAdd l i} has 0 (step 1) and graphPoint e_i 0 has 0_{j'} = 0 by (C2). eps_{natAdd n j} has 1 iff j' = j (injectivity), and graphPoint 0 d_j has (d_j)_{j'} by (C2), also 1 iff j' = j.
3. graphPoint 0 0 = 0 (in R^N): by (L3) with t = 0, a = 0 and b = 0, graphPoint (0 • 0) (0 • 0) = 0 • graphPoint 0 0 = 0, where • is scalar multiplication and 0 • 0 = 0 in R^n and in R^l.
4. Orthonormal basis. b_k := q(eps_k) (k in Fin N) is an orthonormal basis of R^N: it is the standard orthonormal basis EuclideanSpace.basisFun mapped by the linear isometry equivalence q (OrthonormalBasis.map; (b.map q) k = q(b k)). By step 2, b_{castAdd l i} = q(graphPoint e_i 0) and b_{natAdd n j} = q(graphPoint 0 d_j) = e'_j.
5. Trace in an orthonormal basis. For every linear map L of R^N, trace L = sum_{k in Fin N} <b_k, L b_k>. Indeed trace L is the trace of the matrix of L in the basis b (LinearMap.trace_eq_matrix_trace with b.toBasis), whose (k, k) entry is the k-th coordinate of L b_k, and the k-th coordinate of a vector x in an orthonormal basis is <b_k, x> (LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply). (Mathlib also states this as LinearMap.trace_eq_sum_inner in Mathlib.Analysis.InnerProductSpace.Trace, which the contract does not import; the matrix route needs no new import.)
6. Apply step 5 to L := Q o p. Since Q is self-adjoint (Submodule.inner_starProjection_left_eq_right for T-perp), <b_k, Q(p b_k)> = <Q b_k, p b_k>. Also Q x = x - P x for every x (Submodule.starProjection_orthogonal_val).
7. Horizontal terms vanish. Let y := b_{castAdd l i} = q(graphPoint e_i 0). By (L5) (with a = e_i and second argument 0), P y = q(graphPoint e_i 0) = y. So Q y = y - P y = 0, and <Q y, p y> = <0, p y> = 0.
8. Vertical terms. By (L5) (with a = 0 and second argument d_j), P e'_j = q(graphPoint 0 0) = q(0) = 0 (step 3 and linearity of q). So Q e'_j = e'_j - 0 = e'_j and the term is <e'_j, p e'_j>. By self-adjointness and idempotence of p (p(p x) = p x since p x lies in S), <e'_j, p e'_j> = <p e'_j, p e'_j> = |p e'_j|^2.
9. Split the sum of step 5 over the two kinds of indices (Fin.sum_univ_add, the bijection of step 1): trace(Q o p) = sum_{i in Fin n} 0 + sum_{j in Fin l} |p e'_j|^2 = sum_{j in Fin l} |p e'_j|^2, by steps 6-8.
10. finrank S = n by hypothesis and finrank T = n by (L7), so finrank S = finrank T. PA(iii) with m = n + l, P' := S and T' := T gives trace(Q o p) = hsNormSq(p - P) / 2.
11. Steps 9 and 10 give sum_{j in Fin l} |p e'_j|^2 = hsNormSq(S.starProjection - (rotatedPlane q).starProjection) / 2. All steps hold for n = 0 or l = 0 as well (the corresponding sums are empty). QED

Remark (verified Lean realization; not part of the mathematical argument). Placed inside `namespace Submission` of the Submission file (within namespace GMT.Ch05 with the contract's opens; Lean v4.35.0-rc3, Mathlib 25730c7c) as `theorem gwe_gta_vertical_trace_sum : <frozen type> := by` followed by the body below, it compiled with sorry stubs of the sibling theorem(s) hsNorm_starProjection_trace_identities, any_radius_gr_la_graphPoint_algebra, any_radius_gr_la_rotatedPlane_facts in scope. The same tactic body with the sibling propositions as hypotheses has #print axioms [propext, Classical.choice, Quot.sound].
  have hPA := hsNorm_starProjection_trace_identities
  have hGA := any_radius_gr_la_graphPoint_algebra
  have hRP := any_radius_gr_la_rotatedPlane_facts
  intro n ℓ q S hS
  have hcast : ∀ i : Fin n, EuclideanSpace.single (Fin.castAdd ℓ i) (1 : ℝ) = graphPoint (EuclideanSpace.single i (1 : ℝ)) (0 : Rn ℓ) := by
    intro i
    ext k
    refine Fin.addCases (fun i' => ?_) (fun j' => ?_) k
    · rw [(hGA n ℓ).1, PiLp.single_apply, PiLp.single_apply]
      simp [Fin.castAdd_inj]
    · rw [(hGA n ℓ).2.1, PiLp.single_apply]
      have hne : Fin.natAdd n j' ≠ Fin.castAdd ℓ i := by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      simp [hne]
  have hnat : ∀ j : Fin ℓ, EuclideanSpace.single (Fin.natAdd n j) (1 : ℝ) = graphPoint (0 : Rn n) (EuclideanSpace.single j (1 : ℝ)) := by
    intro j
    ext k
    refine Fin.addCases (fun i' => ?_) (fun j' => ?_) k
    · rw [(hGA n ℓ).1, PiLp.single_apply]
      have hne : Fin.castAdd ℓ i' ≠ Fin.natAdd n j := by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      simp [hne]
    · rw [(hGA n ℓ).2.1, PiLp.single_apply, PiLp.single_apply]
      simp [Fin.natAdd_inj]
  have hzero : graphPoint (0 : Rn n) (0 : Rn ℓ) = 0 := by
    have h := (hGA n ℓ).2.2.2.2.1 0 0 0
    simpa using h
  set T := rotatedPlane q with hT
  have hfin : Module.finrank ℝ S = Module.finrank ℝ T := by rw [hS, (hRP n ℓ q).2.2]
  have htr := hPA.2.2 (n + ℓ) S T hfin
  let b : OrthonormalBasis (Fin (n + ℓ)) ℝ (Amb n ℓ) := (EuclideanSpace.basisFun (Fin (n + ℓ)) ℝ).map q
  have hb : ∀ k, b k = q (EuclideanSpace.single k 1) := by
    intro k
    simp [b, EuclideanSpace.basisFun_apply]
  have htrace : ∀ f : Amb n ℓ →ₗ[ℝ] Amb n ℓ, LinearMap.trace ℝ (Amb n ℓ) f = ∑ k, inner ℝ (b k) (f (b k)) := by
    intro f
    rw [LinearMap.trace_eq_matrix_trace ℝ b.toBasis f, Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis]
  have hterm_cast : ∀ i : Fin n, inner ℝ (b (Fin.castAdd ℓ i)) (Tᗮ.starProjection (S.starProjection (b (Fin.castAdd ℓ i)))) = 0 := by
    intro i
    rw [← Submodule.inner_starProjection_left_eq_right, hb, hcast, Submodule.starProjection_orthogonal_val,
      hT, (hRP n ℓ q).1, sub_self, inner_zero_left]
  have hterm_nat : ∀ j : Fin ℓ, inner ℝ (b (Fin.natAdd n j)) (Tᗮ.starProjection (S.starProjection (b (Fin.natAdd n j)))) = ‖S.starProjection (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ))))‖ ^ 2 := by
    intro j
    rw [← Submodule.inner_starProjection_left_eq_right, hb, hnat, Submodule.starProjection_orthogonal_val,
      hT, (hRP n ℓ q).1, hzero, map_zero, sub_zero, ← real_inner_self_eq_norm_sq,
      S.inner_starProjection_left_eq_right,
      S.starProjection_eq_self_iff.2 (S.starProjection_apply_mem _)]
  have key := htrace (Tᗮ.starProjection.toLinearMap ∘ₗ S.starProjection.toLinearMap)
  rw [htr] at key
  rw [key, Fin.sum_univ_add]
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  rw [Finset.sum_eq_zero (fun i _ => hterm_cast i), zero_add]
  exact (Finset.sum_congr rfl (fun j _ => hterm_nat j)).symm

## Key steps

1. eps_{castAdd l i} = graphPoint e_i 0 and eps_{natAdd n j} = graphPoint 0 d_j by coordinates (C1), (C2); graphPoint 0 0 = 0 by (L3)
2. b_k := q(eps_k) is an orthonormal basis and trace L = sum_k <b_k, L b_k> (trace of the matrix in b)
3. With Q = I - P self-adjoint: horizontal terms <Q b_k, p b_k> vanish since P fixes q(graphPoint e_i 0) by (L5)
4. Vertical terms: P e'_j = q(graphPoint 0 0) = 0 by (L5), so the term is <e'_j, p e'_j> = |p e'_j|^2
5. trace(Q o p) = sum_j |p e'_j|^2, and PA(iii) with finrank S = n = finrank T (L7) gives trace(Q o p) = hsNormSq(p - P)/2

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
