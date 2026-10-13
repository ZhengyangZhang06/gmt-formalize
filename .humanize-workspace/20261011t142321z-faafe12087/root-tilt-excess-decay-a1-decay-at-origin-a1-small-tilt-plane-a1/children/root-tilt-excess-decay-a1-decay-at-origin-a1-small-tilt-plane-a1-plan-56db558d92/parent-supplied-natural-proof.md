# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1.decay_at_origin-a1.small_tilt_plane-a1`
- Child DAG node: `root.tilt_excess_decay-a1.decay_at_origin-a1.small_tilt_plane-a1.plane_dist_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Provenance (not needed for the argument): extracted from the parent node's proof, where it bounds the distance from the support to the plane T by the distance to the affine-approximation plane T~ plus hsNorm(p_T - p_T~) ||x||; here it is stated for arbitrary subspaces P, Q and an arbitrary point x. The argument below is self-contained.

Notation. N := n + l, so R^{n+l} = EuclideanSpace R (Fin N). A := p_P - p_Q, a continuous linear map R^N -> R^N. Every linear subspace S of R^N is finite-dimensional, hence complete, so its orthogonal projection p_S = S.starProjection exists, and p_S y lies in S for every y.

1. Operator bound by the Hilbert-Schmidt norm. By the sibling lemma hs_norm_bounds (lgc_hsNormSq_bounds) with m = k = N applied to A: 0 <= hsNormSq A and ||A x||^2 <= hsNormSq A * ||x||^2. The square root is monotone on [0, oo), and sqrt(t^2) = t for t >= 0, sqrt(a b) = sqrt(a) sqrt(b) for a >= 0. Hence ||A x|| = sqrt(||A x||^2) <= sqrt(hsNormSq A * ||x||^2) = sqrt(hsNormSq A) * sqrt(||x||^2) = hsNorm A * ||x||.
2. Nearest-point property. For every subspace S of R^N and every y, the orthogonal projection p_S y is a nearest point of S to y, so dist(y, p_S y) = infDist(y, S) (Mathlib: Submodule.dist_starProjection_eq_infDist). With dist(y, w) = ||y - w|| this gives infDist(x, P) = ||x - p_P x|| and infDist(x, Q) = ||x - p_Q x||.
3. Decomposition. x - p_P x = (x - p_Q x) - (p_P x - p_Q x) = (x - p_Q x) - A x, because (p_P - p_Q) x = p_P x - p_Q x. By the triangle inequality ||u - v|| <= ||u|| + ||v||: ||x - p_P x|| <= ||x - p_Q x|| + ||A x||.
4. Conclusion. By steps 2, 3 and 1: infDist(x, P) = ||x - p_P x|| <= ||x - p_Q x|| + ||A x|| = infDist(x, Q) + ||A x|| <= infDist(x, Q) + hsNorm(p_P - p_Q) * ||x||. QED

Lean notes (names that worked under the pinned toolchain; a complete proof of the frozen type was compiled in this decomposition session): have hb := (lgc_hsNormSq_bounds (n + ℓ) (n + ℓ)).2 (P.starProjection - Q.starProjection); for step 1 unfold hsNorm and rewrite with Real.sqrt_sq (norm_nonneg _) (twice) and Real.sqrt_mul hb.1, then Real.sqrt_le_sqrt (hb.2.2 x); for step 2 rw [← P.dist_starProjection_eq_infDist x, ← Q.dist_starProjection_eq_infDist x, dist_eq_norm, dist_eq_norm]; step 3 by congr 1; simp only [FunLike.coe_sub, Pi.sub_apply]; abel, then norm_sub_le and gcongr.

## Key steps

1. ||(p_P - p_Q) x|| <= hsNorm(p_P - p_Q) ||x|| by taking square roots in ||A x||^2 <= hsNormSq A ||x||^2 (hs_norm_bounds)
2. infDist(x, S) = ||x - p_S x|| for S = P, Q (the orthogonal projection is a nearest point)
3. x - p_P x = (x - p_Q x) - (p_P - p_Q) x and the triangle inequality
4. combine: infDist(x, P) <= infDist(x, Q) + hsNorm(p_P - p_Q) ||x||

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; sha256sum GMT/Ch05/Submission.lean GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Contract.lean`
- `python3 -I: list id/lean_name/status/depends_on of the root.tilt_excess_decay-a1 subtree in <run>/dag.json; print the lean_statements of scaled_lp_bounds-a1, tilt_monotone-a1, tangent_plane_facts-a1, decay_at_origin-a1`
- `python3 -I: dag.json lean_statements containing hsNorm (pure HS-norm lemmas and their status); regex search for plane-comparison / infDist-transfer lemmas (hsNormSq (X.starProjection - Y.starProjection), infDist .* <= infDist)`
- `inspect nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-graph-plane-dist-a1/decomposition-v1.json, decomposition-audit-v1.json, decomposition-review-receipt-v1.json (exact-reuse precedent); dag.json children/depends_on of graph_plane_dist-a1 (reuse mapped to existing accepted node ids)`
- `nodes/root-lipschitz-graph-corollary-a1-hole-estimate-a1-hs-norm-bounds-a1/accepted-candidate.json and parent-supplied-natural-proof.md; git show 7372f81c6640dd17bd99bd3c9bbe79675f27d126:GMT/Ch05/Submission.lean (accepted lgc_hsNormSq_bounds inside namespace Submission)`
- `rg -n 'theorem starProjection_norm_le|starProjection_minimal|starProjection_orthogonal|norm_starProjection_le' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/; sed -n 210,245p and 380,392p Projection/Basic.lean`
- `rg -n 'integrableOn_of_bounded|IntegrableOn.of_bound|theorem integrableOn_const' <snapshot>/mathlib/Mathlib/MeasureTheory; rg -n 'theorem setIntegral_const ' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem ofReal_le_iff_le_toReal' <snapshot>/mathlib/Mathlib; rg -n 'theorem rpow_le_one |theorem rpow_le_rpow_of_exponent_ge ' <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean; rg -n 'theorem sqrt_le_sqrt|sqrt_le_left|sqrt_le_iff|sqrt_mul_self|sqrt_sq ' <snapshot>/mathlib/Mathlib/Analysis/Real/Sqrt.lean`
- `rg -l --fixed-strings for tdo_stp_origin_affine_plane / tdo_stp_hsNormSq_sub_le_tiltExcess / tdo_stp_infDist_le_infDist_add_hsNorm / tdo_stp_ over <run>/dag.json <run>/nodes <snapshot>/project <snapshot>/mathlib/Mathlib GMT .lake/packages/simongmt/Poincare (no match)`
- `sed -n 730,860p book/chapter-05.txt (statement of 4.5, Remark 4.6, proof of 4.5 steps (1), (2))`
- `lake env lean -o /tmp/stp-decomp/olean/GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean; /tmp/stp-decomp/runlean.sh Types.lean | Assembly.lean | Full.lean | Iso_tdo_stp_origin_affine_plane.lean | Iso_tdo_stp_hsNormSq_sub_le_tiltExcess.lean | Iso_tdo_stp_infDist_le_infDist_add_hsNorm.lean | ChildrenAxioms.lean | Comparator.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Real/Sqrt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-small-tilt-plane-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-small-tilt-plane-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-graph-plane-dist-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-graph-corollary-a1-hole-estimate-a1-hs-norm-bounds-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-graph-corollary-a1-hole-estimate-a1-hs-norm-bounds-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/tmp/stp-decomp/checks/Types.lean`
- `/tmp/stp-decomp/checks/Assembly.lean`
- `/tmp/stp-decomp/checks/Full.lean`
- `/tmp/stp-decomp/checks/Iso_tdo_stp_origin_affine_plane.lean`
- `/tmp/stp-decomp/checks/Iso_tdo_stp_hsNormSq_sub_le_tiltExcess.lean`
- `/tmp/stp-decomp/checks/Iso_tdo_stp_infDist_le_infDist_add_hsNorm.lean`
- `/tmp/stp-decomp/checks/ChildrenAxioms.lean`
- `/tmp/stp-decomp/checks/Comparator.lean`

The snapshot pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. Its Contract.lean has sha256 c966f51e..., the same as the workspace Contract.lean and Submission.lean.

Mathlib declarations used by the child proofs (paths under mathlib/Mathlib):
- Submodule.dist_starProjection_eq_infDist (Analysis/InnerProductSpace/Projection/Basic.lean:234): the nearest-point property.
- Submodule.starProjection_norm_le (same file, line 386): ||p_S|| <= 1.
- Measure.integrableOn_of_bounded (MeasureTheory/Integral/IntegrableOn.lean:716).
- setIntegral_const (MeasureTheory/Integral/Bochner/Set.lean:524), with integral μ.real s • c.
- ENNReal.ofReal_le_iff_le_toReal (Basic/ENNReal/Real.lean:262).
- Real.rpow_le_one and Real.rpow_le_rpow_of_exponent_ge (Analysis/SpecialFunctions/Pow/Real.lean:661 and 642).
- Real.sqrt_le_sqrt and Real.sqrt_le_left (Analysis/Real/Sqrt.lean:208 and 223).

No-match results:
- Mathlib has no varifold or tilt-excess results.
- The DAG has no accepted lemma comparing two planes via tiltExcess, and none bounding infDist to one plane by infDist to another plus an HS-norm term. any_radius_gr_la_hsNorm_facts (which has hsNormSq(M+N) <= 2hsNormSq M + 2hsNormSq N) is still decomposing and cannot be reused.
- The three new tdo_stp_ names occur nowhere.

Reuse:
- lgc_hsNormSq_bounds is accepted (candidate 7372f81c, comparator passed) with the identical frozen type. It is reused exactly, following the graph_plane_dist-a1 precedent, where reuse children are mapped to the existing accepted node ids.
- The printed proof of 4.5, steps (1)-(2), and Remark 4.6 (book/chapter-05.txt:776-830) match the parent proof and the split.

Lean evidence (/tmp/stp-decomp/checks):
- All child types and the parent type elaborate.
- The parent is proved from the child stubs plus tdo_scaledLpNorm_bounds.
- The three new children are fully proved, each with only its declared dependency in scope; #print axioms lists only propext, Classical.choice and Quot.sound.
- Comparator-style exact-type checks pass for all five declarations.
- An independent reviewer agent re-ran these checks and returned ACCEPT.
