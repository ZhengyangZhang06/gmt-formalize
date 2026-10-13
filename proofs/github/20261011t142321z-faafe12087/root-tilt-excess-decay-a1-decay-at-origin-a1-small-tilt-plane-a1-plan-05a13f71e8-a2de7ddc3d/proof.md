# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1.decay_at_origin-a1.small_tilt_plane-a1`
- Child DAG node: `root.tilt_excess_decay-a1.decay_at_origin-a1.small_tilt_plane-a1.plane_tilt_comparison-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Provenance (not needed for the argument): extracted from the parent node's proof, where it is used with z = 0, s = delta rho, P = T and Q = T~ (the plane from affine approximation); here it is stated for an arbitrary centre z, radius s and subspaces P, Q. The argument below is self-contained.

Notation. B := B_s(z) (closed ball); mu := V.weight; p_x := V.tangentProj x; for a subspace R of R^{n+l}, p_R := R.starProjection and phi_R(x) := hsNormSq(p_x - p_R); w := mu(B).toReal; N := n + l. By hypothesis mu(B) is finite. We use the sibling lemma hs_norm_bounds (lgc_hsNormSq_bounds) with m = k = N: the map A |-> hsNormSq A is continuous, and 0 <= hsNormSq A <= N ||A||^2 for every continuous linear A : R^N -> R^N.

1. Operator norms of the projections. For every x, ||p_x|| <= 1: by definition V.tangentProj x is either the orthogonal projection (Classical.choose h).starProjection onto some subspace, whose operator norm is <= 1 (Submodule.starProjection_norm_le), or the zero map, of norm 0 <= 1. Likewise ||p_R|| <= 1 for every subspace R.
2. Integrability. Fix a subspace R. (a) The map x |-> p_x - p_R is mu-a.e. strongly measurable (the difference of the mu-a.e. strongly measurable map x |-> p_x, a hypothesis, and a constant), and hsNormSq is continuous, so phi_R = hsNormSq o (x |-> p_x - p_R) is mu-a.e. strongly measurable. (b) For every x, |phi_R(x)| = phi_R(x) <= N ||p_x - p_R||^2 <= N (||p_x|| + ||p_R||)^2 <= N * 2^2 = 4N, by nonnegativity, the bound of hs_norm_bounds, the triangle inequality and step 1. (c) A mu-a.e. strongly measurable real function that is bounded by a constant on a set of finite mu-measure is integrable on that set (Measure.integrableOn_of_bounded with mu(B) != oo). Hence phi_R is mu-integrable on B, in particular for R = P and R = Q.
3. Pointwise inequality. Fix x. For each standard basis vector e_i of R^N put a := (p_x - p_Q) e_i and b := (p_x - p_P) e_i. Then (p_P - p_Q) e_i = p_P e_i - p_Q e_i = a - b. By the triangle inequality and 2 ||a|| ||b|| <= ||a||^2 + ||b||^2, ||a - b||^2 <= (||a|| + ||b||)^2 <= 2 ||a||^2 + 2 ||b||^2. Summing over i = 1, ..., N (definition hsNormSq A = sum_i ||A e_i||^2) gives hsNormSq(p_P - p_Q) <= 2 hsNormSq(p_x - p_P) + 2 hsNormSq(p_x - p_Q) = 2 phi_P(x) + 2 phi_Q(x).
4. Integration. The constant function c := hsNormSq(p_P - p_Q) is integrable on B (B has finite measure), and its integral over B is mu(B).toReal * c = w c (setIntegral_const; mu.real B = mu(B).toReal). The function 2 phi_P + 2 phi_Q is integrable on B by step 2. By step 3 and monotonicity of the integral, w c <= integral over B of (2 phi_P + 2 phi_Q) dmu = 2 * integral_B phi_P dmu + 2 * integral_B phi_Q dmu (linearity of the integral for integrable functions).
5. Rewriting with the tilt-excess. Since s > 0, s^n != 0, and by the definition E(z, s, R) = (s^n)^{-1} * integral_B phi_R dmu we get s^n E(z, s, R) = integral_B phi_R dmu for R = P, Q. Therefore 2 integral_B phi_P dmu + 2 integral_B phi_Q dmu = 2 s^n E(z, s, P) + 2 s^n E(z, s, Q) = 2 s^n (E(z, s, P) + E(z, s, Q)).
6. Steps 4 and 5 give mu(B_s(z)).toReal * hsNormSq(p_P - p_Q) <= 2 s^n (E(z, s, P) + E(z, s, Q)). QED

Lean notes (names that worked under the pinned toolchain; a complete proof of the frozen type was compiled in this decomposition session): obtain ⟨hcont, hbd⟩ := lgc_hsNormSq_bounds (n + ℓ) (n + ℓ); step 1: unfold RectifiableVarifold.tangentProj; split_ifs; Submodule.starProjection_norm_le / simp; step 2: Measure.integrableOn_of_bounded (M := ((n + ℓ : ℕ) : ℝ) * 2 ^ 2) hfin with hcont.comp_aestronglyMeasurable (hmeas.sub aestronglyMeasurable_const) and Filter.Eventually.of_forall, Real.norm_eq_abs, abs_of_nonneg, norm_sub_le, gcongr; step 3: unfold hsNormSq; rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]; Finset.sum_le_sum; simp only [FunLike.coe_sub, Pi.sub_apply]; abel for a - b; nlinarith [norm_sub_le a b, sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b, norm_nonneg (a - b)]; step 4: setIntegral_const, smul_eq_mul, Measure.real_def; setIntegral_mono (integrableOn_const hfin) (((hint P).const_mul 2).add ((hint Q).const_mul 2)); integral_add, integral_const_mul; step 5: unfold RectifiableVarifold.tiltExcess; field_simp.

## Key steps

1. ||V.tangentProj x|| <= 1 and ||p_R|| <= 1 (orthogonal projections or 0)
2. phi_R(x) = hsNormSq(p_x - p_R) is a.e. strongly measurable and bounded by 4(n+l), hence integrable on the finite-measure ball
3. pointwise hsNormSq(p_P - p_Q) <= 2 phi_P(x) + 2 phi_Q(x), columnwise from ||a - b||^2 <= 2||a||^2 + 2||b||^2
4. integrate over B_s(z): mu(B).toReal hsNormSq(p_P - p_Q) <= 2 int phi_P + 2 int phi_Q = 2 s^n (E(z,s,P) + E(z,s,Q))

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
