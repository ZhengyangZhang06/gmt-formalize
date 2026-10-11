# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_regularity-a1`
- Child DAG node: `root.allard_regularity-a1.radial_height-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the radial-integration argument in step 6 of the parent proof (Part III, not in the printed text), isolated as a statement about functions on R^n.

Notation. a := 1/(2n+2); S := S^(n-1), the unit sphere of R^n; |.| Euclidean norms, ||.|| the operator norm, hsNorm the Hilbert-Schmidt norm (||B|| <= hsNorm B).
Facts used. (Pol) Polar coordinates (Mathlib MeasureTheory.Measure.toSphere and measurePreserving_homeomorphUnitSphereProd): there is a finite Borel measure sigma on S such that integral_{R^n} g dL^n = integral_S integral_0^infinity g(t w) t^(n-1) dt dsigma(w) for every Borel g >= 0, and sigma(A) = n L^n({t w : 0 < t < 1, w in A}). For n = 1, S = {-1, 1} and sigma is counting measure. (Cap) For n >= 2 there is c_n > 0 with sigma(S cap B_tau(w_0)) >= c_n tau^(n-1) for w_0 in S and 0 < tau <= 1: with w_0 = e_1, the box Q := {x : x_1 in [1/2, 3/4], |(x_2,...,x_n)| <= tau/4} lies in {t w : 1/2 <= t <= 1, w in S cap B_tau(w_0)} (for x in Q, 1/2 <= |x| <= 1 and |x/|x| - e_1| <= 2|(x_2,...,x_n)|/|x| <= tau), so L^n(Q) = (1/4) omega_{n-1} (tau/4)^(n-1) <= sigma(S cap B_tau(w_0)) integral_{1/2}^1 t^(n-1) dt <= sigma(S cap B_tau(w_0))/n.
Constants. Given n >= 1, alpha in (0,1], M >= 0, A >= 0: put c_1 := 1, K_n := (4^n A/(c_n alpha))^(1/(n+1)) and C := M + K_n >= 0.

Let f, R, delta satisfy the hypotheses: 0 < R, 0 < delta <= 1, f(0) = 0, f in C^1 on B^o_R(0), f 1-Lipschitz on B^o_R(0), hsNorm(Df(x)) <= M (|x|/R)^alpha on B^o_R(0), and integral_{B^o_R(0)} |f(x) - Df(x)x|^2 |x|^(-n-2) dx <= A delta.

1. Basic bounds. |f(x)| = |f(x) - f(0)| <= |x| on B^o_R(0), and ||Df(x)|| <= hsNorm(Df(x)) <= M (|x|/R)^alpha.

2. Radial quotient. For w in S and 0 < t < R put W(t, w) := f(t w)/t. W is C^1 in t with d/dt W(t, w) = (Df(t w)(t w) - f(t w))/t^2, hence t |d/dt W(t, w)|^2 = |f(t w) - Df(t w)(t w)|^2 t^-3 = g(t w) t^(n-1) with g(x) := |f(x) - Df(x)x|^2 |x|^(-n-2) (a nonnegative Borel function on B^o_R(0) minus {0}). By (Pol),
 integral_S integral_0^R t |d/dt W(t, w)|^2 dt dsigma(w) = integral_{B^o_R(0)} g dL^n <= A delta.

3. Small radii. Put r_1 := delta^(1/alpha) R in (0, R]. For 0 < t <= r_1 and w in S, the mean value inequality on the segment [0, t w] and step 1 give |W(t, w)| = |f(t w) - f(0)|/t <= sup_{|x| <= t} ||Df(x)|| <= M (t/R)^alpha <= M (r_1/R)^alpha = M delta.

4. L^2 bound on the sphere. For r_1 <= r < R and w in S let D_r(w) := W(r, w) - W(r_1, w) = integral_{r_1}^r d/dt W(t, w) dt. By Cauchy-Schwarz, |D_r(w)|^2 <= (integral_{r_1}^r dt/t)(integral_{r_1}^r t |d/dt W|^2 dt) <= log(R/r_1) integral_0^R t |d/dt W(t, w)|^2 dt. Integrating over S (Tonelli) and using step 2 and log(R/r_1) = alpha^-1 log(1/delta):
 integral_S |D_r|^2 dsigma <= (A/alpha) delta log(1/delta).

5. From L^2 to sup. Since f is 1-Lipschitz, |W(t, w) - W(t, w')| = |f(t w) - f(t w')|/t <= |w - w'|, so D_r is 2-Lipschitz on S; and |W| <= 1 by step 1, so |D_r| <= 2. Let w_0 in S and m := |D_r(w_0)| (<= 2).
 If n >= 2: for w in S cap B_{m/4}(w_0), |D_r(w)| >= m - 2(m/4) = m/2, and m/4 <= 1/2, so by (Cap) integral_S |D_r|^2 dsigma >= (m/2)^2 c_n (m/4)^(n-1) = c_n 4^-n m^(n+1).
 If n = 1: S = {-1, 1} with counting measure, so integral_S |D_r|^2 dsigma >= |D_r(w_0)|^2 = m^2 = m^(n+1) >= c_1 4^-n m^(n+1).
 In both cases, by step 4, m <= (4^n (A/alpha) delta log(1/delta)/c_n)^(1/(n+1)) = K_n (delta log(1/delta))^(1/(n+1)).

6. Removing the logarithm. (delta log(1/delta))^(1/(n+1)) = delta^(2a) (log(1/delta))^(2a) = delta^a (delta^(1/2) log(1/delta))^(2a) <= delta^a, because sup_{0 < delta <= 1} delta^(1/2) log(1/delta) = 2/e < 1. Also delta <= delta^a since 0 < delta <= 1 and a < 1.

7. Conclusion. Let x in B^o_R(0). If x = 0 then |f(x)| = 0. Otherwise write x = r w with r = |x| in (0, R), w in S. If r <= r_1, step 3 gives |f(x)| = r |W(r, w)| <= M delta r <= M delta^a |x|. If r_1 < r < R, steps 3, 5 and 6 give |f(x)| = r |W(r, w)| <= r (|W(r_1, w)| + |D_r(w)|) <= r (M delta + K_n delta^a) <= (M + K_n) delta^a |x|. Hence ||f x|| <= C delta^(1/(2n+2)) ||x|| for every x in ball 0 R, with C = M + K_n depending only on n, alpha, M, A.

## Key steps

1. Polar coordinates turn the weighted integral into integral_S integral_0^R t |d/dt (f(tw)/t)|^2 dt dsigma
2. Small radii r <= r_1 = delta^(1/alpha) R: |f(tw)|/t <= M delta
3. Cauchy-Schwarz in t bounds the sphere L^2 norm of the increment by (A/alpha) delta log(1/delta)
4. Lipschitz continuity on the sphere converts the L^2 bound into a sup bound via spherical caps
5. (delta log(1/delta))^(1/(n+1)) <= delta^(1/(2n+2))

## Reference use

### local-project

Queries:
- `diff GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Contract.lean; diff GMT/Ch05/Submission.lean <snapshot>/project/GMT/Ch05/Submission.lean`
- `rg -l 'allard52_' <snapshot>`
- `rg -l 'allard52_' .humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087 --include=*.json`
- `python: list dag.json nodes with lean_name and lean_statement (name-reservation check)`
- `rg -n 'theorem measurePreserving_homeomorphUnitSphereProd|def toSphere|theorem LipschitzWith.ae_differentiableAt|theorem measurable_fderiv\b|theorem Submodule.range_starProjection|theorem LipschitzOnWith.extend_pi|theorem ae_tendsto_average_norm_sub|theorem norm_fderiv_le_of_lipschitzOn|theorem LocallyIntegrableOn.integrableOn_isCompact|theorem lintegral_image_eq_lintegral_abs_det_fderiv_mul|theorem uniqueDiffOn_convex|theorem aestronglyMeasurable_of_tendsto_ae' <snapshot>/mathlib/Mathlib`
- `rg -n 'range_starProjection|theorem aestronglyMeasurable_of_tendsto_ae|theorem LocallyIntegrableOn.integrableOn_compact_subset' <snapshot>/mathlib/Mathlib`
- `for pat in Campanato 'radial.*height' Allard monotonicity_formula upperDensity; do rg -l $pat <snapshot>/mathlib/Mathlib | wc -l; done`
- `rg -n '5.2|Allard|AllardRegularityTheorem|1/\(2n\+2\)|rate|gamma|γ' <snapshot>/project/GMT/Ch05/README.md`
- `grep -n 'def HasWeightedApproximateTangentSpaceAt|def CountablyRectifiable|def HasApproximateTangentSpaceAt|theorem HasWeightedApproximateTangentSpaceAt.unique' -A 25 .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -rn 'theorem mul_simonHausdorff_le_of_le_dimensionalUpperDensity|theorem simon_theorem_3_6\b|theorem injective_area_formula_lipschitz_simon|theorem weighted_area_formula_lipschitz_injOn|def simonHausdorff|structure LpAnnularCorrection|def lpMeanCurvatureKappa' -A 22 .lake/packages/simongmt/Poincare/SimonGMT`
- `grep -n 'theorem one_le_stationaryDensityReal_of_mem_support_lp|theorem simon_remark_1_3|theorem exists_contDiff_one_extension_of_whitney' .lake/packages/simongmt/Poincare/SimonGMT/{Chapter04/LpLowerDensity,Chapter03/DisjointCover,Chapter02/WhitneyExtension}.lean`
- `lean GMT/Ch05/Submission.lean -o /tmp/allard-decomp-v2/build/lib/lean/GMT/Ch05/Submission.olean (toolchains/lean-4.35.0-rc3-linux, LEAN_PATH from `lake env printenv LEAN_PATH`)`
- `LEAN_PATH=/tmp/allard-decomp-v2/build/lib/lean:<lake LEAN_PATH> lean /tmp/allard-decomp-v2/check/Types.lean (import GMT.Ch05.Submission; theorem Submission.<lean_name> : <lean_statement> := by sorry for all 8 children; #synth/#check instance probes)`
- `lean /tmp/allard-decomp-v2/check/Axioms.lean (#print axioms for the cited SimonGMT and Mathlib lemmas)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/TangentCone/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpMeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpAnnular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpLowerDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1/decomposition-review-receipt-v1.json`
- `/tmp/allard-decomp-v2/check/Types.lean`
- `/tmp/allard-decomp-v2/check/Axioms.lean`

Snapshot pins: project ea5607598f3133b40a13241f2e51517a8c6423cd, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json). The workspace GMT/Ch05/Contract.lean and Submission.lean are byte-identical to the snapshot copies.

Names.
- `allard52_` has no match in the snapshot.
- In the run directory it occurs only in this node's rejected v1 decomposition, audit and receipt files.
- dag.json reserves other names, none of which collide: the 12 root conjunct names, plus rectifiableVarifold_ae_tangentProj_starProjection, divM_height_test_field_eq, hsNorm_starProjection_trace_identities and exists_smooth_cutoff_half_ball_grad_le in the tilt_excess_height_estimate branch.
- The eight bare names are therefore globally unique.

Mathlib. These searches return 0 files each: Campanato, radial.*height, Allard, monotonicity_formula, upperDensity. All eight children are therefore new. Usable lemmas found:
- toSphere (HaarToSphere.lean:51) and measurePreserving_homeomorphUnitSphereProd (HaarToSphere.lean:142);
- LipschitzWith.ae_differentiableAt (Rademacher.lean:385);
- measurable_fderiv (FDeriv/Measurable.lean:378);
- ae_tendsto_average_norm_sub (DensityTheorem.lean:150; Differentiation.lean:837);
- Submodule.range_starProjection (Projection/Basic.lean:302);
- LipschitzOnWith.extend_pi (Lipschitz.lean:344);
- norm_fderiv_le_of_lipschitzOn (FDeriv/Basic.lean:939);
- LocallyIntegrableOn.integrableOn_isCompact and integrableOn_compact_subset (LocallyIntegrable.lean:117,122);
- uniqueDiffOn_convex (TangentCone/Real.lean:79);
- lintegral_image_eq_lintegral_abs_det_fderiv_mul (Jacobian.lean:1183).

SimonGMT (pinned package, outside the snapshot).
- HasWeightedApproximateTangentSpaceAt (Chapter03/Rectifiable.lean:330) includes finrank P = n. It is a Bochner-integral limit over the blow-up weighted by θ(x + r•y). So V.tangentProj is everywhere 0 or a rank-n orthogonal projection, as the children use.
- HasWeightedApproximateTangentSpaceAt.unique (Rectifiable.lean:345) needs θ x ≠ 0.
- lpMeanCurvatureKappa = (p−n)/(4p) (Chapter04/LpMeanCurvature.lean:76) and LpAnnularCorrection (Chapter04/LpAnnular.lean:335) confirm the corrected monotonicity constants used in density_bounds. These are proved for SimonGMT's own varifold, so density_bounds re-derives them for the contract's RectifiableVarifold.
- mul_simonHausdorff_le_of_le_dimensionalUpperDensity and simon_theorem_3_6 (Chapter01/DensityComparison.lean:251,332) and injective_area_formula_lipschitz_simon (Chapter02/AreaLipschitz.lean:126) match their citations.

README (Ch05, lines 149-151) records that the δ-rate at a fixed γ needs an argument beyond the printed proof. This is Part III, isolated in radial_height.

Lean checks.
- Submission.lean compiled to a temporary olean; Types.lean (import GMT.Ch05.Submission) elaborated all eight lean_statement strings with only sorry warnings. Only density_bounds and graph_comparison changed type relative to v1: ∀ ℓ now comes after the existential constants.
- Instance probes: Prod.instMeasurableSpace, ContinuousLinearMap.instBorelSpace, Monoid.npow for ‖x‖^(n+2), and Submodule.starProjection on mapped graph planes.
- #print axioms gives only [propext, Classical.choice, Quot.sound] for: HasWeightedApproximateTangentSpaceAt.unique, simon_remark_1_3, injective_area_formula_lipschitz_simon, weighted_area_formula_lipschitz_injOn, simon_theorem_3_6, mul_simonHausdorff_le_of_le_dimensionalUpperDensity, exists_lpAnnularCorrection, one_le_stationaryDensityReal_of_mem_support_lp, measurePreserving_homeomorphUnitSphereProd, LipschitzWith.ae_differentiableAt, measurable_fderiv, ae_tendsto_average_norm_sub, LipschitzOnWith.extend_pi and Submodule.range_starProjection.
- Chapter02/WhitneyExtension has no built olean in the shared package cache, so its axioms were not printed. Its source contains no sorry, and it is cited only as a reference inside tangent_ae's proof.
