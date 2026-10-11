# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_regularity-a1`
- Child DAG node: `root.allard_regularity-a1.graph_plane_algebra-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the facts (Gp) and (Nor) of the parent proof (Simon Ch. 5, proof of 5.2, the estimate before (11)), together with three elementary facts the parent proof uses implicitly (the norm comparison ||A|| <= |A| <= sqrt(n) ||A||, the existence of a linear isometry q with rotatedPlane q = T, and continuity of the graph projection).

Notation. For a linear map A : R^n -> R^l let J_A : R^n -> R^(n+l), J_A v := graphPoint v (A v); J_A is linear and injective, J_A^* J_A = I + A^* A (invertible), and Gamma_A := range J_A = span{graphPoint v (A v)} is n-dimensional. Pi(A) := orthogonal projection onto Gamma_A = J_A (I + A^* A)^-1 J_A^*; in block form with respect to R^n x R^l,
 Pi(A) = [[(I + A^*A)^-1, (I + A^*A)^-1 A^*], [A (I + A^*A)^-1, A (I + A^*A)^-1 A^*]].
For a linear isometry q of R^(n+l), the subspace (span{graphPoint v (A v)}).map q is q(Gamma_A) and its orthogonal projection (starProjection) is P_q(A) = q Pi(A) q^-1. |X| denotes the Hilbert-Schmidt norm (hsNorm; |X|^2 = hsNormSq X = trace(X^* X), independent of the orthonormal basis), ||X|| the operator norm. Conjugation by a linear isometry preserves |.|.

1. Continuity (last conjunct). A -> I + A^*A is continuous with values in the invertible operators, inversion is continuous there, and composition/adjoint are continuous; hence A -> Pi(A) and A -> P_q(A) = q Pi(A) q^-1 are continuous (in fact real analytic) on the space of linear maps R^n -> R^l.

2. Derivative at 0. Differentiating Pi(tH) = J_{tH}(I + t^2 H^*H)^-1 J_{tH}^* at t = 0 gives DPi(0)[H] = [[0, H^*], [H, 0]], so |DPi(0)[H]|^2 = |H^*|^2 + |H|^2 = 2|H|^2.

3. (Gp) (first conjunct). Pi is C^infinity, so C_g := 1 + sup_{|X| <= 1} ||D^2 Pi(X)|| < infinity (norms built from |.|; compactness of the unit ball of the finite-dimensional space of linear maps), and ||DPi(X) - DPi(0)|| <= C_g |X| for |X| <= 1. Put L_0 := min{1/4, (sqrt 3 - sqrt 2)/C_g}; it depends only on n, l, and 0 < L_0 <= 1/4. If |A|, |B| <= L_0, the segment from B to A lies in {|X| <= L_0}, so by the mean value inequality |Pi(A) - Pi(B) - DPi(0)[A - B]| <= C_g L_0 |A - B|. With step 2,
 (sqrt 2 - C_g L_0)|A - B| <= |Pi(A) - Pi(B)| <= (sqrt 2 + C_g L_0)|A - B|.
 Since C_g L_0 <= sqrt 3 - sqrt 2, we have sqrt 2 - C_g L_0 >= 2 sqrt 2 - sqrt 3 > 1 and sqrt 2 + C_g L_0 <= sqrt 3, so |A - B|^2 <= |Pi(A) - Pi(B)|^2 <= 3 |A - B|^2. As |P_q(A) - P_q(B)| = |q (Pi(A) - Pi(B)) q^-1| = |Pi(A) - Pi(B)|, this is the first conjunct: hsNormSq(A - B) <= hsNormSq(P_q(A) - P_q(B)) <= 3 hsNormSq(A - B).

4. The case B = 0 (second conjunct). graphPoint v 0 = sum_{i<n} v_i e_{castAdd i}, so Gamma_0 = span{e_{castAdd i} : i < n} = horizontalPlane n l and q(Gamma_0) = rotatedPlane q. Applying step 3 with B = 0 (|0| = 0 <= L_0) gives hsNormSq A <= hsNormSq(P_q(A) - (rotatedPlane q).starProjection) whenever |A| <= L_0.

5. (Nor) (third conjunct). Let x in R^n, y in R^l, w := q(graphPoint x y). Then |w - P_q(A)w| = dist(w, q(Gamma_A)) = dist(graphPoint x y, Gamma_A) = inf_v |graphPoint (x - v) (y - A v)|. For every v, |y - A x| <= |y - A v| + |A(v - x)| <= |y - A v| + ||A|| |x - v| <= (1 + ||A||^2)^(1/2) (|y - Av|^2 + |x - v|^2)^(1/2) (Cauchy-Schwarz) = (1 + ||A||^2)^(1/2) |graphPoint (x - v) (y - Av)|. Taking the infimum, |y - A x| <= (1 + ||A||^2)^(1/2) |w - P_q(A) w| <= sqrt 2 |w - P_q(A) w| <= 2 |w - P_q(A) w| when ||A|| <= 1.

6. Norm comparison (fourth conjunct). For a unit vector u = sum u_i e_i, |A u| <= sum |u_i| |A e_i| <= (sum u_i^2)^(1/2)(sum |A e_i|^2)^(1/2) = |A|, so ||A|| <= |A| = hsNorm A; and hsNormSq A = sum_{i<n} |A e_i|^2 <= n ||A||^2, so hsNorm A <= sqrt(n) ||A||.

7. Rotations (fifth conjunct). Let T be a subspace with dim T = n. Choose an orthonormal basis u_0, ..., u_{n-1} of T and an orthonormal basis u_n, ..., u_{n+l-1} of T^perp (dim T^perp = l). The linear map q with q(e_{castAdd i}) = u_i (i < n) and q(e_{natAdd n j}) = u_{n+j} (j < l) sends an orthonormal basis to an orthonormal basis, hence is a linear isometry equivalence of R^(n+l), and rotatedPlane q = q(span{e_{castAdd i}}) = span{u_0, ..., u_{n-1}} = T.

Steps 1-7 prove all six conjuncts, with L_0 = L_0(n, l) in (0, 1/4].

## Key steps

1. Write P_q(A) = q Pi(A) q^-1 with Pi(A) = J_A (I + A^*A)^-1 J_A^*, continuous and smooth
2. DPi(0)[H] = [[0, H^*],[H, 0]] has Hilbert-Schmidt norm sqrt(2)|H|
3. Mean value inequality with C_g L_0 <= sqrt 3 - sqrt 2 gives the two-sided comparison
4. graph 0 is the horizontal plane, so B = 0 gives the comparison with rotatedPlane q
5. Distance to graph A bounds |y - Ax| by Cauchy-Schwarz
6. Norm comparison and rotations from orthonormal bases

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
