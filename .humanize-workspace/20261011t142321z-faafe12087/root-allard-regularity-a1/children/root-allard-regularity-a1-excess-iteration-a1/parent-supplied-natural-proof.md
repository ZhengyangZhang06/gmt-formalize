# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_regularity-a1`
- Child DAG node: `root.allard_regularity-a1.excess_iteration-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Part I of the parent proof (Simon Ch. 5, proof of 5.2, steps (1)-(7), and Remark 4.6), with the parameter delta of 2.3 in place of the parent's delta_1.

Notation. mu := V.weight, p_x := V.tangentProj x, p_S := S.starProjection, |.| the Hilbert-Schmidt norm (hsNorm), omega_n := unitBallVolume n, alpha' := 1 - n/p in (0,1); E(xi, s, T) := V.tiltExcess xi s T = s^-n integral_{B_s(xi)} |p_x - p_T|^2 dmu; E_*(xi, s, T) := V.tiltExcessStar H p delta xi s T = max{E(xi,s,T), delta^-1 K(xi,s)^2}, K := V.scaledLpNorm H p (as a real number via toReal).
Hypotheses and facts used. (D) TiltExcessDecayTheorem (hypothesis of this theorem): for n, l, p there are eta, delta_45 in (0, 1/4] such that, if 2.3 holds with delta in (0, delta_45], sigma in (0, delta rho/2], xi in spt V cap B_{delta rho}(0) and dim T = n, then E_*(xi, eta sigma, S) <= eta^(2 alpha') E_*(xi, sigma, T) for some n-dimensional S. (P) [sibling allard52_density_bounds, applied to the given n, p and then to the given l] there are delta_P in (0, 1/8], C_P > 0 with C_P delta_P <= 1/2 (depending only on n and p) such that under 2.3 with delta <= delta_P, |y| <= 3 delta rho and 0 < s <= rho/2: mu(B_s(y)) <= (1 + C_P delta) omega_n s^n <= 2 omega_n s^n, and if y in spt V also mu(B_s(y)) >= (1 - C_P delta) omega_n s^n >= omega_n s^n / 2. (T) [sibling allard52_tangent_ae] p is mu-a.e. strongly measurable, and for mu-a.e. x, p_x is the orthogonal projection onto an n-dimensional subspace; by the definition of V.tangentProj, p_x is in any case either 0 or such a projection.
Constants. delta_1 := min{delta_45, delta_P} > 0, C_II := (8/omega_n) eta^-n (1 - eta^(alpha'))^-2, C_III := (2 eta^-n + 4 omega_n C_II) eta^(-2 alpha'), C := max{C_II, C_III} >= 0; all depend only on n, l, p.

Let 0 < delta <= delta_1, assume 2.3 (AllardHypotheses H p delta rho), xi in spt V cap B_{delta rho}(0), sigma in (0, delta rho/2], and S_0 n-dimensional. Put E_*^(0) := E_*(xi, sigma, S_0).

1. Integrability. For every B_s(z) contained in B_rho(0) (in particular B_s(xi) with s <= sigma, since |xi| + s <= delta rho + delta rho/2 < rho) and every n-dimensional T, the function x -> |p_x - p_T|^2 is bounded by 4n (p_x is 0 or a rank-n orthogonal projection, |p_T|^2 = n), mu-a.e. strongly measurable by (T), and mu(B_s(z)) < infinity (B_s(z) is a compact subset of U). So it is mu-integrable on B_s(z); E(z, s, T) is a genuine integral, E <= E_*, and s'^n E(z, s', T) <= s^n E(z, s, T) for s' <= s (integral of a nonnegative integrable function over a smaller set).

2. Iteration of 4.5 (book (1)). Define S_j recursively: given S_{j-1} (dim n), apply (D) with sigma_j := eta^(j-1) sigma (in (0, delta rho/2]) and T := S_{j-1} to obtain S_j (dim n) with E_*(xi, eta^j sigma, S_j) <= eta^(2 alpha') E_*(xi, eta^(j-1) sigma, S_{j-1}). By induction E_*(xi, eta^j sigma, S_j) <= eta^(2 alpha' j) E_*^(0) for all j >= 0.

3. Consecutive planes (book (3), Remark 4.6). Let j >= 1 and B := B_{eta^j sigma}(xi). Since xi in spt V, |xi| <= delta rho <= 3 delta rho and eta^j sigma <= rho/2, (P) gives mu(B) >= omega_n (eta^j sigma)^n / 2. Integrating |p_{S_j} - p_{S_{j-1}}|^2 <= 2|p_x - p_{S_j}|^2 + 2|p_x - p_{S_{j-1}}|^2 over B and using step 1,
 mu(B) |p_{S_j} - p_{S_{j-1}}|^2 <= 2 (eta^j sigma)^n E(xi, eta^j sigma, S_j) + 2 (eta^(j-1) sigma)^n E(xi, eta^(j-1) sigma, S_{j-1}),
 hence, by step 2 and E <= E_*, |p_{S_j} - p_{S_{j-1}}|^2 <= (4/omega_n)[eta^(2 alpha' j) + eta^-n eta^(2 alpha'(j-1))] E_*^(0) <= (8/omega_n) eta^-n eta^(2 alpha'(j-1)) E_*^(0).

4. Limit plane (book (4)-(6)). By step 3, |p_{S_j} - p_{S_{j-1}}| <= a eta^(alpha'(j-1)) with a := ((8/omega_n) eta^-n E_*^(0))^(1/2). Hence (p_{S_j}) is a Cauchy sequence in the finite-dimensional space of operators and converges to some P_infinity, with |P_infinity - p_{S_k}| <= sum_{j>k} a eta^(alpha'(j-1)) = a eta^(alpha' k)/(1 - eta^(alpha')), i.e.
 (5) |P_infinity - p_{S_k}|^2 <= C_II eta^(2 alpha' k) E_*^(0) for k >= 0.
 The set of orthogonal projections of rank n, {P : P^2 = P, P^* = P, trace P = n}, is closed, so P_infinity = p_S for the n-dimensional subspace S := range P_infinity. With k = 0: hsNormSq(p_S - p_{S_0}) <= C_II E_*^(0) <= C E_*^(0).

5. Decay at all scales (book (7)). Let 0 < s <= sigma and choose j >= 0 with eta^(j+1) sigma < s <= eta^j sigma. Integrating |p_x - p_S|^2 <= 2|p_x - p_{S_j}|^2 + 2|p_{S_j} - p_S|^2 over B_s(xi) contained in B_{eta^j sigma}(xi), and using step 1, (P) (mu(B_s(xi)) <= 2 omega_n s^n), step 2 and (5):
 E(xi, s, S) <= 2 s^-n (eta^j sigma)^n E(xi, eta^j sigma, S_j) + 2 s^-n mu(B_s(xi)) |p_{S_j} - p_S|^2 <= 2 eta^-n eta^(2 alpha' j) E_*^(0) + 4 omega_n C_II eta^(2 alpha' j) E_*^(0),
 because eta^j sigma / s < eta^-1. Since eta^(j+1) < s/sigma, eta^(2 alpha' j) = eta^(-2 alpha') (eta^(j+1))^(2 alpha') <= eta^(-2 alpha') (s/sigma)^(2 alpha'). Hence E(xi, s, S) <= C_III (s/sigma)^(2 alpha') E_*^(0) <= C (s/sigma)^(2(1 - n/p)) E_*^(0).

Steps 4 and 5 give an n-dimensional S with hsNormSq(S.starProjection - S_0.starProjection) <= C E_*(xi, sigma, S_0) and V.tiltExcess xi s S <= C (s/sigma)^(2(1-n/p)) E_*(xi, sigma, S_0) for all 0 < s <= sigma, with delta_1 > 0 and C >= 0 depending only on n, l, p.

## Key steps

1. Tilt integrands are bounded and a.e. measurable, so tilt-excess is a genuine integral
2. Iterate 4.5 at radii eta^j sigma: E_*(xi, eta^j sigma, S_j) <= eta^(2 alpha' j) E_*^(0)
3. Density lower bound gives |p_{S_j} - p_{S_{j-1}}|^2 <= (8/omega_n) eta^-n eta^(2 alpha'(j-1)) E_*^(0)
4. Geometric series: p_{S_j} -> p_S with |p_S - p_{S_k}|^2 <= C_II eta^(2 alpha' k) E_*^(0)
5. Interpolate scales with the density upper bound: E(xi, s, S) <= C_III (s/sigma)^(2 alpha') E_*^(0)

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
