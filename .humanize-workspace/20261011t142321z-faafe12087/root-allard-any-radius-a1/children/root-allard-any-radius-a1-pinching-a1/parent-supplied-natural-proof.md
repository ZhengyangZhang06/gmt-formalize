# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_any_radius-a1`
- Child DAG node: `root.allard_any_radius-a1.pinching-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1 ((1a), (1b)) and 2 of the parent proof. Notation: mu := V.weight, B_t(x) closed balls, omega_n := unitBallVolume n, kappa := (p-n)/(4p), Lambda := delta/kappa, gamma_b := (1+gamma)/2, theta_0 := (1 - gamma_b)/4 = (1-gamma)/8 in (0, 1/8], kappa_0 := min{1/4, eps/(8n)}, and cs := kappa_0 theta_0/2, so 0 < cs <= (1-gamma)/64 <= (1-gamma)/16 as required. Let C_9 be the constant that ConicalApproximationTheorem gives for (n, l) and Lambda~ := 2 omega_n, and C_9' := max{C_9, 0}; the first conclusion of 6.1 with C_9 implies the same with C_9' since the added term is >= 0. Throughout, V, H, delta, rho satisfy 2.3 with 0 < delta <= delta_P, where delta_P is fixed in step 5; in particular delta <= kappa, so Lambda <= 1 and the child monotonicity_bounds ((M1), (M2)) applies. All masses below are of balls inside B_rho(0), hence finite.

1. Centre 0. Let C_1 := max{1 + (4e^2 + 2e/omega_n + 1 + 1/omega_n)/kappa, (2 omega_n)^(1 - 1/p)}.
 (1a) For 0 < t <= rho: 1 - C_1 delta <= omega_n^-1 t^-n mu(B_t(0)) <= 1 + C_1 delta. Upper bound for t < rho: (M1) with y = 0, R = rho and t <= r < rho gives t^-n mu(B_t(0)) <= e^(2 Lambda) r^-n mu(B_r(0)) + 2 e^Lambda Lambda <= e^(2 Lambda) r^-n (1+delta) omega_n rho^n + 2 e^Lambda Lambda; letting r -> rho, omega_n^-1 t^-n mu(B_t(0)) <= e^(2 Lambda)(1+delta) + 2 e^Lambda Lambda/omega_n <= (1 + 2e^2 Lambda)(1 + delta) + 2e Lambda/omega_n <= 1 + C_1 delta (e^(2 Lambda) <= 1 + 2 Lambda e^(2 Lambda) <= 1 + 2e^2 Lambda and delta <= 1); for t = rho use 2.3. Lower bound for t < rho: (M2) with y = 0 (in spt V), R = rho, s = t gives omega_n^-1 t^-n mu(B_t(0)) >= e^-Lambda (1 - Lambda/omega_n) >= (1 - Lambda)(1 - Lambda/omega_n) >= 1 - Lambda - Lambda/omega_n >= 1 - C_1 delta (here 1 - Lambda/omega_n > 0 because Lambda/omega_n = delta/(kappa omega_n) < C_1 delta <= 1, and e^-Lambda >= 1 - Lambda; the last step uses Lambda (1 + 1/omega_n) = delta (1 + 1/omega_n)/kappa <= C_1 delta); for t = rho use mu(B_rho(0)) >= mu(B_t(0)) and let t -> rho.
 (1b) For 0 < t <= rho: t^(1-n) integral over B_t(0) of |H| d mu <= C_1 delta. By Hoelder, integral over B_t(0) of |H| <= (integral over B_t(0) of |H|^p)^(1/p) mu(B_t(0))^(1-1/p) <= delta rho^(n/p - 1) (2 omega_n t^n)^(1-1/p), using rho^(p-n) integral over B_rho(0) of |H|^p <= delta^p (2.3) and mu(B_t(0)) <= (1 + C_1 delta) omega_n t^n <= 2 omega_n t^n (C_1 delta <= 1). So t^(1-n) integral <= (2 omega_n)^(1-1/p) delta (t/rho)^(1-n/p) <= C_1 delta.

2. Fix y in spt V cap B_{gamma_b rho}(0). Case (a): |y| <= kappa_0 rho. Put R := (1 - kappa_0) rho; then B_R(y) is contained in B_rho(0) and cs rho < R. By (M1) with s = cs rho <= r < R and mu(B_r(y)) <= mu(B_rho(0)) <= (1+delta) omega_n rho^n, letting r -> R: omega_n^-1 (cs rho)^-n mu(B_{cs rho}(y)) <= e^(2 Lambda)(1+delta)(1 - kappa_0)^-n + 2 e^Lambda Lambda/omega_n <= (1 + C_1 delta)(1 - kappa_0)^-n. By Bernoulli, (1 - kappa_0)^n >= 1 - n kappa_0 >= 1 - eps/8, so (1 - kappa_0)^-n <= 1 + eps/4 <= 1 + eps/2 (eps/8 <= 1/2). Hence the ratio is at most (1 + C_1 delta)(1 + eps/2) <= 1 + eps/2 + 2 C_1 delta <= 1 + eps once delta <= eps/(4 C_1).

3. Case (b): |y| > kappa_0 rho. Put R := |y|/(1 - theta_0). Since gamma_b + theta_0 = (5 + 3 gamma)/8 < 1, R <= gamma_b rho/(1 - theta_0) < rho, and R > |y| > kappa_0 rho.
 Rescaling. By the child rescaled_varifold with c = 0 and scale R there is a contract varifold V~ in U~ := {x : R x in U} (open, containing B_{rho/R}(0), hence B_1(0)) with weight mu~ = R^-n (x -> x/R)_# mu, so that mu~(B_t(x)) = R^-n mu(B_{R t}(R x)), and with generalized mean curvature H~(x) = R H(R x), so that the integral over B_t(0) of |H~| d mu~ equals R^(1-n) times the integral over B_{R t}(0) of |H| d mu. Put xi~ := y/R, so |xi~| = 1 - theta_0.
 Hypotheses of 6.1 for V~ with lam := delta, theta := theta_0, delta~ := 3 C_1 delta and Lambda~ = 2 omega_n (we require delta < 1/4 and 3 C_1 delta < 1/4; also theta_0 < 1/4): for every r' in [delta, 1], |mu~(B_1(0))/omega_n - mu~(B_delta(0))/(omega_n delta^n)| = |omega_n^-1 R^-n mu(B_R(0)) - omega_n^-1 (delta R)^-n mu(B_{delta R}(0))| <= 2 C_1 delta by (1a) (R, delta R <= rho), and r'^(1-n) integral over B_{r'}(0) of |H~| d mu~ = (r' R)^(1-n) integral over B_{r' R}(0) of |H| d mu <= C_1 delta by (1b) (r' R <= rho); the sum is <= 3 C_1 delta = delta~. Moreover mu~(B_1(0)) = R^-n mu(B_R(0)) <= (1 + C_1 delta) omega_n <= 2 omega_n.
 First conclusion of 6.1 with rho~ := theta_0 (in (0, theta]) and tau := 2 delta (in [2 lam, 1]): mu~(B_{(1 - delta~^(1/4)) theta_0}(xi~)) <= (2 delta)^-n mu~(B_{2 delta theta_0}(2 delta xi~)) + C_9' delta~^(1/4) |log delta|. In terms of mu, with r_y := (1 - delta~^(1/4)) theta_0 R:
 R^-n mu(B_{r_y}(y)) <= (2 delta R)^-n mu(B_{2 delta theta_0 R}(2 delta y)) + C_9' delta~^(1/4) |log delta|.
 First term: |2 delta y| <= 2 delta rho <= rho/2, so B_{rho/2}(2 delta y) is contained in B_rho(0); with s := 2 delta theta_0 R < rho/2, (M1) at 2 delta y with radius rho/2 and s <= r' < rho/2, together with mu(B_{r'}(2 delta y)) <= mu(B_{rho/2 + 2 delta rho}(0)) <= (1 + C_1 delta) omega_n (rho/2 + 2 delta rho)^n (by (1a), as rho/2 + 2 delta rho <= rho), gives after letting r' -> rho/2: omega_n^-1 s^-n mu(B_s(2 delta y)) <= e^(2 Lambda)(1 + 4 delta)^n (1 + C_1 delta) + 2 e^Lambda Lambda/omega_n =: 1 + eta_2(delta), where eta_2(delta) -> 0 as delta -> 0. Since (2 delta R)^-n mu(B_s(2 delta y)) = theta_0^n s^-n mu(B_s(2 delta y)):
 omega_n^-1 r_y^-n mu(B_{r_y}(y)) <= (1 - delta~^(1/4))^-n [1 + eta_2(delta) + C_9' delta~^(1/4) |log delta|/(omega_n theta_0^n)] =: 1 + eta_3(delta),
 and eta_3(delta) -> 0 as delta -> 0 because delta~^(1/4) |log delta| = (3 C_1)^(1/4) delta^(1/4) |log delta| -> 0.
 Transfer to the scale cs rho: if delta~^(1/4) <= 1/2 then r_y >= theta_0 R/2 > theta_0 kappa_0 rho/2 = cs rho, and B_{r_y}(y) is contained in B_R(0), hence in B_rho(0) (|y| + r_y <= (1 - theta_0) R + theta_0 R = R). (M1) at y with radius r_y, s = cs rho <= r' < r_y, letting r' -> r_y: omega_n^-1 (cs rho)^-n mu(B_{cs rho}(y)) <= e^(2 Lambda) omega_n^-1 r_y^-n mu(B_{r_y}(y)) + 2 e^Lambda Lambda/omega_n <= e^(2 Lambda)(1 + eta_3(delta)) + 2 e^Lambda Lambda/omega_n. The right side tends to 1 as delta -> 0 (Lambda = delta/kappa), so it is <= 1 + eps for all delta below a positive threshold delta_b depending only on n, l, p, gamma, eps.

4. Conclusion of the estimate. In both cases mu(B_{cs rho}(y)) <= (1 + eps) omega_n (cs rho)^n, which is the claimed inequality V.weight(closedBall y (cs rho)) <= ENNReal.ofReal((1 + eps)(omega_n (cs rho)^n)) (the mass is finite).

5. Choice of delta_P. delta_P > 0 is the minimum of the finitely many positive thresholds used: delta <= kappa, C_1 delta <= 1, delta <= 1/8 (so delta < 1/4), delta <= 1/(24 C_1) (so 3 C_1 delta < 1/4), (3 C_1 delta)^(1/4) <= 1/2, delta <= eps/(4 C_1) (case (a)), and delta <= delta_b (case (b)). All of them depend only on n, l, p, gamma, eps (C_9 = C_9(n, l, 2 omega_n)), and cs depends only on n, gamma, eps; so delta_P and cs are chosen before V, H, delta, rho, as the statement requires.

## Key steps

1. Monotonicity gives (1a) mass ratios at 0 within C_1 delta of 1 and (1b) curvature bounds at all radii <= rho
2. Points near 0: (M1) with R = (1 - kappa_0) rho
3. Other points: dilate by R = |y|/(1 - theta_0) and apply 6.1 with lam = delta, tau = 2 delta
4. (M1) at 2 delta y controls the comparison ball; (M1) at y transfers the pinching from r_y down to cs rho
5. Choose delta_P from the finitely many thresholds

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean; cmp <snapshot>/project/GMT/Ch05/Submission.lean GMT/Ch05/Submission.lean`
- `rg -l 'any_radius_' <snapshot>/project`
- `python3 -I scan of every lean_name field in dag.json and nodes/*/*.json of this run (reservation check)`
- `rg -l -t lean 'Campanato' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem measurePreserving_homeomorphUnitSphereProd|^def toSphere|theorem toSphere_apply_univ' <snapshot>/mathlib/Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`
- `rg -n 'lemma toSphere|theorem toSphere|def volumeIoiPow' <snapshot>/mathlib/Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`
- `rg -n 'theorem ae_tendsto_average_norm_sub' <snapshot>/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `rg -n 'protected def vitaliFamily|theorem tendsto_filterAt' <snapshot>/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `rg -n 'hausdorffMeasure_smul' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'localInverse' <snapshot>/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `rg -n 'theorem volume_closedBall' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `rg -n 'theorem MeasurableSet.image_of_continuousOn_injOn' <snapshot>/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `rg -n 'norm_image_sub_le_of_norm_fderivWithin_le' <snapshot>/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `rg -n 'tendsto_log_mul_rpow_nhdsGT_zero' <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean`
- `rg -n 'Measure.support|support_mem_ae' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `grep -n 'def HasWeightedApproximateTangentSpaceAt|def blowUpMap|def CountablyRectifiable|theorem HasWeightedApproximateTangentSpaceAt.unique' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `rg -n 'def lpMeanCurvatureKappa|structure LpAnnularCorrection|exists_lpAnnularCorrection|one_le_stationaryDensityReal_of_mem_support_lp' .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpMeanCurvature.lean Chapter04/LpAnnular.lean Chapter04/LpLowerDensity.lean; rg -c '\bsorry\b' .lake/packages/simongmt/Poincare/SimonGMT`
- `lake build GMT.Ch05.Submission in the scratch copy /tmp/anyrad-v2/proj of the pinned project (packages symlinked to the workspace .lake/packages)`
- `lake env lean Checks/Types.lean (import GMT.Ch05.Submission; namespace GMT.Ch05; the 12 child types)`
- `lake env lean Checks/Final.lean (12 child types + ParentSkeleton.parent_assembly + RateSkeleton.rate_skeleton + 6.1 shape check)`
- `lake env lean Checks/Inst.lean (set_option pp.explicit true; #check of the weight smul, real scalars and rpow expressions)`
- `lake env lean Checks/Axioms.lean (#print axioms of the cited library results)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpMeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpAnnular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpLowerDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1/decomposition-audit-v1.json`
- `/tmp/anyrad-v2/proj/Checks/Types.lean`
- `/tmp/anyrad-v2/proj/Checks/Final.lean`
- `/tmp/anyrad-v2/proj/Checks/Inst.lean`
- `/tmp/anyrad-v2/proj/Checks/Axioms.lean`

Snapshot and reservations
- Pinned at project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json).
- Its Contract.lean and Submission.lean are byte-identical to the workspace copies (cmp).
- No-match results: 'any_radius_' occurs in 0 snapshot project files; within the run it appears only in this node's own v1 proposal. 'Campanato' matches 0 Mathlib files, so campanato is proved from scratch.
- dag.json and all nodes/*/*.json reserve only: the 12 first-level names, the tilt_excess_height_estimate children (rectifiableVarifold_ae_tangentProj_starProjection, divM_height_test_field_eq, hsNorm_starProjection_trace_identities, exists_smooth_cutoff_half_ball_grad_le), and the aal_/allard52_/lgc_/lip_approx_/w12_ proposal names. No any_radius_* name collides.

Mathlib in the snapshot, by child
- radial_height (polar coordinates): measurePreserving_homeomorphUnitSphereProd (Constructions/HaarToSphere.lean:142), toSphere (:51), toSphere_apply_univ (:87), volumeIoiPow (:113).
- graph_comparison (Besicovitch differentiation): VitaliFamily.ae_tendsto_average_norm_sub (Covering/Differentiation.lean:837), with Besicovitch.vitaliFamily (Covering/Besicovitch.lean:1021) and tendsto_filterAt (:1060). It needs a measure that is locally finite on the whole space, hence mu restricted to B_rho(0).
- rescaled_varifold: Measure.hausdorffMeasure_smul₀ (Measure/Hausdorff.lean:753).
- patching: HasStrictFDerivAt.localInverse and to_localInverse (Calculus/InverseFunctionTheorem/FDeriv.lean:149).
- campanato: InnerProductSpace.volume_closedBall (Measure/Lebesgue/VolumeOfBalls.lean:354; EuclideanSpace version :324).
- Shared tools:
  - MeasurableSet.image_of_continuousOn_injOn (Constructions/Polish/Basic.lean:821);
  - Convex.norm_image_sub_le_of_norm_fderivWithin_le (Calculus/MeanValue.lean:484);
  - tendsto_log_mul_rpow_nhdsGT_zero (SpecialFunctions/Pow/Asymptotics.lean:401), for the delta^(1/4)|log delta| thresholds;
  - Measure.support and support_mem_ae (Measure/Support.lean).

Pinned SimonGMT package (outside the snapshot; rg finds 0 sorry)
- HasWeightedApproximateTangentSpaceAt (Chapter03/Rectifiable.lean:330) uses Bochner blow-up integrals over blowUpMap x r '' M (:96). Its uniqueness where theta != 0 (:345) justifies rescaled_varifold's exact tangent transport and tangent_ae's identification of tangentProj.
- monotonicity_bounds uses the corrected monotonicity:
  - lpMeanCurvatureKappa = (p-n)/(4p) (Chapter04/LpMeanCurvature.lean:76);
  - LpAnnularCorrection (LpAnnular.lean:335);
  - exists_lpAnnularCorrection and its _of_memLp variant (:358, :407);
  - one_le_stationaryDensityReal_of_mem_support_lp (LpLowerDensity.lean:43).

  These are stated for Chapter04.RectifiableVarifold, so the bridge via tangent_ae is spelled out.

Lean checks
- GMT.Ch05.Submission was built in a scratch copy of the pinned project. All 12 child types elaborate after 'import GMT.Ch05.Submission' in namespace GMT.Ch05.
- Three skeletons type-check, with only routine glue left as sorry:
  - the parent assembly (children + AllardRegularityTheorem + ConicalApproximationTheorem + TiltExcessDecayTheorem gives AllardRegularityAnyRadius);
  - graph_rate, with the C_II/C_III normalisation proved;
  - a shape check of 6.1.
- pp.explicit shows Measure.instSMul (ENNReal) and WithLp.instSMul (real scalars).
- #print axioms of every cited library result gives only propext, Classical.choice and Quot.sound.
