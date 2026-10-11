# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_any_radius-a1`
- Child DAG node: `root.allard_any_radius-a1.patching-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 of the parent proof ('One graph over T_0'), with its parameters made explicit: r = r_* (scale of the local graphs), eps = eps_2, kappa = kappa_1, gh = gammahat, ga = gamma_a, gb = gamma_b, r_0 = radius of the graph at 0. Notation: B_s(x) closed and B^o_s(x) open balls; T_0 := rotatedPlane q_0 = q_0(R^n x {0}), so T_0^perp = q_0({0} x R^l); P_0 and Q_0 := I - P_0 are the orthogonal projections onto T_0 and T_0^perp. Thus infDist y T_0 = |Q_0 y|, P_0 q_0(graphPoint(a, b)) = q_0(graphPoint(a, 0)), Q_0 q_0(graphPoint(a, b)) = q_0(graphPoint(0, b)), and |graphPoint(a, b)|^2 = |a|^2 + |b|^2. ||.|| is the operator norm and ||A|| <= hsNorm A.

0. Preliminaries. (a) For each y in S cap B_{ga rho}(0) fix q_y, v_y as in the local-graph hypothesis and put Psi_y(x) := y + q_y(graphPoint(x, v_y(x))). As r > 0, B_r(0) is convex with nonempty interior, v_y is differentiable within it with derivative fderivWithin, and ||fderivWithin v_y|| <= hsNorm <= eps; by the mean value inequality v_y is eps-Lipschitz on B_r(0), so |v_y(x)| <= eps |x|; on the open ball B^o_r(0), v_y is C^1 with fderiv = fderivWithin. (b) The hypothesis (fun x => y + x)^-1(S) cap B_r(0) = q_y(graphOver v_y(B_r(0))) cap B_r(0) says: every point of S cap B_r(y) is Psi_y(x) for some x in B_r(0), and Psi_y(x) is in S whenever x is in B_r(0) and |Psi_y(x) - y| <= r. (c) Likewise u_0 is 1-Lipschitz on B_{r_0}(0), |u_0(x)| <= |x|, and u_0 is C^1 near 0 with fderiv u_0 0 = fderivWithin u_0 (B_{r_0}(0)) 0 = 0 (0 is interior). (d) vartheta := 2 kappa rho/r + eps <= 1/24 + 1/24 = 1/12 (48 kappa rho <= r, eps <= 1/24), 2 kappa rho <= r/24, and 0 < kappa < 1 (gh <= (1 - kappa) ga with gh > 0); also ga < gb <= 1. (e) 0 is in S: 0 = q_0(graphPoint(0, u_0 0)) lies in q_0(graphOver u_0(B_{r_0}(0))) cap B_{r_0}(0) = S cap B_{r_0}(0).

1. Local planes are close to T_0. Let y be in S cap B_{ga rho}(0), T_y := q_y(R^n x {0}), and let e = q_y(graphPoint(e', 0)) be a unit vector of T_y (|e'| = 1). The points y_+- := Psi_y(+-(r/2) e') satisfy |y_+- - y| <= (r/2)(1 + eps) < r, so they lie in S cap B_r(y) by 0(b), which is contained in S cap B_{gb rho}(0) because ga rho + r <= gb rho. Moreover y_+ - y_- = r e + q_y(graphPoint(0, w)) with w := v_y(r e'/2) - v_y(-r e'/2), |w| <= eps r. By the cone hypothesis |Q_0 y_+-| <= kappa |y_+-| <= kappa gb rho <= kappa rho. Hence r |Q_0 e| <= |Q_0(y_+ - y_-)| + |w| <= 2 kappa rho + eps r, i.e. |Q_0 e| <= vartheta. Consequently |Q_0 v| <= vartheta |v| and |P_0 v| >= (1 - vartheta)|v| for every v in T_y.

2. Local graphs over T_0. Fix y in S cap B_{ga rho}(0). Let Phi_y := P_0 o Psi_y on B_r(0), A_y x := P_0 q_y(graphPoint(x, 0)) (linear from R^n to T_0) and g_y(x) := P_0 q_y(graphPoint(0, v_y(x))). Then Phi_y = P_0 y + A_y + g_y. Since q_y(graphPoint(x, 0)) is in T_y with norm |x|, step 1 gives |A_y x| >= (1 - vartheta)|x|; so A_y is an injective linear map between n-dimensional spaces, hence a bijection onto T_0 with ||A_y^-1|| <= (1 - vartheta)^-1 <= 12/11; and g_y is eps-Lipschitz with g_y(0) = 0.
 (i) |Phi_y(x_1) - Phi_y(x_2)| >= (1 - vartheta - eps)|x_1 - x_2| >= (7/8)|x_1 - x_2| for x_1, x_2 in B_r(0).
 (ii) Let D_y := T_0 cap B_{r/2}(P_0 y). For w in D_y, the map Fix_w(x) := A_y^-1(w - P_0 y - g_y(x)) maps B_{0.6 r}(0) into itself (|A_y^-1(w - P_0 y)| <= (12/11)(r/2) and |A_y^-1 g_y(x)| <= (12/11) eps (0.6 r) <= (12/11)(0.025 r), total <= (12/11)(0.525) r < 0.6 r) and is a contraction with constant (12/11) eps <= 1/22. Its unique fixed point x(w) in B_{0.6 r}(0) satisfies Phi_y(x(w)) = w, and Psi_y(x(w)) is in S cap B_r(y) because |Psi_y(x(w)) - y| <= 0.6 r (1 + eps) < r (step 0(b)).
 (iii) If x is in S cap B_r(y) and P_0 x is in D_y, then x = Psi_y(x') for some x' in B_r(0) (step 0(b)), Phi_y(x') = P_0 x = Phi_y(x(P_0 x)), so x' = x(P_0 x) by (i), i.e. x = Psi_y(x(P_0 x)).
 Thus S cap B_r(y) cap P_0^-1(D_y) = {w + nu_y(w) : w in D_y} with nu_y(w) := Q_0 Psi_y(x(w)) in T_0^perp (note P_0 Psi_y(x(w)) = w).
 (iv) Regularity. On B^o_r(0), Phi_y is C^1 with DPhi_y(x) h = A_y h + P_0 q_y(graphPoint(0, Dv_y(x) h)) and |DPhi_y(x) h| >= (1 - vartheta - eps)|h|, so DPhi_y(x) is invertible onto T_0 with ||DPhi_y(x)^-1|| <= 8/7. For w in the relative interior D_y^o := T_0 cap B^o_{r/2}(P_0 y), the point x(w) lies in B_{0.6 r}(0), inside B^o_r(0). By the inverse function theorem (Mathlib HasStrictFDerivAt.to_localInverse) Phi_y has a C^1 local inverse near w with values near x(w); it coincides with w' -> x(w') on a neighbourhood of w in D_y^o by the injectivity (i) (both are points of B_r(0) mapped to w' by Phi_y). Hence nu_y = Q_0 o Psi_y o x is C^1 on D_y^o with Dnu_y(w) = Q_0 DPsi_y(x) DPhi_y(x)^-1, x = x(w). For h in R^n, DPsi_y(x) h = q_y(graphPoint(h, 0)) + q_y(graphPoint(0, Dv_y(x) h)), so |Q_0 DPsi_y(x) h| <= vartheta |h| + eps |h| <= |h|/8 by step 1. Therefore ||Dnu_y(w)|| <= (1/8)(8/7) = 1/7.

3. P_0 is injective on S cap B_{ga rho}(0). If y_1, y_2 are in this set and P_0 y_1 = P_0 y_2, then |y_1 - y_2| = |Q_0 y_1 - Q_0 y_2| <= kappa(|y_1| + |y_2|) <= 2 kappa rho <= r/24 < r, so y_2 is in S cap B_r(y_1) with P_0 y_2 = P_0 y_1 in D_{y_1}. Also y_1 = Psi_{y_1}(0) (v_{y_1}(0) = 0) and Phi_{y_1}(0) = P_0 y_1, so x(P_0 y_1) = 0 by (i), and by 2(iii) y_2 = Psi_{y_1}(x(P_0 y_1)) = y_1.

4. The global function nu. Let D := P_0(S cap B_{ga rho}(0)) and define nu : D -> T_0^perp by nu(P_0 y) := Q_0 y (well defined by step 3); thus S cap B_{ga rho}(0) = {w + nu(w) : w in D}. If y is in S cap B_{ga rho}(0) and w = P_0 x is in D cap D_y with x in S cap B_{ga rho}(0), then |x - y| <= |P_0 x - P_0 y| + |Q_0 x| + |Q_0 y| <= r/2 + 2 kappa rho < r, so by 2(iii) x = w + nu_y(w): nu = nu_y on D cap D_y.

5. D contains Omega := T_0 cap B^o_{gh rho}(0).
 (a) If x' is in S cap B_{gb rho}(0), then |x'| <= |P_0 x'| + |Q_0 x'| <= |P_0 x'| + kappa |x'|, so |x'| <= |P_0 x'|/(1 - kappa).
 (b) Let D' := D cap Omega; 0 is in D' (0 in S, P_0 0 = 0). D' is open in Omega: let w = P_0 y be in D' (y in S cap B_{ga rho}(0)) and w' in Omega cap D_y. Then x' := w' + nu_y(w') = Psi_y(x(w')) is in S cap B_r(y), which is contained in S cap B_{gb rho}(0), so by (a) |x'| <= |w'|/(1 - kappa) < gh rho/(1 - kappa) <= ga rho; hence x' is in S cap B_{ga rho}(0) and w' = P_0 x' is in D'. As Omega cap D_y contains Omega cap B^o_{r/2}(w), D' is a neighbourhood of w in Omega. D' is closed in Omega: if w_k = P_0 y_k in D' (y_k in S cap B_{ga rho}(0)) converge to w in Omega, a subsequence of (y_k) converges to some y with |y| <= ga rho <= rho; since S cap B_rho(0) is closed, y is in S cap B_{ga rho}(0), and P_0 y = w, so w is in D'. Omega is convex, hence connected, so D' = Omega.

6. Definition of u and the conclusions. For x in B^o_{gh rho}(0) the point w(x) := q_0(graphPoint(x, 0)) lies in Omega, contained in D, and nu(w(x)) is in T_0^perp = q_0({0} x R^l); let u(x) be the unique vector with q_0(graphPoint(0, u(x))) = nu(w(x)), and put u(x) := 0 for |x| >= gh rho. Then q_0(graphPoint(x, u(x))) = w(x) + nu(w(x)) for x in B^o_{gh rho}(0).
 (a) C^1 with ||Du|| <= 1/7: given x in B^o_{gh rho}(0), choose y in S cap B_{ga rho}(0) with P_0 y = w(x). Then w(x) is the centre of D_y, so Omega cap D_y^o is a neighbourhood of w(x) in T_0 on which nu = nu_y (step 4), which is C^1 with ||Dnu|| <= 1/7 (step 2(iv)). Since u is nu composed with the linear isometric embedding x -> q_0(graphPoint(x, 0)) and followed by the linear map z -> (last l coordinates of q_0^-1 z), which is isometric on T_0^perp, u is C^1 near x with ||Du(x)|| <= 1/7. Hence ContDiffOn 1 on B^o_{gh rho}(0) and ||fderiv u x|| <= 1/7 there.
 (b) Graph inclusion: for x in B^o_{gh rho}(0), q_0(graphPoint(x, u x)) = w(x) + nu(w(x)) is in S cap B_{ga rho}(0) by definition of nu, and by 5(a) its norm is at most |w(x)|/(1 - kappa) = |x|/(1 - kappa) < gh rho/(1 - kappa) <= ga rho. So q_0(graphOver u (B^o_{gh rho}(0))) is contained in S cap B^o_{ga rho}(0).
 (c) Reverse inclusion: if z is in S cap B^o_{gh rho}(0), then z is in S cap B_{ga rho}(0), so z = w + nu(w) with w = P_0 z and |w| <= |z| < gh rho; writing w = q_0(graphPoint(x, 0)) with |x| = |w|, we get z = q_0(graphPoint(x, u x)) with x in B^o_{gh rho}(0).
 (d) u = u_0 on B^o_{r_0/2}(0): for |x| < r_0/2, zeta := q_0(graphPoint(x, u_0 x)) has |zeta| <= sqrt(2)|x| < r_0, so zeta is in q_0(graphOver u_0(B_{r_0}(0))) cap B_{r_0}(0) = S cap B_{r_0}(0), contained in S cap B_{ga rho}(0) (r_0 <= gh rho < ga rho). Since P_0 zeta = w(x) and |x| < r_0/2 <= gh rho, w(x) is in Omega and, by the definition of nu, nu(w(x)) = Q_0 zeta = q_0(graphPoint(0, u_0 x)); hence u(x) = u_0(x).
 (e) u(0) = u_0(0) = 0, and since u = u_0 on the neighbourhood B^o_{r_0/2}(0) of 0, fderiv u 0 = fderiv u_0 0 = 0 by 0(c).

## Key steps

1. Points of the local graph at distance r/2 and the cone condition force every local plane T_y to be vartheta-close to T_0, vartheta <= 1/12
2. Contraction mapping and the inverse function theorem make each local graph a C^1 graph over a disc of T_0 with slope <= 1/7
3. P_0 is injective on S cap B_{ga rho}(0), so the local graphs define one function nu on D = P_0(S cap B_{ga rho}(0))
4. Openness (cone condition) and closedness of D cap Omega in the connected disc Omega give Omega contained in D
5. Transfer nu to u on B^o_{gh rho}(0); u = u_0 near 0 by injectivity; both graph inclusions follow

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
