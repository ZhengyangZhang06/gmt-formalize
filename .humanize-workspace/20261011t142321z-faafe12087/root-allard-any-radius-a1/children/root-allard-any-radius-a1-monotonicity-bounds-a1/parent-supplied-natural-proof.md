# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_any_radius-a1`
- Child DAG node: `root.allard_any_radius-a1.monotonicity_bounds-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 4, 4.1-4.10 (printed proof), with the coefficient in front of Lambda in 4.2 equal to kappa = (p-n)/(4p), the value required by the integration after 4.4 (SimonGMT Chapter04 lpMeanCurvatureKappa, LpAnnularCorrection, exists_lpAnnularCorrection, one_le_stationaryDensityReal_of_mem_support_lp). This is fact (M) together with step 1 of the parent proof. Notation: mu := V.weight, B_r(y) closed and B^o_r(y) open balls, omega_n := unitBallVolume n, p_x := V.tangentProj x, p_x^perp := I - p_x, K(y,R) := (R^(p-n) integral over B_R(y) of |H|^p d mu)^(1/p), kappa := (p-n)/(4p), Lambda := delta/kappa = 4 p delta/(p-n), alpha' := 1 - n/p. Masses of balls inside B_rho(0) are finite (they are at most mu(B_rho(0)) <= (1+delta) omega_n rho^n), so all statements about masses may be read for their real values.

0. Setup. 2.3 gives rho > 0, B_rho(0) contained in U, theta >= 1 mu-a.e., 0 in spt V, mu(B_rho(0)) <= (1+delta) omega_n rho^n and K(0,rho) <= delta; in particular H is in L^p(mu restricted to B_rho(0)). Since delta <= kappa, Lambda <= 1. If B_R(y) is contained in B_rho(0), then R <= rho and K(y,R)^p = R^(p-n) integral over B_R(y) of |H|^p <= (R/rho)^(p-n) rho^(p-n) integral over B_rho(0) of |H|^p <= delta^p, so K(y,R) <= delta = kappa Lambda. By the child tangent_ae, for mu-a.e. x the map p_x is the orthogonal projection onto the n-dimensional approximate tangent space T_x M, x -> p_x is mu-a.e. strongly measurable, and Theta^n(mu,x) = theta(x).

1. Radial first variation (Ch. 4, 3.3-3.6 and 4.1). Fix y, R with B_R(y) contained in B_rho(0); write r := |x - y|. For sigma in (0, R) and eps > 0 with (1+eps) sigma < R take phi in C^1(R, [0,1]) with phi' <= 0, phi = 1 on (-infinity, 1] and phi = 0 on [1+eps, infinity). The field X(x) := phi(r/sigma)(x - y) is C^1 with compact support in B_R(y), contained in U. At mu-a.e. x (where p_x is a rank-n projection), div_M X = n phi(r/sigma) + (r/sigma) phi'(r/sigma) (1 - |p_x^perp(x - y)|^2/r^2). With I(sigma) := integral phi(r/sigma) d mu and J(sigma) := integral phi(r/sigma) |p_x^perp(x - y)|^2 r^-2 d mu, the first variation identity (generalized mean curvature) gives Simon's 4.1: d/d sigma (sigma^-n I(sigma)) = sigma^-n d/d sigma J(sigma) + sigma^(-n-1) integral (x - y) . H phi(r/sigma) d mu.

2. Hoelder (4.3). As phi(r/sigma) = 0 for r > (1+eps) sigma, Hoelder's inequality and a^(1-1/p) <= 1 + a (a >= 0) give |sigma^(-n-1) integral (x - y) . H phi(r/sigma) d mu| <= (1+eps) sigma^(-n/p) ||H||_{L^p(B_R(y))} (sigma^-n I(sigma))^(1-1/p) <= f(sigma)(1 + sigma^-n I(sigma)), with f(sigma) := 2 kappa Lambda R^-1 (sigma/R)^(-n/p) (using K(y,R) <= kappa Lambda and 1+eps <= 2). So 4.1 reads d/d sigma (sigma^-n I) = sigma^-n J' - F_0(sigma)(1 + sigma^-n I) with |F_0| <= f, and integral_0^sigma f = 2 kappa Lambda (sigma/R)^(1-n/p) p/(p-n) = (Lambda/2)(sigma/R)^alpha'. This is exactly where kappa = (p-n)/(4p) is needed.

3. Integrating factor (4.4-4.6). With F(sigma) := exp(integral_0^sigma F_0) one has d/d sigma [F sigma^-n I + F - 1] = F sigma^-n J' (4.4), and e^-Lambda <= e^(-(Lambda/2)(sigma/R)^alpha') <= F(sigma) <= e^((Lambda/2)(sigma/R)^alpha') <= e^Lambda, |F(sigma) - 1| <= (1/2) e^(Lambda/2) Lambda (sigma/R)^alpha' (4.5); for Lambda <= 1, |F(sigma) - 1| <= Lambda (sigma/R)^alpha' <= Lambda (4.6), because |e^t - 1| <= |t| e^|t| <= 2|t| for |t| <= 1/2; and F(sigma) -> 1 as sigma -> 0.

4. Annular identity (4.7, 4.8). Integrating 4.4 from s to r and letting eps -> 0 (F_0 depends on eps; the uniform bounds of step 3 allow passing to a limit factor F, as in SimonGMT exists_cancellationFactor_squeeze), one obtains a function F on (0, R) satisfying the bounds of step 3 and, for 0 < s <= r < R,
 Phi(r) - Phi(s) = G(s,r) integral over B_r(y) minus B_s(y) of |p_x^perp(x - y)|^2 |x - y|^(-n-2) d mu(x), with G(s,r) in [e^-Lambda, e^Lambda],
 where Phi(t) := F(t) t^-n mu(B_t(y)) + F(t) - 1. In particular Phi is nondecreasing on (0, R). [Lean route: SimonGMT LpAnnularCorrection (fields factor_bounds, error_bound_of_le_one, annular_identity, annular_factor_bounds, monotone), obtained from HasGeneralizedMeanCurvatureIn.exists_lpAnnularCorrection(_of_memLp) for the Chapter04 varifold built from V restricted to the open ball W' := B^o_R(y) (on whose closure, contained in B_rho(0), H is L^p), applied at radii R'' < R: carrier a Borel set M~ contained in M cap W' with H^n((M cap W') minus M~) = 0 and theta >= 1 on M~ (possible because H^n(M cap {theta < 1}) = 0, theta being >= 1 mu-a.e. and positive on M), multiplicity theta, tangent field x -> T_x M from tangent_ae. For theta >= 1 the measure H^n restricted to M~ is at most mu, hence locally finite, so by Simon Ch. 3, Remark 1.8(1) the unweighted approximate tangent space of M~ exists and equals T_x M at H^n-a.e. x of M~; the weight of this varifold is mu restricted to W', its tangential divergence agrees mu-a.e. with div_M, and its first variation identity in W' is that of V. Since the inequalities below only involve radii r < R, apply the identity on (0, R''] and let R'' increase to R.]

5. Density. By step 4, Phi is nondecreasing on (0, R) and Phi(t) >= -Lambda, so lim_{t -> 0} Phi(t) exists; as F(t) -> 1, Theta(y) := lim_{t -> 0} omega_n^-1 t^-n mu(B_t(y)) exists and omega_n Theta(y) = lim_{t -> 0} Phi(t) <= Phi(r) for every r in (0, R). Moreover mu({y}) <= mu(B_t(y)) = O(t^n) -> 0.

6. Theta >= 1 on spt V cap B^o_rho(0) (Ch. 4, 4.9 and 4.10(1)). Every z in W := B^o_rho(0) is the centre of the ball B_{(rho - |z|)/2}(z) contained in B_rho(0), so steps 1-5 apply at z. Upper semicontinuity: let z_k -> z in W, put R := (rho - |z|)/4, so that B_R(z_k) is contained in B_rho(0) for large k, and let 0 < r < R. By steps 5 and 3, omega_n Theta(z_k) <= Phi_{z_k}(r) <= e^((Lambda/2)(r/R)^alpha') r^-n mu(B_r(z_k)) + Lambda (r/R)^alpha'. Since limsup_k mu(B_r(z_k)) <= mu(B_r(z)) (closed balls), limsup_k omega_n Theta(z_k) <= e^((Lambda/2)(r/R)^alpha') r^-n mu(B_r(z)) + Lambda (r/R)^alpha', and letting r -> 0 gives limsup_k Theta(z_k) <= Theta(z). Hence {z in W : Theta(z) < 1} is open. By tangent_ae (c) and theta >= 1 mu-a.e., Theta = theta >= 1 mu-a.e., so this open set is mu-null and therefore disjoint from spt mu. Thus Theta(z) >= 1 for every z in spt V cap W.

7. Proof of (M1). Let B_R(y) be contained in B_rho(0) and 0 < s <= r < R. By step 4, Phi(s) <= Phi(r). Using |F - 1| <= Lambda and F <= e^Lambda (step 3): F(s) s^-n mu(B_s(y)) = Phi(s) - (F(s) - 1) <= Phi(r) + Lambda = F(r) r^-n mu(B_r(y)) + (F(r) - 1) + Lambda <= e^Lambda r^-n mu(B_r(y)) + 2 Lambda. Dividing by F(s) >= e^-Lambda gives s^-n mu(B_s(y)) <= e^(2 Lambda) r^-n mu(B_r(y)) + 2 e^Lambda Lambda, which is (M1) (all masses are finite, so it holds for their real values).

8. Proof of (M2). Let y be in spt V and 0 < s < R with B_R(y) contained in B_rho(0). Then |y| <= rho - R < rho, so y is in spt V cap W and Theta(y) >= 1 by step 6. By step 5, F(s) s^-n mu(B_s(y)) = Phi(s) - (F(s) - 1) >= omega_n Theta(y) - Lambda >= omega_n - Lambda. If omega_n - Lambda <= 0, (M2) holds because its left side is <= 0 <= mu(B_s(y)). Otherwise s^-n mu(B_s(y)) >= (omega_n - Lambda)/F(s) >= e^-Lambda (omega_n - Lambda).

9. Proof of (M3). Apply step 4 with y = 0 and R = rho. For 0 < t < r < rho, integral over B_r(0) minus B_t(0) of |p_x^perp x|^2 |x|^(-n-2) d mu = (Phi(r) - Phi(t))/G(t,r) <= e^Lambda (Phi(r) - Phi(t)) <= e^Lambda (Phi(r) - omega_n Theta(0)) <= e^Lambda (Phi(r) - omega_n), using Phi(t) >= lim_{t' -> 0} Phi(t') = omega_n Theta(0) (step 5) and Theta(0) >= 1 (step 6, 0 in spt V). Also Phi(r) <= e^Lambda r^-n mu(B_r(0)) + Lambda <= e^Lambda r^-n (1+delta) omega_n rho^n + Lambda. Let t -> 0: the sets B_r(0) minus B_t(0) increase to B_r(0) minus {0}, mu({0}) = 0 (step 5), and the integrand |x - p_x x|^2/|x|^(n+2) of the statement equals |p_x^perp x|^2 |x|^(-n-2) for x != 0 and is 0 at x = 0; by monotone convergence its (lower) integral over B_r(0) is at most e^Lambda (e^Lambda r^-n (1+delta) omega_n rho^n + Lambda - omega_n). Let r -> rho: the balls B_r(0) increase to the open ball B^o_rho(0), and monotone convergence gives the bound e^Lambda (e^Lambda (1+delta) omega_n + Lambda - omega_n) for the integral over B^o_rho(0), which is (M3).

## Key steps

1. Under 2.3, K(y,R) <= delta = kappa Lambda whenever B_R(y) lies in B_rho(0); Lambda <= 1
2. Radial first variation, Hoelder with kappa = (p-n)/(4p) and an integrating factor F with e^-Lambda <= F <= e^Lambda, |F - 1| <= Lambda
3. Annular identity Phi(r) - Phi(s) = G times the conical integral, G in [e^-Lambda, e^Lambda]; Phi nondecreasing
4. Theta exists, is upper semicontinuous and equals theta >= 1 a.e., hence Theta >= 1 on spt V cap B^o_rho(0)
5. (M1) from Phi(s) <= Phi(r); (M2) from omega_n Theta(y) <= Phi(s); (M3) from the annular identity at 0 and monotone convergence

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
