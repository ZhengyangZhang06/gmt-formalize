# Parent-supplied natural-language proof

- Parent DAG node: `root.affine_approximation-a1`
- Child DAG node: `root.affine_approximation-a1.lp_monotonicity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 4, 3.2-3.6 (radial first variation and the epsilon-cutoff) and 4.1-4.8 (L^p mean curvature), with the coefficient in front of Lambda in 4.2 read as kappa = (p-n)/(4p) (the value required by the integration after 4.4; cf. SimonGMT Chapter04 lpMeanCurvatureKappa and LpAnnularCorrection), and with the passage epsilon -> 0 of the integrating factor carried out explicitly.

Notation (contract). mu := V.weight = theta H^n restricted to M (M = V.carrier, theta = V.mult); spt V := V.support = U cap spt mu; p_x := V.tangentProj x and p_x^perp v := v - p_x v; B_s(y) := closedBall y s (closed), B^o_s(y) := ball y s (open); omega_n := unitBallVolume n > 0; for z and s > 0, K(z,s) := V.scaledLpNorm H p z s = (s^(p-n) integral_{B_s(z)} |H|^p dmu)^(1/p) in [0,infinity]; kappa := (p-n)/(4p) > 0; g_y(x) := |x - y - p_x(x - y)|^2 / |x - y|^(n+2) (= 0 at x = y by the convention a/0 = 0). Also r(x) := |x - y|, nu(x) := (x - y)/r(x) and D^perp r(x) := p_x^perp nu(x) for x != y, and D^perp r(y) := 0, so that g_y(x) = |D^perp r(x)|^2 / r(x)^n for x != y (and both sides are 0 at x = y). For 0 < t <= S write ||H||_t := (integral_{B_t(y)} |H|^p dmu)^(1/p).

0. Preliminaries. By aal_tangent_structure (n >= 1, U open): for mu-a.e. x, p_x is the orthogonal projection onto an n-dimensional subspace (so p_x is symmetric, idempotent, trace p_x = n, |p_x v| <= |v|, and |p_x nu|^2 + |p_x^perp nu|^2 = |nu|^2 = 1), and x -> p_x is mu-a.e. strongly measurable, so g_y and all integrands below are mu-a.e. strongly measurable. B_S(y) is compact and contained in U, so mu(B_S(y)) < infinity (V.integrableOn_mult), and H is mu-integrable on B_S(y) (H is locally integrable on U, part of V.HasGeneralizedMeanCurvature). By hypothesis ||H||_S < infinity; t -> ||H||_t is nondecreasing, and ||H||_R = R^(n/p - 1) K(y,R) <= R^(n/p - 1) kappa Lambda (because K(y,R) = (R^(p-n) ||H||_R^p)^(1/p) = R^(1 - n/p) ||H||_R).
 Integrability in (ii): if 0 < s <= r <= R, then on B_r(y) minus B_s(y) we have r(x) > s, hence 0 <= g_y(x) <= |x - y|^2/|x - y|^(n+2) < s^(-n) for mu-a.e. such x (|p_x^perp v| <= |v|); as mu(B_r(y)) < infinity and g_y is a.e. strongly measurable, g_y is mu-integrable on B_r(y) minus B_s(y).

1. Cutoffs. Fix chi in C^1(R) nonincreasing with chi = 1 on (-infinity, 0] and chi = 0 on [1, infinity). For epsilon in (0,1] let phi_epsilon(t) := chi((t - 1)/epsilon): phi_epsilon is C^1, nonincreasing, 0 <= phi_epsilon <= 1, phi_epsilon = 1 on (-infinity, 1], phi_epsilon = 0 on [1 + epsilon, infinity), and for every t, phi_epsilon(t) -> indicator of (-infinity, 1] at t as epsilon -> 0+ (for t > 1 it is 0 once epsilon < t - 1).

2. Radial first variation (Simon 3.2, 4.1). Fix epsilon in (0,1] and rho > 0 with (1 + epsilon) rho < S. Let X(x) := phi_epsilon(r(x)/rho)(x - y). X equals x - y on B^o_rho(y) (phi_epsilon = 1 on (-infinity,1]) and is a composition of C^1 maps on the complement of {y}, so X is C^1; it vanishes outside B_{(1+epsilon) rho}(y), so it has compact support and tsupport X is contained in B_{(1+epsilon) rho}(y), which is contained in B_S(y) and hence in U. For x != y, DX(x) v = phi_epsilon(r/rho) v + rho^(-1) phi_epsilon'(r/rho) (nu . v)(x - y). At mu-a.e. x (where p_x is a rank-n orthogonal projection), using that the trace of v -> (nu . p_x v) w equals p_x nu . w,
 div_M X(x) = trace(DX(x) o p_x) = n phi_epsilon(r/rho) + (r/rho) phi_epsilon'(r/rho) (1 - |D^perp r|^2)
(at x = y the second term is absent because phi_epsilon' = 0 on (-infinity,1)). The definition of generalized mean curvature (V.HasGeneralizedMeanCurvature H, applicable to X) gives
 integral [n phi_epsilon(r/rho) + (r/rho) phi_epsilon'(r/rho)(1 - |D^perp r|^2)] dmu = - integral phi_epsilon(r/rho)(x - y) . H dmu. (2.1)
For 0 < rho < S/(1 + epsilon) put I(rho) := integral phi_epsilon(r/rho) dmu, J(rho) := integral phi_epsilon(r/rho)|D^perp r|^2 dmu, L(rho) := integral phi_epsilon(r/rho)(x - y) . H dmu (finite). The rho-derivative of phi_epsilon(r/rho) is -(r/rho^2) phi_epsilon'(r/rho), which is bounded uniformly for rho in compact subintervals and supported in B_S(y) (finite measure); by differentiation under the integral sign I and J are C^1 with I'(rho) = - integral (r/rho^2) phi_epsilon'(r/rho) dmu >= 0 and J'(rho) = - integral (r/rho^2) phi_epsilon'(r/rho) |D^perp r|^2 dmu >= 0, and L is continuous by dominated convergence (|phi_epsilon(r/rho)(x - y) . H| <= S |H| on B_S(y)). Since (r/rho) phi_epsilon'(r/rho) = - rho d/drho[phi_epsilon(r/rho)], (2.1) says n I - rho I' + rho J' = - L, i.e.
 d/drho (rho^(-n) I(rho)) = rho^(-n) J'(rho) + rho^(-n-1) L(rho). (2.2)

3. Hoelder estimate (Simon 4.2-4.3 with kappa = (p-n)/(4p)). As phi_epsilon(r/rho) = 0 for r >= (1+epsilon) rho and 0 <= phi_epsilon <= 1 (so phi_epsilon^(p/(p-1)) <= phi_epsilon), Hoelder's inequality gives |L(rho)| <= (1+epsilon) rho integral_{B_{(1+epsilon)rho}(y)} |H| phi_epsilon(r/rho) dmu <= (1+epsilon) rho ||H||_{(1+epsilon)rho} I(rho)^(1-1/p). Using a^(1-1/p) <= 1 + a (a >= 0),
 |rho^(-n-1) L(rho)| <= (1+epsilon) ||H||_{(1+epsilon)rho} rho^(-n/p) (rho^(-n) I(rho))^(1-1/p) <= (1+epsilon) ||H||_{(1+epsilon)rho} rho^(-n/p) (1 + rho^(-n) I(rho)).
Define a_epsilon(rho) := rho^(-n-1) L(rho) / (1 + rho^(-n) I(rho)), continuous on (0, S/(1+epsilon)), with
 |a_epsilon(rho)| <= (1+epsilon) ||H||_{(1+epsilon) rho} rho^(-n/p) <= 2 ||H||_S rho^(-n/p). (3.1)
Since n/p < 1, rho^(-n/p) is integrable near 0. Now (2.2) reads d/drho (1 + rho^(-n) I) = rho^(-n) J' + a_epsilon (1 + rho^(-n) I).

4. Integrating factor (Simon 4.4) and squeeze (Simon 3.5). For 0 < rho < S/(1+epsilon) let F_epsilon(rho) := exp(- integral_0^rho a_epsilon(t) dt); F_epsilon is C^1 with F_epsilon' = - a_epsilon F_epsilon, hence d/drho [F_epsilon(rho)(1 + rho^(-n) I(rho))] = F_epsilon(rho) rho^(-n) J'(rho) >= 0 and, for 0 < sigma <= rho < S/(1+epsilon),
 F_epsilon(rho)(1 + rho^(-n) I(rho)) - F_epsilon(sigma)(1 + sigma^(-n) I(sigma)) = integral_sigma^rho F_epsilon(t) t^(-n) J'(t) dt =: D_epsilon(sigma,rho). (4.1)
By Tonelli (the integrand F_epsilon(t) t^(-n) (-(r/t^2) phi_epsilon'(r/t)) |D^perp r|^2 is >= 0), D_epsilon(sigma,rho) = integral |D^perp r(x)|^2 [integral_sigma^rho F_epsilon(t) t^(-n) d/dt(phi_epsilon(r/t)) dt] dmu(x). For fixed x with r = r(x) > 0, d/dt(phi_epsilon(r/t)) = -(r/t^2) phi_epsilon'(r/t) >= 0 vanishes unless r/(1+epsilon) <= t <= r, where r^(-n) <= t^(-n) <= (1+epsilon)^n r^(-n), and integral_sigma^rho d/dt(phi_epsilon(r/t)) dt = phi_epsilon(r/rho) - phi_epsilon(r/sigma) >= 0. With c_epsilon(rho) := integral_0^rho |a_epsilon(t)| dt we have e^(-c_epsilon(rho)) <= F_epsilon(t) <= e^(c_epsilon(rho)) for 0 < t <= rho. Hence
 e^(-c_epsilon(rho)) A_epsilon(sigma,rho) <= D_epsilon(sigma,rho) <= e^(c_epsilon(rho)) (1+epsilon)^n A_epsilon(sigma,rho), (4.2)
where A_epsilon(sigma,rho) := integral r^(-n) (phi_epsilon(r/rho) - phi_epsilon(r/sigma)) |D^perp r|^2 dmu (integrand := 0 at x = y).

5. Letting epsilon -> 0 (Simon 3.6, 4.5-4.7). Fix a nonincreasing sequence epsilon_k -> 0+ with epsilon_1 <= 1 and (1 + epsilon_1) R < S (e.g. epsilon_k := epsilon_1/k), so that (1 + epsilon_k) R < S for every k, and write I_k, L_k, a_k, F_k, c_k, D_k, A_k for the objects above with epsilon = epsilon_k; all are defined for radii in (0, R].
 (5a) For t in (0, R]: I_k(t) -> mu(B_t(y)) and L_k(t) -> L_0(t) := integral_{B_t(y)} (x - y) . H dmu, by dominated convergence (phi_{epsilon_k}(r/t) -> indicator{r <= t}, dominated by the indicator of B_S(y), resp. by S |H| on B_S(y)). Hence a_k(t) -> a_0(t) := t^(-n-1) L_0(t)/(1 + t^(-n) mu(B_t(y))).
 (5b) By Hoelder as in Step 3 with the indicator of B_t(y) in place of phi: |L_0(t)| <= t ||H||_t mu(B_t(y))^(1-1/p), so |a_0(t)| <= ||H||_t t^(-n/p) <= ||H||_R t^(-n/p) <= kappa Lambda R^(-1) (t/R)^(-n/p) for 0 < t <= R. Since kappa/(1 - n/p) = 1/4,
 integral_0^rho |a_0(t)| dt <= kappa Lambda R^(-1) integral_0^rho (t/R)^(-n/p) dt = (Lambda/4)(rho/R)^(1-n/p) <= Lambda/4 (0 < rho <= R). (5.1)
 (5c) By (3.1), |a_k(t)| <= 2 ||H||_S t^(-n/p), which is integrable on (0, R]; by dominated convergence integral_0^rho a_k -> integral_0^rho a_0 and c_k(rho) -> c_0(rho) := integral_0^rho |a_0| for every rho in (0, R]. Define F(rho) := exp(- integral_0^rho a_0(t) dt) for 0 < rho <= R and F(rho) := 1 otherwise. Then F_k(rho) -> F(rho) for rho in (0, R].
 (5d) Proof of (i). For 0 < r <= R put b(r) := (Lambda/4)(r/R)^(1-n/p) in [0, Lambda/4]. Then |log F(r)| <= c_0(r) <= b(r), so e^(-Lambda) <= e^(-b(r)) <= F(r) <= e^(b(r)) <= e^Lambda, and by |e^u - 1| <= e^|u| |u|, |F(r) - 1| <= e^(b(r)) b(r) <= e^(Lambda/4)(Lambda/4)(r/R)^(1-n/p) <= (1/2) e^(Lambda/2) Lambda (r/R)^(1-n/p). If Lambda <= 1, then e^(b(r)) b(r) <= e^(1/4)(Lambda/4)(r/R)^(1-n/p) <= Lambda (r/R)^(1-n/p).
 (5e) Limit of (4.1)-(4.2). Let 0 < sigma <= rho <= R. By (5a), (5c) the left side of (4.1) for epsilon_k tends to F(rho)(1 + rho^(-n) mu(B_rho(y))) - F(sigma)(1 + sigma^(-n) mu(B_sigma(y))) = Phi(rho) - Phi(sigma), where Phi(t) := F(t) t^(-n) mu(B_t(y)) + F(t) - 1. Also A_k(sigma,rho) -> A_0(sigma,rho) := integral_{B_rho(y) minus B_sigma(y)} g_y dmu by dominated convergence: if r(x) <= sigma the integrand is 0 for all k (phi_k(r/rho) = phi_k(r/sigma) = 1); if r(x) > sigma it is at most sigma^(-n) on B_S(y) and converges to r^(-n)(indicator{r <= rho} - indicator{r <= sigma})|D^perp r|^2 = g_y(x) indicator_{B_rho(y) minus B_sigma(y)}(x). Since c_k(rho) -> c_0(rho) <= Lambda/4 and (1 + epsilon_k)^n -> 1, (4.2) passes to the limit:
 e^(-Lambda) A_0(sigma,rho) <= Phi(rho) - Phi(sigma) <= e^(Lambda) A_0(sigma,rho). (5.2)

6. Definition of G and proof of (ii). For 0 < s <= r <= R let G(s,r) := (Phi(r) - Phi(s))/A_0(s,r) if A_0(s,r) != 0, and G(s,r) := 1 otherwise (and G := 1 for all other arguments). If A_0(s,r) > 0, (5.2) gives e^(-Lambda) <= G(s,r) <= e^Lambda and Phi(r) - Phi(s) = G(s,r) A_0(s,r). If A_0(s,r) = 0, (5.2) forces Phi(r) = Phi(s), so the identity holds with G(s,r) = 1, and e^(-Lambda) <= 1 <= e^Lambda as Lambda > 0. Step 0 gives the integrability of g_y on B_r(y) minus B_s(y), so A_0(s,r) is the Bochner integral in the statement, and Phi(t) is exactly F(t) * (mu(B_t(y)).toReal / t^n) + (F(t) - 1) (mu(B_t(y)) < infinity). This proves (ii).

Remark (not used above). For the strengthened SimonGMT varifold structure Chapter04.RectifiableVarifold (tangent field stored as data), the same conclusion is SimonGMT Chapter04.RectifiableVarifold.HasGeneralizedMeanCurvatureIn.exists_lpAnnularCorrection (structure LpAnnularCorrection, with lpMeanCurvatureKappa n p = (p-n)/(4p)); using it here would require a bridge from the contract's RectifiableVarifold (Borel carrier hull, localization of theta to a compact subset of U, and identification of the stored tangent field with V.tangentProj via aal_tangent_structure). The self-contained argument of Steps 0-6 avoids that bridge.

## Key steps

1. Use aal_tangent_structure: p_x is a rank-n orthogonal projection mu-a.e. and measurable; g_y is integrable on annuli.
2. Test the first variation with X = phi_epsilon(|x-y|/rho)(x-y): d/drho(rho^-n I) = rho^-n J' + rho^-n-1 L.
3. Hoelder: |a_epsilon| <= (1+epsilon)||H||_{(1+epsilon)rho} rho^(-n/p) with a_epsilon = rho^-n-1 L/(1+rho^-n I).
4. Integrating factor F_epsilon = exp(-int_0^rho a_epsilon) makes F_epsilon(1+rho^-n I) increasing; Tonelli squeeze of the increment between e^(-c)A_epsilon and e^c(1+epsilon)^n A_epsilon.
5. Let epsilon -> 0 along a nonincreasing sequence: I -> mu(B_t), L -> L_0, a_epsilon -> a_0 dominated; F := exp(-int_0^rho a_0) with int|a_0| <= (Lambda/4)(rho/R)^(1-n/p) since kappa/(1-n/p) = 1/4.
6. Bounds (i) from |log F| <= (Lambda/4)(r/R)^(1-n/p); limit squeeze gives e^-Lambda A_0 <= Phi(r)-Phi(s) <= e^Lambda A_0.
7. Define G as the ratio (or 1 when the annular integral vanishes) to obtain (ii).

## Reference use

### local-project

Queries:
- `timeout 500 rg -n 'aal_|affine_approximation_lemma' <snapshot>/project`
- `grep -n 'lemma measure_compl_support' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `grep -rn 'theorem lintegral_mul_le_Lp_mul_Lq' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/MeanInequalities.lean`
- `grep -n 'theorem mul_meas_ge_le_lintegral₀' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `grep -n 'theorem hausdorffMeasure_homothety_image' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `grep -rn 'theorem finrank_span_eq_card' <snapshot>/mathlib/Mathlib/LinearAlgebra/Dimension/`
- `grep -rn 'theorem volume_ball' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `grep -rn 'theorem.*infDist' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/*.lean`
- `grep -n '^def \|^theorem ' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (CountablyRectifiable, HasWeightedApproximateTangentSpaceAt, .unique)`
- `grep -n 'lpMeanCurvatureKappa|LpAnnularCorrection|exists_lpAnnularCorrection|def radialNormalSq|def HasGeneralizedMeanCurvatureIn' .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/*.lean`
- `grep -rn 'area_image_criticalSet_eq_zero|area_formula_lipschitz_multiplicity|simon_remark_1_3|simon_theorem_1_17|contDiff_whitneyExtension|exists_contDiff_one_extension_of_whitney|simon_theorem_3_6|rademacher_ae_differentiableAt|injective_area_formula_lipschitz_simon' .lake/packages/simongmt/Poincare/SimonGMT`
- `python3 -I: verifier/lean_contract.py validate_lean_statement on all 8 child lean_statements`
- `lake env lean /tmp/claude-1000/aal-check/Check2.lean (Contract lines 1-459 + 8 sorried child types in GMT.Ch05.Submission + sorry-free assembly aal_assembly_check : AffineApproximationLemma)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/MeanInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpMeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpAnnular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaNoninjective.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-02-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-03-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-04-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-05-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/claude-1000/aal-check/Check2.lean`

Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json).

No prior declarations: 'aal_' and 'affine_approximation_lemma' have no matches in the snapshot project, and no DAG node reserves an aal_ name.

Mathlib items located for the children and the assembly (paths under mathlib/Mathlib):
- Measure.measure_compl_support (MeasureTheory/Measure/Support.lean:202): mu-a.e. point lies in spt V.
- lintegral_mul_le_Lp_mul_Lq (MeasureTheory/Integral/MeanInequalities.lean:202): Hoelder.
- mul_meas_ge_le_lintegral₀ (MeasureTheory/Integral/Lebesgue/Markov.lean:52): Chebyshev.
- hausdorffMeasure_homothety_image (MeasureTheory/Measure/Hausdorff.lean:1060): H^n scaling of blow-ups.
- finrank_span_eq_card (LinearAlgebra/Dimension/Constructions.lean:463): used in the Lean assembly to show finrank(horizontalPlane n l) = n.
- EuclideanSpace.volume_ball (MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:307): omega_n.
- Submodule.dist_starProjection_eq_infDist (Analysis/InnerProductSpace/Projection/Basic.lean:234): dist(v,T) = |v - p_T v|.

Pinned SimonGMT (outside the snapshot; paths under .lake/packages/simongmt/Poincare/SimonGMT), what it provides:
- HasWeightedApproximateTangentSpaceAt and .unique (Chapter03/Rectifiable.lean:330, 345).
- simon_remark_1_3 and simon_remark_1_3_nullMeasurable (Chapter03/DisjointCover.lean:90).
- Lusin, simon_theorem_1_17 (Chapter01/Lusin.lean:328).
- Upper density, simon_theorem_3_6 (Chapter01/DensityComparison.lean:332).
- rademacher_ae_differentiableAt (Chapter02/Lipschitz.lean:192).
- exists_contDiff_one_extension_of_whitney (Chapter02/WhitneyExtension.lean:373).
- area_image_criticalSet_eq_zero (Chapter02/AreaCritical.lean:185).
- area_formula_lipschitz_multiplicity (Chapter02/AreaNoninjective.lean:144).
- injective_area_formula_lipschitz_simon (Chapter02/AreaLipschitz.lean:126).

What SimonGMT lacks:
- Only the easy direction of Ch. 3 Lemma 1.2 (Chapter03/SubmanifoldCover.lean).
- No C^1 approximation theorem and no Thm 1.9. So aal_tangent_structure carries the printed proofs, and that child should expect to split further.

Chapter04 monotonicity:
- lpMeanCurvatureKappa = (p-n)/(4p) (LpMeanCurvature.lean:76).
- LpAnnularCorrection and exists_lpAnnularCorrection (LpAnnular.lean:335, 358) match aal_lp_monotonicity field by field, including the larger ball S > R.
- They are stated for the strengthened Chapter04.RectifiableVarifold, so reuse needs a bridge; this is not assumed.

Lean check:
- All 8 child types elaborate in the contract scope and pass validate_lean_statement.
- The assembly aal_assembly_check : AffineApproximationLemma compiles from aal_tilt_height_curvature_bound and aal_height_bound_small_delta. The only warnings are sorry warnings for the placeholder children, plus a push_neg deprecation warning in the scratch assembly.
