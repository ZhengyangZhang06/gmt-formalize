# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1`
- Child DAG node: `root.tilt_excess_decay-a1.lp_monotonicity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 4, 3.2-3.5 and 4.1-4.8 (radial first variation with the epsilon-cutoff, Hoelder bound, integrating factor, epsilon -> 0). The coefficient in front of Lambda in 4.2 is taken to be kappa = (p-n)/(4p), the value for which the integration after 4.4 yields the bounds 4.5-4.6; this constant agrees with lpMeanCurvatureKappa of the SimonGMT Chapter04 files, but no Chapter04 result is used. Only the monotonicity consequence 4.8 is proved, i.e. the inequality Phi(s) <= Phi(r); for it only the sign of the J-term of 3.4 is needed. This argument is carried out directly for the contract varifold and uses no Chapter04 library structure.

Notation. mu := V.weight; p_x := V.tangentProj x; B_t(y) := closedBall y t (closed ball); r(x) := |x - y| and nu(x) := (x - y)/r(x) for x != y. kappa := (p - n)/(4p) > 0 and alpha := 1 - n/p in (0,1), so kappa/alpha = 1/4. For 0 < t <= S put ||H||_t := (integral^-_{B_t(y)} |H|^p dmu)^{1/p}, where integral^- is the lower (lintegral) integral of the extended function |H|^p. This is finite because t <= S and the hypothesis bounds the integral over B_S(y), and it is nondecreasing in t. K(y,R) := V.scaledLpNorm H p y R = (ofReal(R^{p-n}) integral^-_{B_R(y)} |H|^p dmu)^{1/p} = R^alpha ||H||_R, since ofReal(R^{p-n})^{1/p} = ofReal(R^alpha). The hypothesis K(y,R) <= ofReal(kappa Lambda) therefore gives ||H||_R <= kappa Lambda R^{-alpha}.

0. Preliminaries.
(a) By ted_tangent_plane_facts, conclusions (1) and (2) (applicable since n >= 1 and U is open): for mu-a.e. x, p_x = P.starProjection for an n-dimensional subspace P. Hence p_x is self-adjoint and idempotent, trace p_x = n and |p_x v| <= |v|. Moreover x |-> p_x is mu-a.e. strongly measurable.
(b) B_S(y) is a compact subset of U, so mu(B_S(y)) < infinity (V.integrableOn_mult). H is mu-integrable on B_S(y): the first conjunct of V.HasGeneralizedMeanCurvature H makes H locally integrable on U, hence integrable on compact subsets of U.
(c) Hoelder. Let g be mu-measurable with 0 <= g <= 1 and g = 0 outside B_t(y) for some t <= S. Then integral g |H| dmu <= ||H||_t (integral g dmu)^{1-1/p}. This is Hoelder with exponents p and p/(p-1) (note p > n >= 1, so p > 1), using g^{p/(p-1)} <= g.
(d) Elementary: a^{1-1/p} <= 1 + a for a >= 0, and |e^u - 1| <= |u| e^{|u|} for real u.

1. Cutoffs. Let chi(t) := 1 for t <= 0, chi(t) := 1 - 3t^2 + 2t^3 for 0 <= t <= 1, and chi(t) := 0 for t >= 1. chi is C^1 and nonincreasing with 0 <= chi <= 1; chi'(t) = -6t(1-t) on [0,1], chi' = 0 outside (0,1), and |chi'| <= 3/2.
For eps in (0,1] let phi_eps(t) := chi((t - 1)/eps). Then phi_eps is C^1 and nonincreasing, 0 <= phi_eps <= 1, phi_eps = 1 on (-infinity,1], phi_eps = 0 on [1+eps, infinity), phi_eps' <= 0, phi_eps' = 0 on (-infinity,1], and |phi_eps'| <= 3/(2 eps). For each t, phi_eps(t) tends to the indicator of (-infinity,1] at t as eps -> 0+ (if t > 1, phi_eps(t) = 0 as soon as eps < t - 1).

2. Radial first variation (Simon 3.2-3.4, 4.1). Fix eps in (0,1] and put T_eps := S/(1 + eps). For rho in (0, T_eps) let X_rho(x) := phi_eps(r(x)/rho)(x - y).
(a) X_rho is C^1. On the open set {r < rho} it equals x - y, because phi_eps = 1 on (-infinity,1]. On the open set {x != y} it is built from C^1 maps by composition and products. X_rho vanishes outside B_{(1+eps) rho}(y), so it has compact support and tsupport X_rho ⊆ B_{(1+eps) rho}(y) ⊆ B_S(y) ⊆ U (as (1+eps) rho < S). Hence X_rho is an admissible field in V.HasGeneralizedMeanCurvature H.
(b) For x != y, D X_rho(x) v = phi_eps(r/rho) v + rho^{-1} phi_eps'(r/rho) (nu . v)(x - y), and D X_rho(x) = I where r < rho. Let x be a point where p_x is a rank-n orthogonal projection (mu-a.e. x, by 0(a)). The map v |-> (nu . p_x v) w has trace (p_x nu) . w, and (p_x nu) . (x - y) = r |p_x nu|^2. Hence
 div_M X_rho(x) = trace(D X_rho(x) o p_x) = n phi_eps(r/rho) + (r/rho) phi_eps'(r/rho) |p_x nu|^2.
The second term is 0 where r <= rho, in particular at x = y. Since phi_eps' <= 0 and 0 <= |p_x nu|^2 <= 1,
 div_M X_rho(x) >= n phi_eps(r/rho) + (r/rho) phi_eps'(r/rho) for mu-a.e. x. (2.1)
(c) Integrability. div_M X_rho is mu-a.e. strongly measurable, by 0(a) and continuity of D X_rho. It is bounded by n + (1+eps) 3/(2 eps) and vanishes outside B_S(y). Also X_rho . H is integrable, since |X_rho| <= S and H is integrable on B_S(y). The first-variation identity gives
 integral div_M X_rho dmu = - L(rho), where L(rho) := integral phi_eps(r/rho)(x - y) . H dmu.
(d) Let I(rho) := integral phi_eps(r/rho) dmu. For fixed x, rho |-> phi_eps(r(x)/rho) is C^1 on (0, infinity) with derivative -(r/rho^2) phi_eps'(r/rho). This derivative vanishes unless rho <= r <= (1+eps) rho, and is then bounded by (1+eps) rho^{-1} 3/(2 eps). For rho in a compact interval [a, b] of (0, T_eps) the derivatives are therefore bounded by 3/(a eps) and vanish outside B_S(y), which has finite measure. Differentiation under the integral sign shows that I is differentiable on (0, T_eps) with I'(rho) = - integral (r/rho^2) phi_eps'(r/rho) dmu, so integral (r/rho) phi_eps'(r/rho) dmu = - rho I'(rho). L is continuous on (0, T_eps) by dominated convergence: the integrand is continuous in rho and dominated by S |H| on B_S(y).
(e) Integrating (2.1) and using (c) and (d) gives -L(rho) >= n I(rho) - rho I'(rho). Hence, for rho in (0, T_eps),
 d/drho (rho^{-n} I(rho)) = rho^{-n-1}(rho I'(rho) - n I(rho)) >= rho^{-n-1} L(rho). (2.2)

3. Hoelder bound (Simon 4.2-4.3). Since phi_eps(r/rho) = 0 for r >= (1+eps) rho, we have |(x - y) . H| phi_eps(r/rho) <= (1+eps) rho |H| phi_eps(r/rho). By 0(c) with g = phi_eps(r/rho) and t = (1+eps) rho,
 |L(rho)| <= (1+eps) rho ||H||_{(1+eps) rho} I(rho)^{1-1/p}.
Hence, by 0(d),
 |rho^{-n-1} L(rho)| <= (1+eps) ||H||_{(1+eps) rho} rho^{-n/p} (rho^{-n} I(rho))^{1-1/p} <= (1+eps) ||H||_{(1+eps) rho} rho^{-n/p} (1 + rho^{-n} I(rho)).
Define a_eps(rho) := rho^{-n-1} L(rho)/(1 + rho^{-n} I(rho)) for rho in (0, T_eps). It is continuous and satisfies
 |a_eps(rho)| <= (1+eps) ||H||_{(1+eps) rho} rho^{-n/p} <= 2 ||H||_S rho^{-n/p}. (3.1)
Since n/p < 1, rho^{-n/p} is integrable on (0, b] for every b > 0.

4. Integrating factor (Simon 4.4). For rho in (0, T_eps) put F_eps(rho) := exp(- integral_0^rho a_eps(t) dt), which is finite by (3.1), and Psi_eps(rho) := F_eps(rho)(1 + rho^{-n} I(rho)). By the fundamental theorem of calculus (a_eps is continuous), F_eps is differentiable with F_eps' = - a_eps F_eps. By (2.2),
 Psi_eps'(rho) = F_eps(rho) [d/drho(rho^{-n} I(rho)) - a_eps(rho)(1 + rho^{-n} I(rho))] = F_eps(rho) [d/drho(rho^{-n} I(rho)) - rho^{-n-1} L(rho)] >= 0.
By the mean value theorem, Psi_eps is nondecreasing on (0, T_eps). (4.1)

5. Letting eps -> 0 (Simon 3.5-3.6, 4.5-4.7). Choose eps_1 in (0,1] with (1 + eps_1) R < S and put eps_k := eps_1/k. Then R < T_{eps_k} for every k. Write I_k, L_k, a_k, F_k, Psi_k for the objects of Steps 2-4 with eps = eps_k; all are defined on (0, R].
(a) Let t in (0, R]. Then I_k(t) -> mu(B_t(y)) and L_k(t) -> L_0(t) := integral_{B_t(y)} (x - y) . H dmu, by dominated convergence. Indeed phi_{eps_k}(r/t) -> indicator{r <= t} pointwise, and the integrands vanish outside B_{(1+eps_1) R}(y) ⊆ B_S(y), where they are dominated by 1 and S |H| respectively. Hence a_k(t) -> a_0(t) := t^{-n-1} L_0(t)/(1 + t^{-n} mu(B_t(y))). As a pointwise limit of continuous functions, a_0 is measurable on (0, R].
(b) By 0(c) with g the indicator of B_t(y), |L_0(t)| <= t ||H||_t mu(B_t(y))^{1-1/p}. As in Step 3, for 0 < t <= R,
 |a_0(t)| <= ||H||_t t^{-n/p} <= ||H||_R t^{-n/p} <= kappa Lambda R^{-1} (t/R)^{-n/p},
using ||H||_R <= kappa Lambda R^{-alpha} = kappa Lambda R^{-1} R^{n/p}. Integrating, with kappa/alpha = 1/4:
 integral_0^rho |a_0(t)| dt <= kappa Lambda R^{-1} integral_0^rho (t/R)^{-n/p} dt = (kappa/alpha) Lambda (rho/R)^alpha = (Lambda/4)(rho/R)^alpha, 0 < rho <= R. (5.1)
(c) By (3.1), |a_k(t)| <= 2 ||H||_S t^{-n/p} on (0, R]. By dominated convergence, integral_0^rho a_k -> integral_0^rho a_0 for each rho in (0, R]. Define F(rho) := exp(- integral_0^rho a_0(t) dt) for 0 < rho <= R, and F(rho) := 1 for all other real rho. Then F_k(rho) -> F(rho) for rho in (0, R].
(d) Conclusion (i). Let 0 < r <= R and b := (Lambda/4)(r/R)^alpha, so b is in (0, Lambda/4]. By (5.1), |log F(r)| <= b, so e^{-Lambda} <= e^{-b} <= F(r) <= e^b <= e^Lambda. By 0(d),
 |F(r) - 1| <= b e^b <= (1/4) e^{Lambda/4} Lambda (r/R)^alpha <= (1/2) e^{Lambda/2} Lambda (r/R)^alpha.
If Lambda <= 1, then b e^b <= (e^{1/4}/4) Lambda (r/R)^alpha <= Lambda (r/R)^alpha.
(e) Conclusion (ii). Let 0 < s <= r <= R. By (4.1), Psi_k(s) <= Psi_k(r) for every k, and by (a) and (c), Psi_k(t) -> F(t)(1 + t^{-n} mu(B_t(y))) for t in {s, r}. Hence F(s)(1 + s^{-n} mu(B_s(y))) <= F(r)(1 + r^{-n} mu(B_r(y))). This is Phi(s) <= Phi(r) with Phi(t) = F(t) t^{-n} mu(B_t(y)) + F(t) - 1. Since mu(B_t(y)) <= mu(B_S(y)) < infinity, the number t^{-n} mu(B_t(y)) is (V.weight (closedBall y t)).toReal / t^n, as in the statement.

## Key steps

1. ted_tangent_plane_facts (1),(2): p_x is mu-a.e. a rank-n orthogonal projection and mu-measurable; H is integrable and mu finite on B_S(y)
2. First variation with X = phi_eps(|x-y|/rho)(x-y): since phi_eps' <= 0 and |p_x nu| <= 1, d/drho(rho^-n I) >= rho^(-n-1) L
3. Hoelder: |rho^(-n-1) L| <= (1+eps)||H||_{(1+eps)rho} rho^(-n/p)(1 + rho^-n I); a_eps := rho^(-n-1) L/(1 + rho^-n I)
4. Integrating factor F_eps = exp(-int_0^rho a_eps) makes F_eps(1 + rho^-n I) nondecreasing
5. eps -> 0 along eps_k: I_k -> mu(B_t), L_k -> L_0, a_k -> a_0 (dominated by 2||H||_S t^(-n/p)); F := exp(-int_0^rho a_0) with int|a_0| <= (Lambda/4)(rho/R)^alpha since kappa/alpha = 1/4
6. Bounds (i) from |log F(r)| <= (Lambda/4)(r/R)^alpha; monotonicity (ii) is the limit of the monotonicity of F_eps(1 + rho^-n I)

## Reference use

### local-project

Queries:
- `rg -n 'ted_lp_monotonicity|ted_density_ge_one|ted_allard_density_bounds' <snapshot> (no match)`
- `grep -rhoE '"lean_name": *"[^"]*"' <run>/nodes <run>/dag.json | sort | uniq -c`
- `rg -n 'theorem LocallyIntegrableOn.integrableOn_compact_subset|theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le|theorem monotoneOn_of_deriv_nonneg|theorem lintegral_mul_le_Lp_mul_Lq|theorem le_toOuterMeasure_caratheodory|theorem tendsto_measure_biInter_gt|theorem withDensity_apply|euclideanHausdorffMeasure_def' <snapshot>/mathlib/Mathlib`
- `rg -n 'exists_measurable_subset_ae_eq' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean; rg -n 'measure_compl_support' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `rg -l -i 'varifold|monotonicity formula' <snapshot>/mathlib/Mathlib (no match)`
- `rg -n 'theorem simon_theorem_3_6|def dimensionalUpperDensity|def simonHausdorffMeasureReal|theorem simonHausdorffMeasureReal_toOuterMeasure|theorem measure_toOuterMeasure_isBorelRegular|def IsBorelRegularOuterMeasure|def HasWeightedApproximateTangentSpaceAt|def blowUpMap' .lake/packages/simongmt/Poincare/SimonGMT`
- `rg -c sorry .lake/packages/simongmt/Poincare/SimonGMT/Chapter01/{DensityComparison,Hausdorff,Basic}.lean (no match)`
- `sed -n 215,600p book/chapter-04.txt; sed -n 590,735p book/chapter-01.txt`
- `lean /tmp/ted-decomp-v2/checks/Types.lean; lean /tmp/ted-decomp-v2/checks/Props.lean; lean /tmp/ted-decomp-v2/checks/PrintNew.lean`
- `lean /tmp/ted-decomp-v2/checks/Assembly.lean (#print axioms parent_check)`
- `lean /tmp/ted-decomp-v2/checks/Wiring.lean (#print axioms wiring_lp_hyps)`
- `lean /tmp/ted-decomp-v2/checks/WiringUD.lean (#print axioms wiring_upper_density)`
- `python3 -I /tmp/ted-decomp-v2/scripts/numcheck.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Deriv/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/MeanInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/OuterMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-lp-monotonicity-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-density-ge-one-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-pinched-density-bounds-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/tmp/ted-decomp-v2/checks/Types.lean`
- `/tmp/ted-decomp-v2/checks/Props.lean`
- `/tmp/ted-decomp-v2/checks/PrintNew.lean`
- `/tmp/ted-decomp-v2/checks/Assembly.lean`
- `/tmp/ted-decomp-v2/checks/Wiring.lean`
- `/tmp/ted-decomp-v2/checks/WiringUD.lean`
- `/tmp/ted-decomp-v2/scripts/numcheck.py`

Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json). Its Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

No prior declarations: ted_lp_monotonicity, ted_density_ge_one and ted_allard_density_bounds have no match in the snapshot, in dag.json or in any other node's files.

No-match search: Mathlib has no varifold or monotonicity-formula results ('varifold|monotonicity formula' matches no file). The monotonicity is therefore proved in the child ted_lp_monotonicity directly from the contract's first-variation identity.

Mathlib items located for the new proofs (paths under mathlib/Mathlib):
- LocallyIntegrableOn.integrableOn_compact_subset (MeasureTheory/Function/LocallyIntegrable.lean:122).
- hasDerivAt_integral_of_dominated_loc_of_deriv_le (Analysis/Calculus/ParametricIntegral.lean:286).
- monotoneOn_of_deriv_nonneg (Analysis/Calculus/Deriv/MeanValue.lean:411).
- Hoelder, lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top (MeasureTheory/Integral/MeanInequalities.lean:147).
- NullMeasurableSet.exists_measurable_subset_ae_eq (MeasureTheory/Measure/NullMeasurable.lean:214).
- measure_compl_support (MeasureTheory/Measure/Support.lean:202).
- le_toOuterMeasure_caratheodory (MeasureTheory/Measure/OuterMeasure.lean:37).
- tendsto_measure_biInter_gt (MeasureTheory/Measure/Continuity.lean:266).
- withDensity_apply (MeasureTheory/Measure/WithDensity.lean:44).
- euclideanHausdorffMeasure_def (Geometry/Euclidean/Volume/Measure.lean:74): μHE[d] is a scalar multiple of μH[d].

The pinned simongmt package lies outside the snapshot; 'rg -c sorry' finds no match in the Chapter01 files used. It provides:
- simon_theorem_3_6 (Chapter01/DensityComparison.lean:332).
- measure_toOuterMeasure_isBorelRegular (Chapter01/Basic.lean:309).
- simonHausdorffMeasureReal = (omega_m/2^m) • μH[m] (Chapter01/Hausdorff.lean:283), with simonHausdorffMeasureReal_toOuterMeasure (:445).
- HasWeightedApproximateTangentSpaceAt and blowUpMap (Chapter03/Rectifiable.lean:330, 96), used by translate_varifold.
No Chapter04 declaration is used anywhere in v2.

The proofs of aal_lp_monotonicity, aal_density_ge_one and aal_pinched_density_bounds in the affine-approximation branch were consulted; these were reviewed as natural proofs, but the declarations are not accepted. The v2 children re-derive the needed arguments under ted_ names, with lp_monotonicity in a weaker, inequality-only form.

Lean checks:
- All nine child types elaborate in the contract scope.
- The sorry-free assembly proves TiltExcessDecayTheorem from translate_varifold, allard_density_bounds, decay_at_origin and the four sibling Props, using only propext, Classical.choice and Quot.sound.
- The sorry-free wiring lemmas for both monotonicity call sites, and for applying the Upper Density Theorem to V.weight with the μHE[n] normalization, use only the same three axioms.
