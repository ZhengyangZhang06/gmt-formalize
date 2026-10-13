# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_regularity-a1.density_bounds-a1`
- Child DAG node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the parent proof, i.e. the derivation (a)-(d) of the monotonicity facts (M.i)-(M.iii) (Simon, Introduction to GMT, Ch. 4, 4.1-4.9, with the corrected coefficient kappa = (p-n)/(4p) in 4.2; 4.7 is the annular identity), specialized to the present hypotheses: the tangent-plane facts are only used on the open ball B°_R(y), which contains the supports of all test fields. Instead of the parent's compactness extraction in (d), the passage eps -> 0 is done by dominated convergence (which gives convergence of the integrating factors for every radius) and Fatou's lemma (which gives the annular inequality in the direction needed).

Notation. mu := V.weight; B_t := closedBall y t and B°_t := ball y t; r_x := |x - y|; p_x := V.tangentProj x; kappa := (p - n)/(4p); alpha' := 1 - n/p; omega_n := unitBallVolume n; for x != y, nu(x) := |x - y - p_x(x - y)|^2/|x - y|^2, and nu(y) := 0; g(x) := |x - y - p_x(x - y)|^2/|x - y|^(n+2), so g(x) = nu(x) r_x^(-n) for x != y and g(y) = 0 (real division by 0 is 0); m(t) := mu(B_t).toReal. Since 1 <= n < p: p > 0, 0 < n/p < 1, 0 < alpha' < 1, kappa > 0 and 2 kappa/alpha' = 2 (p - n)/(4p) * p/(p - n) = 1/2. Note nu(x) >= 0 for every x.

0. Preliminary facts.
 (a) B_R is compact and contained in U, so mu(B_R) = integral over carrier cap B_R of theta dH^n < infinity (field integrableOn_mult of the structure). Hence mu(B_t) < infinity and mu(B_t) = ofReal(m(t)) for all t <= R.
 (b) HasGeneralizedMeanCurvature H contains LocallyIntegrableOn H U mu; B_R is a compact subset of U, so H is mu-integrable on B_R.
 (c) K := V.scaledLpNorm H p y R = (ofReal(R^(p-n)) * Q)^(1/p) with Q := integral^-_{B_R} |H|^p dmu. Since K <= ofReal(kappa Lambda) < infinity, ofReal(R^(p-n)) > 0 and 1/p > 0, we get Q < infinity, and N := Q^(1/p) (the L^p(mu restricted to B_R) norm of H) satisfies N = R^(n/p - 1) K <= R^(n/p - 1) kappa Lambda.
 (d) By (T1), for mu-a.e. x in B°_R, p_x is the orthogonal projection onto an n-dimensional subspace; at such x, p_x is self-adjoint and idempotent with trace n, v . p_x v = |p_x v|^2 and |v - p_x v|^2 = |v|^2 - |p_x v|^2 <= |v|^2. Hence 0 <= nu(x) <= 1 and (x - y) . p_x(x - y) = r_x^2 (1 - nu(x)) for such x != y.
 (e) By (T2), x -> p_x is a.e.-strongly measurable for mu restricted to B°_R; hence so are nu and g there (continuous operations). Fix a strongly measurable map q : R^(n+l) -> L(R^(n+l)) with q = p mu-a.e. on B°_R. Replacing p_x by q(x) in nu and g changes them only on a mu-null subset of B°_R. Every integrand below that involves nu or g vanishes outside B°_R, so the replacement changes none of the integrals below and makes all of their integrands measurable.

1. Cutoffs. Let psi(u) := 1 for u <= 0, psi(u) := 1 - 3u^2 + 2u^3 for 0 <= u <= 1, psi(u) := 0 for u >= 1. Then psi is C^1 (psi'(u) = 6u(u - 1) on [0, 1], which vanishes at 0 and 1), nonincreasing, with values in [0, 1] and |psi'| <= 3/2. For eps in (0, 1) put phi_eps(u) := psi((u - 1)/eps). Then phi_eps is C^1 and nonincreasing, 0 <= phi_eps <= 1, phi_eps = 1 on (-infinity, 1], phi_eps = 0 on [1 + eps, infinity), phi_eps' <= 0, phi_eps' = 0 outside [1, 1 + eps], |phi_eps'| <= 3/(2 eps), and integral_1^(1+eps) (-phi_eps'(u)) du = phi_eps(1) - phi_eps(1 + eps) = 1. For every u, phi_eps(u) -> 1_{u <= 1} as eps -> 0 (for u > 1, phi_eps(u) = 0 as soon as eps <= u - 1).

2. First variation with radial fields. Fix eps in (0, 1) and put R_eps := R/(1 + eps). For t in (0, R_eps) let X_t(x) := phi_eps(r_x/t)(x - y).
 (a) X_t is C^1 on R^(n+l): on B°_t we have phi_eps(r_x/t) = 1, so X_t(x) = x - y there; on {x != y}, x -> r_x is C^infinity and phi_eps is C^1. The support of X_t lies in the compact ball B_((1+eps)t), which is contained in B°_R, hence in U, because (1 + eps)t < R. So X_t is C^1 with compact support and tsupport X_t is contained in U, and the definition of V.HasGeneralizedMeanCurvature H gives integral divM X_t dmu = - integral X_t . H dmu.
 (b) For x != y and v in R^(n+l): DX_t(x)v = phi_eps(r_x/t) v + t^(-1) phi_eps'(r_x/t) r_x^(-1) ((x - y) . v)(x - y); and DX_t(y) = I. Using trace(c I o p_x) = c trace(p_x) and, for w := x - y, trace(v -> (w . p_x v) w) = w . p_x w, we get at every x in B°_R of 0(d): divM X_t(x) = trace(DX_t(x) o p_x) = n phi_eps(r_x/t) + (r_x/t) phi_eps'(r_x/t)(1 - nu(x)) (at x = y the second term is 0). If x lies outside the closed ball B_((1+eps)t), X_t vanishes on a neighbourhood of x, so divM X_t(x) = 0, and also n phi_eps(r_x/t) + (r_x/t) phi_eps'(r_x/t)(1 - nu(x)) = 0. Hence the displayed formula for divM X_t holds mu-a.e.
 (c) For t in (0, R_eps) put I_eps(t) := integral phi_eps(r_x/t) dmu, J_eps(t) := integral phi_eps(r_x/t) nu(x) dmu, E_eps(t) := integral phi_eps(r_x/t) (x - y) . H(x) dmu. The integrands vanish outside B_((1+eps)t) and are bounded there by 1, 1 (mu-a.e., by 0(d)) and (1 + eps) t |H|, so the three integrals are finite by 0(a), 0(b). For fixed x, t -> phi_eps(r_x/t) is C^1 on (0, infinity) with derivative -phi_eps'(r_x/t) r_x/t^2, which vanishes unless t < r_x <= (1 + eps)t; on a compact interval [t_1, t_2] in (0, R_eps) it is bounded by (3/(2 eps))(1 + eps)/t_1 times the indicator of B_((1+eps)t_2). Differentiation under the integral sign (dominated convergence) shows that I_eps and J_eps are C^1 on (0, R_eps) with
 t I_eps'(t) = - integral (r_x/t) phi_eps'(r_x/t) dmu, t J_eps'(t) = - integral (r_x/t) phi_eps'(r_x/t) nu(x) dmu >= 0,
 and dominated convergence shows that E_eps is continuous on (0, R_eps).
 (d) Integrating the formula of (b) and using (a): n I_eps(t) + integral (r_x/t) phi_eps'(r_x/t) dmu - integral (r_x/t) phi_eps'(r_x/t) nu dmu = -E_eps(t), i.e. n I_eps - t I_eps' + t J_eps' = -E_eps. Dividing by t^(n+1):
 (*) d/dt (t^(-n) I_eps(t)) = t^(-n) J_eps'(t) + t^(-n-1) E_eps(t), 0 < t < R_eps.

3. Hoelder bound. Let t in (0, R_eps). Since phi_eps(r_x/t) = 0 unless r_x <= (1 + eps)t <= 2t, |(x - y) . H| <= r_x |H| and 0 <= phi_eps <= 1, Hoelder's inequality applied to phi_eps^(1/p) |H| and phi_eps^(1 - 1/p) (exponents p and p/(p - 1)) gives
 |E_eps(t)| <= 2t integral phi_eps(r_x/t) |H| dmu <= 2t (integral_{B_R} |H|^p dmu)^(1/p) I_eps(t)^(1 - 1/p) = 2t N I_eps(t)^(1 - 1/p).
 With a := t^(-n) I_eps(t) >= 0 we have t^(-n) I_eps(t)^(1 - 1/p) = t^(-n/p) a^(1 - 1/p) <= t^(-n/p)(1 + a) (a^theta <= 1 + a for a >= 0 and theta in [0, 1]). Using N <= R^(n/p - 1) kappa Lambda and R^(n/p - 1) t^(-n/p) = R^(-1) (t/R)^(-n/p):
 |t^(-n-1) E_eps(t)| <= b(t) (1 + t^(-n) I_eps(t)), where b(t) := 2 kappa Lambda R^(-1) (t/R)^(-n/p).
 Hence a_eps(t) := t^(-n-1) E_eps(t)/(1 + t^(-n) I_eps(t)) is continuous on (0, R_eps) and |a_eps(t)| <= b(t) there.

4. Integrating factor. For t > 0, integral_0^t b(tau) dtau = 2 kappa Lambda R^(-1) R (t/R)^(alpha')/alpha' = (Lambda/2)(t/R)^(alpha') <= Lambda/2 for t <= R. So a_eps is integrable on (0, t] for t < R_eps. For t in (0, R_eps) define F_eps(t) := exp(- integral_0^t a_eps(tau) dtau), Psi_eps(t) := 1 + t^(-n) I_eps(t) and Phi_eps(t) := F_eps(t) Psi_eps(t) - 1 = F_eps(t) t^(-n) I_eps(t) + F_eps(t) - 1. By the fundamental theorem of calculus (a_eps continuous), F_eps is C^1 with F_eps' = -a_eps F_eps, and (*) reads Psi_eps' = t^(-n) J_eps' + a_eps Psi_eps. Hence Phi_eps' = -a_eps F_eps Psi_eps + F_eps (t^(-n) J_eps' + a_eps Psi_eps) = F_eps(t) t^(-n) J_eps'(t), a continuous nonnegative function; and F_eps(t) >= e^(-Lambda/2). Therefore, for 0 < s <= r < R_eps,
 (**) Phi_eps(r) - Phi_eps(s) = integral_s^r F_eps(t) t^(-n) J_eps'(t) dt >= e^(-Lambda/2) integral_s^r t^(-n) J_eps'(t) dt >= 0.

5. Passage eps -> 0; definition of F. For t in (0, R) put E(t) := integral_{B_t} (x - y) . H dmu and a(t) := t^(-n-1) E(t)/(1 + t^(-n) m(t)). Fix t in (0, R) and eps_0 in (0, 1) with (1 + eps_0) t < R. For eps <= eps_0 the integrands of I_eps(t) and E_eps(t) are dominated by the indicator of B_((1+eps_0)t) and by (1 + eps_0) t |H| times it (integrable by 0(a), 0(b)), and they converge pointwise to 1_{B_t}(x) and 1_{B_t}(x) (x - y) . H(x) (step 1). By dominated convergence I_eps(t) -> m(t) and E_eps(t) -> E(t); hence a_eps(t) -> a(t), and |a(t)| <= b(t) by step 3. Fix a sequence eps_k -> 0 in (0, 1). For t in (0, R): for k large, (0, t] is contained in (0, R_(eps_k)); a_(eps_k) -> a pointwise on (0, t], |a_(eps_k)| <= b with integral_0^t b < infinity, so by dominated convergence integral_0^t a_(eps_k) -> integral_0^t a. Define F(t) := exp(- integral_0^t a(tau) dtau) for t in (0, R) and F(t) := 1 for t not in (0, R). Then F_(eps_k)(t) -> F(t) and Phi_(eps_k)(t) -> Phi(t) = F(t) (t^n)^(-1) m(t) + F(t) - 1 for every t in (0, R); this Phi is the function of the statement.

6. Conclusion (i). For t in (0, R): |integral_0^t a| <= integral_0^t b = (Lambda/2)(t/R)^(alpha') <= Lambda/2. Hence e^(-Lambda) <= e^(-Lambda/2) <= F(t) <= e^(Lambda/2) <= e^Lambda, and by |e^z - 1| <= e^|z| |z|: |F(t) - 1| <= e^(Lambda/2)(Lambda/2)(t/R)^(alpha') <= Lambda (t/R)^(alpha'), since Lambda <= 1 and e^(1/2)/2 < 1.

7. Conclusion (ii), monotonicity. Let 0 < s <= r < R. For k large, r < R_(eps_k), and (**) gives Phi_(eps_k)(s) <= Phi_(eps_k)(r). Letting k -> infinity (step 5), Phi(s) <= Phi(r).

8. Conclusion (ii), annular bound. Let 0 < s <= r < R. If s = r the annulus B_r minus B_s is empty, its integral is 0 and the claim holds. Let s < r and k large so that r < R_(eps_k). The function (t, x) -> t^(-n) (r_x/t^2)(-phi_eps'(r_x/t)) nu(x) (with the measurable version of p from 0(e)) is nonnegative and measurable on [s, r] x B°_R, continuous in t and measurable in x, and it vanishes for x outside B_((1+eps)r), which lies in B°_R. Apply Tonelli's theorem to Lebesgue measure on [s, r] and the finite measure mu restricted to B°_R; together with 2(c) this gives
 integral_s^r t^(-n) J_eps'(t) dt = integral nu(x) h_eps(r_x) dmu(x), where h_eps(c) := integral_s^r t^(-n)(c/t^2)(-phi_eps'(c/t)) dt >= 0 for c > 0, and h_eps(0) := 0.
 For c in (s, r] and eps <= c/s - 1, the substitution u = c/t (dt = -(c/u^2) du) gives h_eps(c) = integral_(c/r)^(c/s) (u/c)^n (-phi_eps'(u)) du >= c^(-n) integral_1^(1+eps) (-phi_eps'(u)) du = c^(-n), because [1, 1 + eps] is contained in [c/r, c/s], -phi_eps' >= 0 and (u/c)^n >= c^(-n) for u >= 1. Consequently, for every x, liminf_k ofReal(nu(x) h_(eps_k)(r_x)) >= ofReal(nu(x) r_x^(-n)) 1_{s < r_x <= r} = ofReal(g(x)) 1_{B_r minus B_s}(x). By Fatou's lemma for [0, infinity]-valued functions and (**):
 integral^-_{B_r minus B_s} ofReal(g) dmu <= liminf_k integral^- ofReal(nu h_(eps_k)(r_x)) dmu = liminf_k integral_s^r t^(-n) J_(eps_k)'(t) dt <= e^(Lambda/2) liminf_k (Phi_(eps_k)(r) - Phi_(eps_k)(s)) = e^(Lambda/2) (Phi(r) - Phi(s)) <= e^Lambda (Phi(r) - Phi(s)),
 where all quantities after the first are finite reals and Phi(r) - Phi(s) >= 0 by step 7. Thus integral^-_{B_r minus B_s} ofReal(g) dmu <= ofReal(e^Lambda (Phi(r) - Phi(s))). Since g(x) = |x - y - p_x(x - y)|^2/|x - y|^(n+2), this is the annular bound of (ii).

9. Conclusion (iii). By step 7, Phi is nondecreasing on (0, R), and Phi(t) >= F(t) - 1 >= -Lambda because m(t) >= 0 and F(t) > 0. Hence L := lim_(t -> 0+) Phi(t) = inf over (0, R) of Phi exists in R, and L <= Phi(r) for every r in (0, R). By step 6, F(t) -> 1 as t -> 0+ (because (t/R)^(alpha') -> 0), so t^(-n) m(t) = (Phi(t) + 1)/F(t) - 1 -> L; as t^(-n) m(t) >= 0, L >= 0. omega_n = pi^(n/2)/Gamma(n/2 + 1) > 0; put t_* := L/omega_n >= 0. For t in (0, R), mu(B_t) is finite and omega_n t^n > 0, so mu(B_t)/ofReal(omega_n t^n) = ofReal(t^(-n) m(t)/omega_n), which tends to ofReal(L/omega_n) = ofReal(t_*) by continuity of ofReal; that is, V.HasDensity y t_*. Finally omega_n t_* = L <= Phi(r) for every r in (0, R). This is (iii) with t := t_*, and together with steps 6-8 proves the statement with the F of step 5.

Implementation note (non-normative). The accepted declaration dohr_local_monotonicity (candidate commit 4c0fc30d6a1cd4ba43b449f2e51583e4e473c461, GMT/Ch05/Submission.lean, a single theorem whose proof consists of local lemmas) has the same hypotheses on (V, H, y, R, Lambda), apart from the conclusion. Its proof contains Lean versions of:
- the radial first variation, as an inequality that discards the nu-term;
- the Hoelder bound on the curvature term;
- the integrating-factor monotonicity for one cutoff;
- the cutoff limit;
- the density limit.
These can be adapted. Three ingredients are new here:
- keeping the nu-term, so that the identity of step 2(d) holds with J_eps;
- the decay bound |F - 1| <= Lambda (t/R)^(alpha') of step 6;
- the Tonelli/Fatou annular estimate of step 8.
In addition, cutoffs equal to 1 on (-infinity, 1] give closed balls directly in the limit.

## Key steps

1. Finiteness of mu(B_R), integrability of H on B_R, ||H||_{L^p(B_R)} <= R^(n/p-1) kappa Lambda, and 0 <= nu <= 1 a.e. on B°_R from (T1)
2. Radial C^1 test fields phi_eps(r/t)(x - y) supported in B_((1+eps)t), inside B°_R and U, give n I - t I' + t J' = -E, i.e. d/dt(t^-n I) = t^-n J' + t^(-n-1) E
3. Hoelder: |t^(-n-1) E| <= b(t)(1 + t^-n I) with b(t) = 2 kappa Lambda R^-1 (t/R)^(-n/p) and integral_0^t b = (Lambda/2)(t/R)^(alpha')
4. Integrating factor F_eps = exp(-integral_0^t a_eps) gives (Phi_eps)' = F_eps t^-n J_eps' >= 0
5. Dominated convergence as eps -> 0 gives F_eps -> F and Phi_eps -> Phi pointwise, with e^-Lambda <= F <= e^Lambda and |F - 1| <= Lambda (t/R)^(alpha')
6. Monotonicity of Phi in the limit; Fatou plus the substitution u = c/t give the annular lower integral bound with factor e^Lambda
7. Monotone Phi bounded below and F -> 1 give the density t >= 0 with omega_n t = inf Phi <= Phi(r)

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp <snapshot>/project/GMT/Ch05/Submission.lean GMT/Ch05/Submission.lean; cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean`
- `rg -c -t lean 'allard52_density_constants|allard52_annular_monotonicity|allard52_support_density_ge_one|allard52_center_density_bounds|aal_allard_subball_bounds' <snapshot>/project <snapshot>/mathlib/Mathlib`
- `for pat in Allard Varifold monotonicity_formula tangentProj; do rg -l -t lean $pat <snapshot>/mathlib/Mathlib | wc -l; done`
- `rg -n (theorem setLIntegral_iUnion_of_directed | theorem lintegral_union_le | theorem lintegral_liminf_le' | theorem tendsto_measure_biInter_gt | lemma mem_support_iff_forall | theorem LocallyIntegrableOn.integrableOn_compact_subset | theorem lintegral_lintegral_swap | theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le | theorem norm_image_sub_le_of_norm_deriv_le | theorem integral_hasDerivAt_right) MeasureTheory Analysis/Calculus/ParametricIntegral.lean Analysis/Calculus/MeanValue.lean, run in <snapshot>/mathlib/Mathlib`
- `rg -n (monoton|κ|kappa|2.4|density) <snapshot>/project/GMT/Ch05/README.md; sed -n 25,45p <snapshot>/project/GMT/Ch05/README.md`
- `grep -n (def lpMeanCurvatureKappa|structure LpAnnularCorrection|theorem HasGeneralizedMeanCurvatureIn.exists_lpAnnularCorrection) -A3 .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpMeanCurvature.lean .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpAnnular.lean`
- `python3 over dag.json: lean_name, lean_statement, status, parent and candidate_commit for the five proposed names, allard52_tangent_ae, allard52_density_bounds and every accepted node`
- `git show 595bf34cad5e797b1ca2c89a3d419f3daecdab75:GMT/Ch05/Submission.lean; git show 9f4dca65df4fbd188bea65e81c59d598279e6643:GMT/Ch05/Submission.lean | grep -n 'theorem allard52_tangent_ae'; git show 4c0fc30d6a1cd4ba43b449f2e51583e4e473c461:GMT/Ch05/Submission.lean | grep -n 'theorem dohr_local_monotonicity'`
- `toolchains/lean-4.35.0-rc3-linux/bin/lean GMT/Ch05/Submission.lean -o /tmp/db3-build/lib/GMT/Ch05/Submission.olean (LEAN_PATH = /tmp/db3-build/lib plus lake-packages-25730c7c/*/.lake/build/lib/lean)`
- `LEAN_PATH=<same> lean /tmp/db3-check/Types.lean; lean /tmp/db3-check/Assembly.lean; lean /tmp/db3-check/Appx_density_constants.lean; lean /tmp/db3-check/Appx_center_density_bounds.lean; lean /tmp/db3-check/Appx_support_density_ge_one.lean; lean /tmp/db3-check/Subball.lean`
- `python3 field-by-field comparison of the proposed subproblems with nodes/root-allard-regularity-a1-density-bounds-a1/decomposition-v2.json`
- `grep max_nodes .humanize/swarm-configs/675fa2adfe3d43c39028ca3e3199bdce.json; read _existing_lean_name_problem, _accepted_checkpoint, _install_parent_supplied_child_handoff and the node-bound check of /runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/runtime.py, and ensure in store.py`
- `sed -n 270,315p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt (Simon Ch. 5, 2.3, 2.4 and inequality (1) in the proof of 2.5)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpMeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpAnnular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/swarm-configs/675fa2adfe3d43c39028ca3e3199bdce.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/tmp/db3-check/Types.lean`
- `/tmp/db3-check/Assembly.lean`
- `/tmp/db3-check/Appx_density_constants.lean`
- `/tmp/db3-check/Appx_center_density_bounds.lean`
- `/tmp/db3-check/Appx_support_density_ge_one.lean`
- `/tmp/db3-check/Subball.lean`

Pins: project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json). The workspace Contract.lean and Submission.lean are byte-identical to the snapshot copies.

Names.
- The five proposed names have no match in the snapshot project or Mathlib (rg exit status 1).
- In dag.json (200 nodes) the four new names occur nowhere.
- aal_allard_subball_bounds is the accepted node root.affine_approximation-a1.pinched_density_bounds-a1.allard_subball_bounds-a1 (candidate 595bf34c). Its frozen lean_statement is byte-identical to the proposed one, so runtime reuse is permitted.
- allard52_tangent_ae is accepted (candidate 9f4dca65, theorem at line 816) with the type used by the assembly.

Mathlib.
- The topics Allard, Varifold, monotonicity_formula and tangentProj have 0 hits, so the annular monotonicity is new.
- Lemmas used by the child proofs exist: setLIntegral_iUnion_of_directed (Lebesgue/Basic.lean:668), lintegral_union_le (Basic.lean:632), lintegral_liminf_le' (Lebesgue/Add.lean:216), tendsto_measure_biInter_gt (Measure/Continuity.lean:266), mem_support_iff_forall (Measure/Support.lean:75), LocallyIntegrableOn.integrableOn_compact_subset (LocallyIntegrable.lean:122), lintegral_lintegral_swap (Measure/Prod.lean:1071), integral_hasDerivAt_right (FundThmCalculus.lean:725), hasDerivAt_integral_of_dominated_loc_of_deriv_le (ParametricIntegral.lean:286) and norm_image_sub_le_of_norm_deriv_le (MeanValue.lean:727).

SimonGMT.
- lpMeanCurvatureKappa n p = (p - n) / (4 * p) (LpMeanCurvature.lean:76) confirms the corrected kappa.
- LpAnnularCorrection and exists_lpAnnularCorrection (LpAnnular.lean:335, 358) are proved for the library varifold with stored tangent data. The chapter README (lines 33-38) says this needs a bridge, so annular_monotonicity re-derives the result for the contract varifold.
- The accepted dohr_local_monotonicity (4c0fc30d, line 465) has the same hypotheses but no conical term and no decay rate.

Lean checks (Lean v4.35.0-rc3).
- Types.lean: every proposed type, the tangent sibling type and the frozen parent type elaborate with only sorry warnings.
- Assembly.lean proves the exact frozen parent type from the five children and allard52_tangent_ae. #print axioms lists exactly propext, Classical.choice, Quot.sound and those six declarations.
- Appendices: density_constants and center_density_bounds use standard axioms only; support_density_ge_one uses standard axioms plus aal_allard_subball_bounds and allard52_annular_monotonicity.
- The accepted subball body recompiles with standard axioms only.
- No matrix or inline-instance constructions occur; V.weight is passed directly as the abstract measure of center_density_bounds and elaborates.

Runtime. The current config has max_nodes = 1000 against 200 existing nodes, so the 4 new nodes fit. Reused accepted nodes skip handoff installation, and ensure returns existing nodes unchanged.

Source. Simon's 2.4 and the proof of 2.5 (1) confirm the pinched density and conical-integral bounds that are formalized here with explicit constants.
