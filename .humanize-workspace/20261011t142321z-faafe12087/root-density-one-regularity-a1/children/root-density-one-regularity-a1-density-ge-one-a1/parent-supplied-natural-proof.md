# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_regularity-a1`
- Child DAG node: `root.density_one_regularity-a1.density_ge_one-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 4, the monotonicity identity 3.1-3.5 (derivation with radial fields), Section 4 (4.1-4.9: L^p mean curvature, kappa = (p-n)/(4p) in 4.2, integrating factor, existence and upper semicontinuity of Theta), the upper semicontinuity argument 3.11, and Remark 4.10(1) (Theta >= 1 on spt V when theta >= 1). This is fact (M) of the parent proof. Notation: mu = V.weight; balls B_r closed; for xi fixed, r(x) := |x - xi|, w(x) := (x - xi)/|x - xi| for x != xi and w(xi) := 0; P_x := tangentProj_V(x); kappa := (p - n)/(4p) in (0, 1/4); omega_n = unitBallVolume n.
0. Local finiteness. For compact K contained in U, mu(K) = int_{M cap K} theta dH^n < infinity (theta integrable on M cap K). Since U is open and H is locally integrable on U for mu (part of the generalized mean curvature hypothesis), H is mu-integrable on every compact K contained in U (cover K by finitely many neighbourhoods within U on which H is integrable); in particular H, hence |H|, is mu-a.e. strongly measurable on such K, and int_K |H|^p dmu < infinity by the local L^p hypothesis.
1. Tangent facts (sibling tangent_ae). By the sibling, P is a.e. strongly measurable for H^n restricted to M, and for H^n-a.e. x in M some n-dimensional subspace is an approximate tangent space of M with respect to theta at x and Theta^n(mu, x) = theta(x). Since mu = theta H^n restricted to M is absolutely continuous with respect to H^n restricted to M, both statements hold mu-a.e. At such x the definition of tangentProj (projection onto a chosen approximate tangent space whenever one exists) makes P_x the orthogonal projection onto an n-dimensional subspace: P_x is self-adjoint, idempotent, ||P_x|| <= 1 and trace P_x = n. With theta >= 1 mu-a.e. we obtain:
(G) for mu-a.e. x: P_x is an orthogonal projection of rank n and Theta^n(mu, x) = theta(x) >= 1.
2. Radial first variation (Ch. 4, 3.2-3.4 and 4.1). Fix xi in U and R > 0 with B_R(xi) contained in U. Put A_R := int_{B_R(xi)} |H|^p dmu < infinity and Lambda := kappa^{-1} (R^(p-n) A_R)^(1/p) in [0, infinity), so that 4.2 holds: (R^(p-n) A_R)^(1/p) = kappa Lambda. Fix e in (0,1) and a C^1 nonincreasing phi : R -> [0,1] with phi = 1 on (-infinity, 1] and phi = 0 on [1 + e, infinity). For 0 < sigma < R/(1+e) let X_sigma(x) := phi(r(x)/sigma)(x - xi).
(2a) X_sigma is C^1 on R^(n+l): on the open ball of radius sigma about xi it equals x - xi, and on R^(n+l) minus {xi} it is a product of C^1 functions (r is smooth there); these two open sets cover R^(n+l). Its support is contained in B_{(1+e)sigma}(xi), which is compact and contained in B_R(xi), hence in U. So X_sigma is an admissible test field.
(2b) For x != xi, DX_sigma(x) v = phi(r/sigma) v + (r/sigma) phi'(r/sigma) <w, v> w, and DX_sigma = identity near xi. Hence, at every x where P_x is an orthogonal projection of rank n, div_M X_sigma(x) = trace(DX_sigma(x) o P_x) = n phi(r/sigma) + (r/sigma) phi'(r/sigma) <w, P_x w> = n phi(r/sigma) + (r/sigma) phi'(r/sigma)(1 - |w_perp|^2), where w_perp := w - P_x w (so <w, P_x w> = |P_x w|^2 = 1 - |w_perp|^2 when |w| = 1); at x = xi we have w = 0 = w_perp, DX_sigma(xi) = identity and div_M X_sigma(xi) = n = n phi(0), and every term containing w or w_perp is multiplied by r = 0 or by d/dsigma[phi(r/sigma)] = 0, so (2.1), I' and J' below are unaffected.
(2c) div_M X_sigma is mu-measurable (step 1), bounded (|trace(L o P_x)| <= (n + l)||L|| as ||P_x|| <= 1) and vanishes outside B_R(xi); <X_sigma, H> is integrable since |X_sigma| <= 2 sigma and H is integrable on B_R(xi) (step 0). The generalized mean curvature identity for X_sigma together with (2b), valid mu-a.e. by (G), gives
(2.1) int [n phi(r/sigma) + (r/sigma) phi'(r/sigma)] dmu - int (r/sigma) phi'(r/sigma) |w_perp|^2 dmu = - int phi(r/sigma) <x - xi, H> dmu.
(2d) Let I(sigma) := int phi(r/sigma) dmu and J(sigma) := int phi(r/sigma) |w_perp|^2 dmu. Since d/dsigma [phi(r/sigma)] = -(r/sigma^2) phi'(r/sigma) is continuous in sigma, vanishes unless r <= (1+e) sigma, and is bounded by (1+e) sup|phi'| / sigma_0 for sigma >= sigma_0 > 0, differentiation under the integral (mu(B_R(xi)) < infinity) shows that I and J are C^1 on (0, R/(1+e)) with sigma I'(sigma) = -int (r/sigma) phi'(r/sigma) dmu and sigma J'(sigma) = -int (r/sigma) phi'(r/sigma) |w_perp|^2 dmu. Moreover J is nondecreasing (for sigma_1 < sigma_2, phi(r/sigma_1) <= phi(r/sigma_2) as phi is nonincreasing), so J' >= 0. Thus (2.1) reads n I - sigma I' + sigma J' = - int phi(r/sigma) <x - xi, H> dmu, and multiplying by -sigma^(-n-1):
(4.1) d/dsigma (sigma^(-n) I(sigma)) = sigma^(-n) J'(sigma) + sigma^(-n-1) int phi(r/sigma) <x - xi, H> dmu.
3. Hoelder estimate (4.2-4.3). On the support of phi(r/sigma), |x - xi| <= (1+e) sigma <= 2 sigma, and 0 <= phi <= 1 gives phi <= phi^((p-1)/p). By Hoelder's inequality with exponents p and p/(p-1): |sigma^(-n-1) int phi(r/sigma) <x - xi, H> dmu| <= 2 sigma^(-n) int_{B_R(xi)} |H| phi(r/sigma)^((p-1)/p) dmu <= 2 sigma^(-n) A_R^(1/p) I(sigma)^(1-1/p) = 2 sigma^(-n/p) A_R^(1/p) (sigma^(-n) I(sigma))^(1-1/p). Now sigma^(-n/p) A_R^(1/p) = R^(-1) (sigma/R)^(-n/p) (R^(p-n) A_R)^(1/p) = kappa Lambda R^(-1) (sigma/R)^(-n/p), and a^(1-1/p) <= 1 + a for a >= 0. Hence, defining F_0(sigma) := -sigma^(-n-1) int phi(r/sigma) <x - xi, H> dmu / (1 + sigma^(-n) I(sigma)) (continuous in sigma by dominated convergence):
(4.3) d/dsigma (sigma^(-n) I) = sigma^(-n) J' - F_0(sigma)(1 + sigma^(-n) I), with |F_0(sigma)| <= 2 kappa Lambda R^(-1) (sigma/R)^(-n/p).
4. Integrating factor (4.4-4.5). As n/p < 1, int_0^sigma |F_0(t)| dt <= 2 kappa Lambda R^(-1) int_0^sigma (t/R)^(-n/p) dt = 2 kappa Lambda (p/(p-n)) (sigma/R)^(1-n/p) = (1/2) Lambda (sigma/R)^(1-n/p) <= Lambda/2 for sigma <= R. Let F(sigma) := exp(int_0^sigma F_0(t) dt) and E(sigma) := F(sigma) - 1. Then F is C^1 with F' = F_0 F and, by (4.3), d/dsigma [F sigma^(-n) I + E] = F [F_0 (sigma^(-n) I + 1) + sigma^(-n) J' - F_0 (1 + sigma^(-n) I)] = F sigma^(-n) J' >= 0. So
(4.4) g_e(sigma) := F(sigma) sigma^(-n) I(sigma) + E(sigma) is nondecreasing on (0, R/(1+e)), and
(4.5) exp(-(1/2) Lambda (sigma/R)^(1-n/p)) <= F(sigma) <= exp((1/2) Lambda (sigma/R)^(1-n/p)), |E(sigma)| <= (1/2) e^(Lambda/2) Lambda (sigma/R)^(1-n/p) (using |e^a - 1| <= |a| e^|a|).
5. Letting e -> 0 (4.7-4.8). Let e_k -> 0 and phi_k, I_k, F_0^(k), F^(k), E^(k) be the corresponding objects. For t in (0, R): phi_k(r/t) -> 1_{r <= t} pointwise (it equals 1 for r <= t and 0 for r > t once (1 + e_k) t < r), and it is dominated by the indicator of B_R(xi) once (1 + e_k) t < R. By dominated convergence (mu(B_R(xi)) < infinity and |x - xi||H| integrable on B_R(xi)), I_k(t) -> mu(B_t(xi)) and F_0^(k)(t) -> F_0*(t) := -t^(-n-1) int_{B_t(xi)} <x - xi, H> dmu / (1 + t^(-n) mu(B_t(xi))). The uniform bound |F_0^(k)(t)| <= 2 kappa Lambda R^(-1) (t/R)^(-n/p), integrable on (0, sigma), and dominated convergence give F^(k)(sigma) -> F*(sigma) := exp(int_0^sigma F_0*), E^(k)(sigma) -> E*(sigma) := F*(sigma) - 1, and the bounds (4.5) persist. For fixed 0 < sigma < tau < R and all k with (1 + e_k) tau < R, (4.4) gives g_{e_k}(sigma) <= g_{e_k}(tau); letting k -> infinity:
(4.8) g(sigma) := F*(sigma) sigma^(-n) mu(B_sigma(xi)) + E*(sigma) <= g(tau) for 0 < sigma < tau < R.
6. Existence of Theta (4.9, first half). g is nondecreasing on (0, R) and g(sigma) >= E*(sigma) >= -(1/2) e^(Lambda/2) Lambda, so g_0 := lim_{sigma->0+} g(sigma) exists in R. By (4.5), F*(sigma) -> 1 and E*(sigma) -> 0 as sigma -> 0+, hence sigma^(-n) mu(B_sigma(xi)) = (g(sigma) - E*(sigma))/F*(sigma) -> g_0. Thus Theta^n(mu, xi) := g_0/omega_n in [0, infinity) exists and mu(B_sigma(xi))/(omega_n sigma^n) -> Theta^n(mu, xi). Moreover, for 0 < tau < R,
(6.1) omega_n Theta^n(mu, xi) <= g(tau) <= exp((1/2) Lambda (tau/R)^(1-n/p)) tau^(-n) mu(B_tau(xi)) + (1/2) e^(Lambda/2) Lambda (tau/R)^(1-n/p).
This holds for every xi in U and every R with B_R(xi) contained in U, with Lambda = Lambda(xi, R) as above; since the right side of (6.1) is nondecreasing in Lambda, (6.1) also holds with any Lambda' >= Lambda(xi, R) in place of Lambda.
7. Upper semicontinuity (3.11, 4.9). Let xi be in U and y_j -> xi. Choose R > 0 with B_{2R}(xi) contained in U and put Lambda* := kappa^{-1} (R^(p-n) int_{B_{2R}(xi)} |H|^p dmu)^(1/p) < infinity. For j large, |y_j - xi| < R, so B_R(y_j) is contained in B_{2R}(xi), hence in U, and Lambda(y_j, R) <= Lambda*. Fix 0 < tau < R and 0 < d < R - tau. For j with |y_j - xi| < d, B_tau(y_j) is contained in B_{tau+d}(xi), and (6.1) at y_j with Lambda* gives omega_n Theta^n(mu, y_j) <= exp((1/2) Lambda* (tau/R)^(1-n/p)) tau^(-n) mu(B_{tau+d}(xi)) + (1/2) e^(Lambda*/2) Lambda* (tau/R)^(1-n/p). Taking limsup in j, then letting d -> 0+ (mu(B_{tau+d}(xi)) decreases to mu(B_tau(xi)) because the closed balls decrease to B_tau(xi) and mu(B_{2R}(xi)) < infinity), and then tau -> 0+ (tau^(-n) mu(B_tau(xi)) -> omega_n Theta^n(mu, xi) by step 6, the exponential factor -> 1 and the additive term -> 0), we obtain limsup_j Theta^n(mu, y_j) <= Theta^n(mu, xi). So Theta^n(mu, .) is upper semicontinuous on U.
8. Theta >= 1 on spt V (Remark 4.10(1)). Let xi be in spt V = U cap spt mu, so mu(B_s(xi)) > 0 for every s > 0. By (G) the set of points where Theta^n(mu, x) >= 1 fails is mu-null. Hence for every s > 0 with B_s(xi) contained in U there is x_s in B_s(xi) with Theta^n(mu, x_s) >= 1 (otherwise B_s(xi) would be mu-null). Taking s = s_j -> 0, x_{s_j} -> xi, and step 7 gives Theta^n(mu, xi) >= limsup_j Theta^n(mu, x_{s_j}) >= 1. With t := Theta^n(mu, xi) in [1, infinity), step 6 gives mu(B_r(xi))/(omega_n r^n) -> t as r -> 0+; for small r the quotient is finite (B_r(xi) is a compact subset of U) and this is the convergence V.HasDensity xi t in [0, infinity].

## Key steps

1. From the sibling: mu-a.e. P_x is a rank-n orthogonal projection and Theta = theta >= 1 mu-a.e.
2. First variation with radial fields X = phi(r/sigma)(x - xi) gives d/dsigma(sigma^-n I) = sigma^-n J' + sigma^(-n-1) int phi <x - xi, H> (4.1)
3. Hoelder with kappa = (p-n)/(4p) bounds the curvature term by F_0 with |F_0| <= 2 kappa Lambda R^-1 (sigma/R)^(-n/p) (4.3)
4. Integrating factor: F sigma^-n I + F - 1 is nondecreasing, with F -> 1 (4.4-4.5); pass to closed balls as e -> 0 (4.8)
5. Theta^n(mu, xi) exists everywhere in U with the bound (6.1); Theta is upper semicontinuous (3.11)
6. Points of density >= 1 are mu-dense near any xi in spt V, so Theta(xi) >= 1 (4.10(1))

## Reference use

### local-project

Queries:
- `sed -n 1280,1400p book/chapter-05.txt (Theorem 7.1 and its printed proof)`
- `sed -n 215,575p book/chapter-04.txt (3.1-3.17, 4.1-4.11); sed -n 1,200p and 270,340p book/chapter-03.txt (1.1-1.9); sed -n 560,720p book/chapter-01.txt (3.1-3.7); grep -n 'Approximation Theorem' book/chapter-02.txt`
- `grep -n '^def \|^theorem ' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -rn 'ae_hasWeightedApproximateTangent\|ae_hasApproximateTangent\|Theorem 1.9\|1\.9' .lake/packages/simongmt/Poincare/SimonGMT`
- `grep -n '^theorem \|^def ' .lake/packages/simongmt/Poincare/SimonGMT/Chapter01/{Densities,DensityComparison,LowerDensityComparison,HausdorffDensityBounds,RelativeDensityComparison,GeneralDensity,EuclideanNormalization,Hausdorff}.lean`
- `cat .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/{LpLowerDensity,MultiplicityBridge}.lean; sed -n 1,227p .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/Basic.lean`
- `grep -n '^theorem \|^lemma \|^def ' .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/{Lipschitz,WhitneyExtension}.lean .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/{SubmanifoldCover,Differential}.lean; grep -n 'injective_area_formula_lipschitz_simon' -A 12 .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean; grep -n '^theorem' .lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `grep -rn 'μHE\[' <snapshot>/mathlib/Mathlib --include=*.lean; sed -n 1,200p <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n image_symmDiff <snapshot>/mathlib/Mathlib/Data/Set/Image.lean; rg -n 'inf_symmDiff_distrib_right|symmDiff_inf_distrib|inter_symmDiff_distrib' <snapshot>/mathlib/Mathlib/Order/SymmDiff.lean <snapshot>/mathlib/Mathlib/Data/Set/*.lean`
- `grep -n 'divRight\|mulRight\|to_additive' <snapshot>/mathlib/Mathlib/Topology/MetricSpace/IsometricSMul.lean`
- `rg -n 'theorem fderivWithin_of_mem_nhds|theorem ball_subset_interior_closedBall|theorem closedBall_mem_nhds ' <snapshot>/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean <snapshot>/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `rg -n 'isometry_sub_const|isometry_add_const|IsometryEquiv.subRight|def subRight|def addRight' <snapshot>/mathlib/Mathlib/Topology <snapshot>/mathlib/Mathlib/Analysis/Normed`
- `cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean; cmp <snapshot>/project/GMT/Ch05/README.md GMT/Ch05/README.md`
- `grep -rl '<the seven proposed lean_names>' .humanize GMT; python3 scan of dag.json nodes for reserved children/theorems`
- `lake env lean /tmp/dor-a1-check/Check2.lean (contract lines 1-460, namespace Submission with allard_regularity_theorem and the 7 children as sorry placeholders, full proof of density_one_regularity : DensityOneRegularity, sanity example transferring tangentProj measurability to V.weight)`
- `lake env lean /tmp/dor-a1-check/verify/FormalAll.lean (reviewer's sorry-free proofs of four children with the frozen types; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Data/Set/Image.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Data/Set/SymmDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Order/SymmDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/IsometricSMul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpLowerDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/MultiplicityBridge.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/tmp/dor-a1-check/Check2.lean`
- `/tmp/dor-a1-check/verify/FormalAll.lean`

Snapshot: project ea5607598f3133b40a13241f2e51517a8c6423cd, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json). The snapshot's Contract.lean and README.md are byte-identical to the workspace copies (cmp).

No prior work: there is no existing proof of DensityOneRegularity or of any proposed child. The seven proposed names occur nowhere in .humanize or GMT, and dag.json reserves no child names yet.

SimonGMT, Chapter03/Rectifiable.lean: defines HasWeightedApproximateTangentSpaceAt (l.330) and proves uniqueness (l.345), but the grep finds no a.e.-existence result (Ch. 3, 1.9 is not formalized) and nothing on measurability of the tangent field. Hence child tangent_ae.

SimonGMT Chapter04 L^p density results (LpLowerDensity.lean: one_le_stationaryDensityReal_of_mem_support_lp) are stated for Chapter04.RectifiableVarifold. That structure stores a tangent field, a measurable carrier and a globally locally finite weight (Chapter04/Basic.lean), so they do not apply to the contract varifold. Hence child density_ge_one, proved from the contract's first variation following Simon 4.1-4.10(1).

SimonGMT Chapter01/DensityComparison.lean has the Upper Density Theorem (simon_theorem_3_6) and the comparison theorem (simon_theorem_3_3, mul_simonHausdorff_le_of_le_dimensionalUpperDensity). Both are stated for simonHausdorffOuterMeasureReal, a positive multiple of μH[n] (Hausdorff.lean: simonHausdorffOuterMeasureReal_eq_scaled_hausdorffMeasure). Since μHE[n] is also a nonzero multiple of μH[n] (Mathlib Geometry/Euclidean/Volume/Measure.lean), null sets agree; this is used by carrier_support_null.

SimonGMT also provides, for tangent_ae: Lusin (Chapter01/Lusin.lean, simon_theorem_1_17), the injective Lipschitz area formula (Chapter02/AreaLipschitz.lean:126) and Whitney C^1 extension (Chapter02/WhitneyExtension.lean).

Mathlib items used by the parent assembly:
- Isometry.euclideanHausdorffMeasure_image and IsometryEquiv.measurePreserving_euclideanHausdorffMeasure (Measure.lean)
- Set.image_symmDiff (Data/Set/Image.lean:388)
- Set.inter_symmDiff_distrib_right (Data/Set/SymmDiff.lean:46)
- IsometryEquiv.subRight, via to_additive of divRight (IsometricSMul.lean:166-172)
- fderivWithin_of_mem_nhds (FDeriv/Basic.lean:522)
- ball_subset_interior_closedBall (Pseudo/Defs.lean:1216) and closedBall_mem_nhds (Pseudo/Defs.lean:842)
The names isometry_sub_const / isometry_add_const / def subRight have no match in Topology or Analysis/Normed.

Lean checks:
- All 7 child types elaborate in the contract scope.
- density_one_regularity : DensityOneRegularity compiles from the children plus the sibling AllardRegularityTheorem. The only warnings are the 8 sorry warnings on the placeholders; an independent reviewer reproduced this.
- The reviewer's sorry-free Lean proofs of allard_scale, translate_varifold, open_graph_domain and holder_class use exactly the frozen types and recompile with axioms propext, Classical.choice, Quot.sound.
