# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.lipschitz_approximation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 5, Lemma 2.6 and its printed proof (pp. 110-113), in the contract normalization (arbitrary linear isometry q, T_0 = q(R^n x {0}), height hypothesis with an arbitrary constant K >= 0, documented erratum: the sup bound carries the scale factor sigma_0 = delta rho). Corrections of the printed argument: (i) monotonicity is used with the correct constant Lambda = 4 p delta/(p-n) of Ch. 4, 4.2 (kappa = (p-n)/(4p)); (ii) a dichotomy on the tilt of T_0 (Case A/Case B) makes beta and C independent of K; (iii) pairs of points of G at distance > sigma_0/2 are handled by the height bound (B3); (iv) the loss sqrt(l) in the componentwise extension is absorbed into beta, and a radial retraction gives the exact sup bound; (v) in (9)-(10) the annulus is B_{3s} minus B_s and the ball B_{3s}(zeta) must stay inside B_{3 sigma_0/4}(0), so graph points far from spt V are reached by a continuity (path) argument.

Notation (contract). mu := V.weight = theta H^n restricted to M (M = V.carrier, theta = V.mult); spt V := V.support = U cap spt mu; p_x := V.tangentProj x and p_x^perp := I - p_x; |A| is the Hilbert-Schmidt norm (hsNorm), ||A|| the operator norm, ||A|| <= |A| <= sqrt(rank A) ||A||; B_s(y) is the closed ball and B^o_s(y) the open ball; omega_n := unitBallVolume n; K(z,s) := (s^(p-n) integral_{B_s(z)} |H|^p dmu)^(1/p) in [0,infinity] (the contract's scaledLpNorm); E(z,s,T) := s^-n integral_{B_s(z)} |p_x - p_T|^2 dmu (tiltExcess); kappa := (p-n)/(4p) > 0; a := 1/(2n+2). Under 2.3, if B_s(z) is contained in B_rho(0) then K(z,s)^p = s^(p-n) integral_{B_s(z)} |H|^p <= (s/rho)^(p-n) rho^(p-n) integral_{B_rho(0)} |H|^p, so K(z,s) <= (s/rho)^(1-n/p) delta <= delta.
Further notation: sigma_0 := delta rho; alpha := a = 1/(2n+2); T_0 := rotatedPlane q; P := p_{T_0}; Q := I - P = p_{T_0^perp}; tilt(A) := integral_A |p_x - P|^2 dmu. Write q^-1 y = graphPoint(a(y), b(y)) with a(y) in R^n, b(y) in R^l; since q is a linear isometry mapping R^n x {0} onto T_0 and {0} x R^l onto T_0^perp, |a(y)| = |Py| <= |y| and |b(y)| = |Qy| = dist(y, T_0).

Sibling used: AffineApproximationLemma, with constant C_A >= 1 (enlarging the sibling's constant preserves both of its inequalities): for 0 < delta <= 1/4, 2.3, xi in spt V cap B_{delta rho}(0), s in (0, 2 delta rho] there is an n-plane T' with C_A^-1 (s^-n integral_{B_{s/2}(xi)} |p_x - p_{T'}|^2)^(1/2) <= s^-1 h(xi,s,T') + K(xi,s) and s^-1 h(xi,s,T') <= C_A delta^alpha, where h(xi,s,T') := sup{dist(x - xi, T') : x in spt V cap B_s(xi)}.

Facts used:
(F1) [Simon Ch. 3, Def. 1.7, Rem. 1.8, Thm. 1.9; contract tangentProj] For mu-a.e. x the approximate tangent space T_xM of M with respect to theta exists; at such x, p_x is the orthogonal projection onto the n-dimensional space T_xM, and Theta^n(mu,x) = theta(x) (Rem. 1.8(2)). The map x -> p_x is mu-measurable and bounded (|p_x - p_T|^2 <= 4n), so tilt integrals over compact subsets of U are finite: by Ch. 3, Rem. 1.3 and Rem. 1.8(1), M is covered up to an H^n-null set by countably many H^n-measurable pieces M_j contained in embedded C^1 submanifolds N_j, and for H^n-a.e. x in M_j the space T_xM exists and equals T_xN_j, which depends continuously on x in N_j; since T_xM is unique where theta(x) > 0 (SimonGMT HasWeightedApproximateTangentSpaceAt.unique), p_x agrees mu-a.e. with a Borel map. If Gamma is the graph of a Lipschitz map over (a subset of) an n-plane, then T_xM = T_x Gamma for H^n-a.e. x in M cap Gamma (Rem. 1.8(1)), and T_x Gamma is the range of the differential of the graph map at H^n-a.e. x in Gamma (Rademacher, Ch. 2, 1.4).
(F2) mu(R^(n+l) minus spt mu) = 0 and mu(R^(n+l) minus U) = 0, so mu-a.e. point lies in spt V; mu(K) < infinity for compact K in U; H^n(M minus spt V) = 0 (because mu(M minus spt V) = 0 and theta > 0 on M); spt V is relatively closed in U; if y in U minus spt V then mu(B^o_r(y)) = 0 for some r > 0.
(M) [Monotonicity: Simon Ch. 4, 4.1-4.10, with the coefficient in front of Lambda in 4.2 equal to kappa = (p-n)/(4p), the value required by the integration after 4.4 (cf. SimonGMT Chapter04 `lpMeanCurvatureKappa`, `LpAnnularCorrection`)]. Let y in R^(n+l) and R > 0 with B_R(y) in U and K(y,R) <= kappa Lambda for some Lambda > 0. (Under 2.3, whenever B_R(y) is contained in B_rho(0) we have K(y,R) <= delta, so Lambda := delta/kappa = 4 p delta/(p-n) is admissible; Lambda <= 1 as soon as delta <= kappa.) Then there are F : (0,R) -> (0,infinity) and numbers G(s,r) such that for all 0 < s <= r < R:
 (M.i) e^-Lambda <= F(r) <= e^Lambda and |F(r) - 1| <= (1/2) e^(Lambda/2) Lambda (r/R)^(1-n/p); if Lambda <= 1, then |F(r) - 1| <= Lambda (r/R)^(1-n/p) <= Lambda; F(r) -> 1 as r -> 0.
 (M.ii) Phi(r) - Phi(s) = G(s,r) integral_{B_r(y) minus B_s(y)} |p_x^perp(x - y)|^2 |x - y|^(-n-2) dmu(x), where Phi(t) := F(t) t^-n mu(B_t(y)) + F(t) - 1 and G(s,r) in [e^-Lambda, e^Lambda].
 (M.iii) Hence Phi is nondecreasing, Theta(y) := lim_{s -> 0} omega_n^-1 s^-n mu(B_s(y)) exists, and omega_n Theta(y) = lim_{s -> 0} Phi(s) <= Phi(r) for every r in (0,R); in particular mu({y}) = 0.
 (M.iv) [Ch. 4, 4.9 and 4.10(1), applied to V restricted to an open set W in U on which H is in L^p_loc] If theta >= 1 mu-a.e. and W is an open subset of U each point of which is the centre of a ball as above, then Theta >= 1 at every point of spt V cap W: Theta = theta >= 1 mu-a.e. by (F1), Theta is upper semicontinuous on W (4.9), so {x in W : Theta(x) < 1} is open and mu-null, hence disjoint from spt mu. Under 2.3 this applies to W = B^o_rho(0) (H is in L^p(B_rho(0)) since K(0,rho) <= delta < infinity).
 (M.v) If Lambda <= 1 and 0 < s <= r < R, then s^-n mu(B_s(y)) <= e^(2 Lambda) r^-n mu(B_r(y)) + 2 e^Lambda Lambda. [By (M.ii) Phi(s) <= Phi(r), so F(s) s^-n mu(B_s(y)) = Phi(s) - (F(s) - 1) <= F(r) r^-n mu(B_r(y)) + (F(r) - 1) + Lambda <= e^Lambda r^-n mu(B_r(y)) + 2 Lambda; divide by F(s) >= e^-Lambda.]
(P) [2.4 of the text, with explicit constants]. Assume 2.3 (AllardHypotheses H p delta rho) with delta <= min{1/8, kappa}, so Lambda := delta/kappa <= 1. Consider the smooth functions of t in [0, min{1/8, kappa}] (with Lambda_t := t/kappa)
 g_+(t) := e^(2 Lambda_t) (1 + t)(1 - 3t)^-n + 2 e^(Lambda_t) Lambda_t/omega_n,
 g_-(t) := e^(-Lambda_t) (1 - Lambda_t/omega_n),
 g_c(t) := e^(Lambda_t) (e^(Lambda_t) (1 + t)(1 - 3t)^-n - 1) + e^(Lambda_t) Lambda_t/omega_n.
Since g_+(0) = g_-(0) = 1 and g_c(0) = 0, there is C_P = C_P(n,p) >= 1 with g_+(t) <= 1 + C_P t, g_-(t) >= 1 - C_P t and g_c(t) <= C_P t on that interval. Put delta_P := min{1/8, kappa, 1/(2 C_P)}.
Claim. If delta <= delta_P, |y| <= 3 delta rho and 0 < s <= rho/2, then (P.i) mu(B_s(y)) <= (1 + C_P delta) omega_n s^n <= 2 omega_n s^n and Theta(y) <= 1 + C_P delta; if moreover y in spt V, then (P.ii) mu(B_s(y)) >= (1 - C_P delta) omega_n s^n >= omega_n s^n/2 and (P.iii) integral_{B_s(y)} |p_x^perp(x - y)|^2 |x - y|^(-n-2) dmu(x) <= C_P omega_n delta (integrand := 0 at x = y).
Proof. R_y := (1 - 3 delta) rho >= 5 rho/8 > rho/2 >= s, B_{R_y}(y) is contained in B_rho(0) (as |y| + R_y <= rho), so (M) applies at y with R = R_y and Lambda = delta/kappa <= 1, and mu(B_r(y)) <= mu(B_rho(0)) <= (1 + delta) omega_n rho^n for r < R_y. (P.i): for s <= r < R_y, (M.ii),(M.i) give F(s) s^-n mu(B_s(y)) = Phi(s) - (F(s) - 1) <= Phi(r) + Lambda <= e^Lambda r^-n mu(B_r(y)) + 2 Lambda; dividing by F(s) >= e^-Lambda and letting r -> R_y, omega_n^-1 s^-n mu(B_s(y)) <= g_+(delta); Theta(y) is the limit as s -> 0. (P.ii): Theta(y) >= 1 by (M.iv), so by (M.iii) F(s) s^-n mu(B_s(y)) >= omega_n - (F(s) - 1) >= omega_n - Lambda and s^-n mu(B_s(y)) >= e^-Lambda (omega_n - Lambda) = omega_n g_-(delta) (here omega_n - Lambda > 0 because g_-(delta) >= 1/2). (P.iii): for 0 < t < s <= r < R_y, (M.ii),(M.iii) give integral_{B_s(y) minus B_t(y)} |p_x^perp(x-y)|^2 |x-y|^(-n-2) dmu <= e^Lambda (Phi(r) - Phi(t)) <= e^Lambda (e^Lambda r^-n mu(B_r(y)) + Lambda - omega_n Theta(y)) <= e^Lambda (e^Lambda r^-n mu(B_r(y)) + Lambda - omega_n); let r -> R_y and t -> 0 (monotone convergence, mu({y}) = 0) to get <= omega_n g_c(delta).
(Cov) [Ch. 1, 3.4, 5-times covering lemma] A family of closed balls in R^(n+l) with bounded radii has a countable pairwise disjoint subfamily {B_j} such that every ball of the family is contained in the 5-fold enlargement of some B_j.
(Ext) [Ch. 2, 1.2 (McShane), componentwise] An M-Lipschitz map from a subset of R^n to R^l extends to an (sqrt(l) M)-Lipschitz map on R^n.
(Gr) If g : R^n -> R^l has Lip g <= 1 and A is a subset of R^n, then H^n(q(graph of g over A)) <= 2^(n/2) L^n(A) (the map x -> q(graphPoint(x, g(x))) is sqrt(2)-Lipschitz, and H^n = L^n on R^n).

Proof. Constants C_1, C_2, ... depend only on n, l, p, and are independent of beta, L, K, delta, rho, q. The constant beta in (0,1/4] is fixed in step 11 (depending only on n, l, p); c_0 := beta^2. Let L in (0,1], K >= 0, 0 < delta <= (beta L)^(2n+2), 2.3, and q as in the statement. Then delta <= beta^(2n+2) <= delta_P <= 1/8 (step 11) and delta^alpha <= beta L; every centre used below lies in B_{sigma_0}(0), a subset of B_{3 delta rho}(0), and every radius is <= 5 sigma_0/2 <= rho/2, so (P) is available.

1. Case A: tilt(B_{sigma_0}(0)) >= c_0 L^2 sigma_0^n. Take f := 0: Lip f = 0 <= L and |f| = 0 <= K delta^alpha sigma_0. The left side of the claim is at most mu(B_{sigma_0/2}(0)) + H^n(q(B^n_{sigma_0/2}(0) x {0})) <= 2 omega_n (sigma_0/2)^n + omega_n (sigma_0/2)^n <= 3 omega_n sigma_0^n <= (3 omega_n/c_0) L^-2 tilt(B_{sigma_0}(0)) (by (P.i) and since H^n = L^n on the n-plane T_0).

From now on Case B: tilt(B_{sigma_0}(0)) < c_0 L^2 sigma_0^n.

2. Height bound. The sibling at xi = 0 (in spt V cap B_{delta rho}(0)) and s = 2 sigma_0 gives an n-plane T* with h(0, 2 sigma_0, T*) <= 2 C_A delta^alpha sigma_0 and, since K(0, 2 sigma_0) <= delta <= delta^alpha, integral_{B_{sigma_0}(0)} |p_x - p_{T*}|^2 dmu <= C_1 delta^(2 alpha) sigma_0^n <= C_1 beta^2 L^2 sigma_0^n, C_1 := 2^n C_A^2 (C_A + 1)^2. Integrating |P - p_{T*}|^2 <= 2|p_x - P|^2 + 2|p_x - p_{T*}|^2 over B_{sigma_0}(0), whose measure is >= omega_n sigma_0^n/2 by (P.ii), gives |P - p_{T*}|^2 <= (4/omega_n)(c_0 + C_1 beta^2) L^2 = C_2^2 beta^2 L^2, C_2 := (4 (1 + C_1)/omega_n)^(1/2). Hence for x in spt V cap B_{2 sigma_0}(0):
 dist(x, T_0) = |Qx| <= dist(x, T*) + ||p_{T*} - P|| |x| <= 2 C_A delta^alpha sigma_0 + 2 C_2 beta L sigma_0 <= C_3 beta L sigma_0 =: h_0, C_3 := 2 C_A + 2 C_2. (B3)

3. Good set (book). G := {y in spt V cap B_{3 sigma_0/4}(0) : integral_{B_{s/2}(y)} |p_x - P|^2 dmu <= beta^2 L^2 s^n for every s in (0, sigma_0/2]}. For each y in (spt V cap B_{3 sigma_0/4}(0)) minus G choose s_y in (0, sigma_0/2] with beta^2 L^2 s_y^n < integral_{B_{s_y/2}(y)} |p_x - P|^2 dmu. (Cov) gives countably many pairwise disjoint B_{s_j}(y_j) of this family whose enlargements B_{5 s_j}(y_j) cover (spt V cap B_{3 sigma_0/4}(0)) minus G. By (P.i), mu(B_{5 s_j}(y_j)) <= 2 omega_n 5^n s_j^n; the balls B_{s_j/2}(y_j) are pairwise disjoint and contained in B_{sigma_0}(0). Since mu-a.e. point lies in spt V (F2),
 beta^2 L^2 mu(B_{3 sigma_0/4}(0) minus G) <= beta^2 L^2 sum_j mu(B_{5 s_j}(y_j)) <= 2 omega_n 5^n sum_j beta^2 L^2 s_j^n <= 2 omega_n 5^n sum_j tilt(B_{s_j/2}(y_j)) <= 2 omega_n 5^n tilt(B_{sigma_0}(0)),
 i.e. mu(B_{3 sigma_0/4}(0) minus G) <= C_4 beta^-2 L^-2 tilt(B_{sigma_0}(0)), C_4 := 2 omega_n 5^n. (6)

4. G is a graph with small Lipschitz constant. Let y_1 != y_2 in G and s := |y_1 - y_2| <= 3 sigma_0/2.
 (a) If s <= sigma_0/2: y_1 in spt V cap B_{delta rho}(0) and s <= 2 delta rho, so the sibling at (y_1, s) gives an n-plane T_1 with h(y_1, s, T_1) <= C_A delta^alpha s and (K(y_1, s) <= delta <= delta^alpha) integral_{B_{s/2}(y_1)} |p_x - p_{T_1}|^2 <= C_A^2 (C_A + 1)^2 delta^(2 alpha) s^n <= C_1 beta^2 L^2 s^n. As y_1 in G, integral_{B_{s/2}(y_1)} |p_x - P|^2 <= beta^2 L^2 s^n. Integrating |P - p_{T_1}|^2 <= 2|p_x - P|^2 + 2|p_x - p_{T_1}|^2 over B_{s/2}(y_1) (measure >= omega_n (s/2)^n/2 by (P.ii)) gives |P - p_{T_1}| <= C_5 beta L, C_5 := (2^(n+2) (1 + C_1)/omega_n)^(1/2). As y_2 in spt V cap B_s(y_1): |Q(y_2 - y_1)| <= dist(y_2 - y_1, T_1) + ||P - p_{T_1}|| s <= (C_A + C_5) beta L s =: C_6 beta L s.
 (b) If s > sigma_0/2: by (B3), |Q(y_2 - y_1)| <= |Q y_1| + |Q y_2| <= 2 h_0 = 2 C_3 beta L sigma_0 < 4 C_3 beta L s.
 Thus |Q(y_2 - y_1)| <= eps_1 L |y_2 - y_1| with eps_1 := max{C_6, 4 C_3} beta. As |y_2 - y_1| <= |P(y_2 - y_1)| + |Q(y_2 - y_1)| and eps_1 L <= 1/2 (step 11): |b(y_2) - b(y_1)| = |Q(y_2 - y_1)| <= 2 eps_1 L |P(y_2 - y_1)| = 2 eps_1 L |a(y_2) - a(y_1)|. So a is injective on G, and g : a(G) -> R^l, g(a(y)) := b(y), is (2 eps_1 L)-Lipschitz.

5. Extension and sup bound (book (5),(7)). By (Ext) there is f_1 : R^n -> R^l with f_1 = g on a(G) and Lip f_1 <= 2 sqrt(l) eps_1 L =: eps_0 L. Let R_0 := min{K delta^alpha sigma_0, h_0} >= 0, let pi be the nearest-point retraction of R^l onto the closed ball of radius R_0 about 0 (1-Lipschitz, the identity on that ball), and f := pi o f_1. Every y in G lies in spt V cap B_{2 sigma_0}(0), so |b(y)| = dist(y, T_0) <= K delta^alpha sigma_0 by hypothesis and <= h_0 by (B3); hence f = g on a(G). Therefore Lip f <= eps_0 L <= L on R^n (eps_0 <= 1, step 11), in particular f is L-Lipschitz on B^n_{sigma_0/2}(0), and |f| <= R_0 <= K delta^alpha sigma_0 everywhere. Put Fhat := {q(graphPoint(x, f(x))) : x in R^n} (a closed set, f being continuous on R^n, so all sets B minus Fhat below are Borel) and F := q '' graphOver f (B^n_{sigma_0/2}(0)). Then G and F are subsets of Fhat, and for x, z in Fhat, |Q(x - z)| = |f(a(x)) - f(a(z))| <= eps_0 |a(x) - a(z)| <= eps_0 |x - z|.

6. First term. If y in spt V cap B_{sigma_0/2}(0) cap G then |a(y)| <= |y| <= sigma_0/2 and y = q(graphPoint(a(y), f(a(y)))) is in F. So B_{sigma_0/2}(0) cap (spt V minus F) is contained in (spt V cap B_{3 sigma_0/4}(0)) minus G, and by (6) its measure is <= C_4 beta^-2 L^-2 tilt(B_{sigma_0}(0)).

7. Key estimate (book (9),(10), with the annulus B_{3s} minus B_s). Let zeta in Fhat minus spt V with |zeta| <= 17 sigma_0/32 and 0 < d := dist(zeta, spt V) <= sigma_0/16, and put s := d/2. Then B_{3s}(zeta) is contained in B_{20 sigma_0/32}(0), a subset of B_{3 sigma_0/4}(0), and
 s^n <= C_8 [ mu(B_{3s}(zeta) minus Fhat) + tilt(B_{3s}(zeta)) ]. (10')
 Proof. (a) Since spt mu is closed and |zeta| + d < rho, there is y in spt mu with |y - zeta| = dist(zeta, spt mu) <= d; such y has |y| < rho, hence y in U and y in spt V, so |y - zeta| = d and |y| <= sigma_0 <= 3 delta rho. The open ball B^o_d(zeta) misses spt mu, so mu(B_s(zeta)) = 0 (F2). (b) (M) at zeta with R := (1 - 3 delta) rho (B_R(zeta) is contained in B_rho(0); Lambda = delta/kappa <= 1). Since mu(B_s(zeta)) = 0, Phi(s) = F(s) - 1, and (M.ii) with r = 3s < R gives F(3s) (3s)^-n mu(B_{3s}(zeta)) = (F(s) - 1) - (F(3s) - 1) + G(s,3s) integral_{B_{3s}(zeta) minus B_s(zeta)} |p_x^perp(x - zeta)|^2 |x - zeta|^(-n-2) dmu <= 2 Lambda + e^Lambda s^(-n-2) I, where I := integral_{B_{3s}(zeta)} |p_x^perp(x - zeta)|^2 dmu, using |x - zeta| >= s on the annulus. With F(3s) >= e^-Lambda: (3s)^-n mu(B_{3s}(zeta)) <= 2 e Lambda + e^2 s^(-n-2) I. (c) B_s(y) is contained in B_{3s}(zeta), and mu(B_s(y)) >= omega_n s^n/2 by (P.ii); so (3s)^-n mu(B_{3s}(zeta)) >= 3^-n omega_n/2. Since delta <= delta_8 (step 11) gives 2 e Lambda = 8 e p delta/(p-n) <= 3^-n omega_n/4, we get s^(n+2) <= 4 * 3^n e^2 omega_n^-1 I. (d) On B_{3s}(zeta), p_x^perp = Q + (P - p_x), so |p_x^perp(x - zeta)|^2 <= 2 |Q(x - zeta)|^2 + 2 ||P - p_x||^2 |x - zeta|^2 <= 2 |Q(x - zeta)|^2 + 18 s^2 |p_x - P|^2, and |Q(x - zeta)| <= 3 eps_0 s for x in Fhat (step 5), |Q(x - zeta)| <= 3s otherwise. Also mu(B_{3s}(zeta)) <= mu(B_{5s}(y)) <= 2 omega_n 5^n s^n by (P.i). Hence I <= 18 s^2 [2 omega_n 5^n eps_0^2 s^n + mu(B_{3s}(zeta) minus Fhat) + tilt(B_{3s}(zeta))]. (e) By (c),(d): s^n <= A_8 [2 omega_n 5^n eps_0^2 s^n + mu(B_{3s}(zeta) minus Fhat) + tilt(B_{3s}(zeta))], A_8 := 72 * 3^n e^2/omega_n. As eps_0^2 <= 1/(4 A_8 omega_n 5^n) (step 11), the first term is <= s^n/2, and (10') follows with C_8 := 2 A_8.

8. Far points. Suppose some zeta in (F minus spt V) cap B_{sigma_0/2}(0) has dist(zeta, spt V) > sigma_0/16. Write zeta = q(graphPoint(x_z, f(x_z))) with |x_z| <= sigma_0/2 and let gamma(t) := q(graphPoint(t x_z, f(t x_z))), t in [0,1], a path in Fhat with |gamma(t)| <= sigma_0/2 + h_0 <= 17 sigma_0/32 (h_0 <= sigma_0/32, step 11). The continuous function t -> dist(gamma(t), spt V) is <= |gamma(0) - 0| = |f(0)| <= h_0 <= sigma_0/32 at t = 0 (0 in spt V) and > sigma_0/16 at t = 1, so it equals sigma_0/16 at some t. Applying (10') at zeta' := gamma(t) (so s = sigma_0/32), using that B_{3s}(zeta') is in B_{3 sigma_0/4}(0), G is contained in Fhat, and (6): (sigma_0/32)^n <= C_8 [mu(B_{3 sigma_0/4}(0) minus G) + tilt(B_{sigma_0}(0))] <= C_8 (C_4 beta^-2 + 1) L^-2 tilt(B_{sigma_0}(0)). In this case the whole left side of the claim is at most mu(B_{sigma_0/2}(0)) + H^n(F) <= 2 omega_n (sigma_0/2)^n + 2^(n/2) omega_n (sigma_0/2)^n <= 3 omega_n sigma_0^n (by (P.i) and (Gr)), hence <= 3 omega_n 32^n C_8 (C_4 beta^-2 + 1) L^-2 tilt(B_{sigma_0}(0)).

9. Near points. Otherwise every zeta in Z := (F minus spt V) cap B_{sigma_0/2}(0) has 0 < d(zeta) := dist(zeta, spt V) <= sigma_0/16 (d(zeta) > 0 by (F2), as zeta in U minus spt V), so (10') holds at zeta with s(zeta) := d(zeta)/2 <= sigma_0/32. (Cov) applied to {B_{3 s(zeta)}(zeta) : zeta in Z} gives countably many pairwise disjoint B_{3 s_j}(zeta_j) with Z contained in the union of the B_{15 s_j}(zeta_j). Fhat cap B_{15 s_j}(zeta_j) is contained in q(graph of f over B^n_{15 s_j}(a(zeta_j))), so H^n(Fhat cap B_{15 s_j}(zeta_j)) <= 2^(n/2) omega_n 15^n s_j^n by (Gr) (Lip f <= 1). Summing (10') over the disjoint balls B_{3 s_j}(zeta_j), all contained in B_{3 sigma_0/4}(0):
 H^n(Z) <= 2^(n/2) omega_n 15^n C_8 [mu(B_{3 sigma_0/4}(0) minus Fhat) + tilt(B_{sigma_0}(0))] <= 2^(n/2) omega_n 15^n C_8 (C_4 beta^-2 + 1) L^-2 tilt(B_{sigma_0}(0)),
 using G subset Fhat, (6) and L <= 1. With step 6 this bounds the left side of the claim.

10. Conclusion of Case B. By steps 6, 8, 9 the left side of the claim is <= C' L^-2 tilt(B_{sigma_0}(0)) with C' := C_4 beta^-2 + (3 omega_n 32^n + 2^(n/2) omega_n 15^n) C_8 (C_4 beta^-2 + 1), and f has the required Lipschitz and sup properties (step 5).

11. Choice of constants. The constants C_A, C_1, ..., C_6, A_8, C_8 do not depend on beta. Choose beta in (0,1/4] (depending only on n, l, p) with: beta^(2n+2) <= min{delta_P, delta_8}, delta_8 := 3^-n omega_n (p-n)/(32 e p); eps_1 = max{C_6, 4 C_3} beta <= 1/2; eps_0 = 2 sqrt(l) eps_1 <= 1 and eps_0^2 <= 1/(4 A_8 omega_n 5^n); C_3 beta <= 1/32 (so h_0 <= sigma_0/32). Put c_0 := beta^2 and C := max{3 omega_n/c_0, C'}. Then beta, C depend only on n, l, p, and the lemma holds for all L in (0,1] and K >= 0.

## Key steps

1. Corrected monotonicity constants (Lambda = 4 p delta/(p-n)) and pinched mass bounds (P)
2. Case A, large tilt of T_0: f = 0
3. Case B: T_0 is C beta L-close to T(0, 2 sigma_0), so the height is <= h_0 = C beta L sigma_0
4. Good set G; five-times covering bounds mu(B_{3 sigma_0/4}(0) minus G) by C beta^-2 L^-2 times the tilt
5. G is a (2 eps_1 L)-Lipschitz graph over T_0; componentwise extension plus retraction gives f
6. (10') from monotonicity at graph points off spt V (annulus B_{3s} minus B_s), absorbing the eps_0 term
7. Far points by the path argument; near points by covering

## Reference use

### local-project

Queries:
- `rg -l 'TiltExcessHeightEstimate|AffineApproximationLemma|LipschitzApproximationLemma|LipschitzGraphCorollary|HarmonicApproximationLemma|TiltExcessDecayTheorem|AllardRegularityTheorem|AllardRegularityAnyRadius|ConicalApproximationTheorem|DensityOneRegularity|DensityOneHigherRegularity|RegularSetOpenDense' <snapshot>`
- `for pat in Rellich Kondrachov Weyl Campanato Kirszbraun '[Cc]oarea' '[Vv]arifold' Allard Schauder 'Poincare_inequality|poincare_inequality'; do rg -l $pat <snapshot>/mathlib/Mathlib | wc -l; done`
- `rg -n 'def HarmonicOnNhd|def HarmonicAt|theorem mk_ball' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Harmonic`
- `rg -n 'theorem LipschitzOnWith.extend_real|lipschitzExtensionConstant' <snapshot>/mathlib/Mathlib`
- `rg -l 'exists_disjoint_subfamily_covering_enlargement|Besicovitch|Rademacher|lintegral_image_eq_lintegral_abs_det_fderiv_mul' <snapshot>/mathlib/Mathlib`
- `rg -n 'def lpMeanCurvatureKappa|structure LpAnnularCorrection|exists_lpAnnularCorrection|one_le_stationaryDensityReal_of_mem_support_lp|fiveTimes|lipschitz_extension_real_optimal|rademacher_ae_differentiableAt|injective_area_formula_lipschitz_simon|harmonicComparison_energy_le_sixthPower|HasWeightedApproximateTangentSpaceAt.unique' .lake/packages/simongmt/Poincare/SimonGMT`
- `rg -c sorry .lake/packages/simongmt/Poincare/SimonGMT`
- `lake env lean /tmp/gmt-ch05-v2-check/Check.lean (Contract.lean lines 1-460, then namespace Submission with the 12 child declarations, then the root assembly)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Harmonic/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpMeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpAnnular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpLowerDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/SobolevCovering.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter05/HarmonicEnergy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/tmp/gmt-ch05-v2-check/Check.lean`

Snapshot pinned at project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json).

No prior proofs: the 12 conjunct names occur only in project/GMT/Ch05/{Contract,Submission}.lean and README.md.

No-match searches in mathlib/Mathlib (0 files each): Rellich, Kondrachov, Campanato, Kirszbraun, coarea, varifold, Allard, Poincare_inequality. 'Weyl' matches only Lie-algebra and root-system files, and 'Schauder' only Schauder-basis files (l2Space.lean, Normed/Module/Bases.lean). So Mathlib has no Weyl lemma for harmonic functions and no Schauder PDE theory.

Usable Mathlib items:
- HarmonicAt and HarmonicOnNhd (Harmonic/Basic.lean:41,48).
- LipschitzOnWith.extend_real (Topology/MetricSpace/Lipschitz.lean:308) and lipschitzExtensionConstant (FiniteDimension.lean:194).
- Vitali and Besicovitch coverings.
- Rademacher (Analysis/Calculus/Rademacher.lean).
- Change of variables (MeasureTheory/Function/Jacobian.lean).

The pinned simongmt package lies outside the snapshot; 'rg -c sorry' finds no matches. It provides:
- lpMeanCurvatureKappa = (p-n)/(4p) (Chapter04/LpMeanCurvature.lean:76) and LpAnnularCorrection (Chapter04/LpAnnular.lean:335). These confirm the corrected monotonicity used in all revised child proofs: Lambda = 4 p delta/(p-n), factor bounds e^(-Lambda) <= F <= e^Lambda, error |F-1| <= (e^(Lambda/2)/2) Lambda (rho/R)^(1-n/p), and |F-1| <= Lambda (rho/R)^(1-n/p) when Lambda <= 1.
- one_le_stationaryDensityReal_of_mem_support_lp (LpLowerDensity.lean:43).
- Chapter01.exists_fiveTimesCovering (used at Chapter04/SobolevCovering.lean:39).
- lipschitz_extension_real_optimal and rademacher_ae_differentiableAt (Chapter02/Lipschitz.lean:170,192).
- injective_area_formula_lipschitz_simon (Chapter02/AreaLipschitz.lean:126).
- HasWeightedApproximateTangentSpaceAt.unique (Chapter03/Rectifiable.lean:345).
- harmonicComparison_energy_le_sixthPower (Chapter05/HarmonicEnergy.lean:94).
The Chapter04 results are stated for the stronger Chapter04.RectifiableVarifold, which stores the tangent field as data, so reuse needs a bridge via Ch. 3, 1.9 and axiom checks.

Lean check (Check.lean): all 12 child types elaborate in the contract scope, and the root assembly has exactly the type of main_theorem. The only warnings are sorry warnings for the placeholder child declarations.
