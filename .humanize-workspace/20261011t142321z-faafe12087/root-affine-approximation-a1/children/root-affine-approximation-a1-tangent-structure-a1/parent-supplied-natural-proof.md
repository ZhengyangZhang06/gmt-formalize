# Parent-supplied natural-language proof

- Parent DAG node: `root.affine_approximation-a1`
- Child DAG node: `root.affine_approximation-a1.tangent_structure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 3, Lemma 1.2 (with Ch. 2, Thm 1.5), Remark 1.3, the proof of Theorem 1.6 ('=>'), Remarks 1.8(1),(2) and Theorem 1.9 ('=>'), localized to U (theta is only integrable on compact subsets of U), together with the measurability statement (F1) of the parent proof.

Notation: mu := V.weight; p_x := V.tangentProj x; B_r(x) is the closed ball; H^n = mu_HE[n]; for f in C_c(R^(n+l)), x in R^(n+l) and lambda > 0, Lambda_lambda(f) := integral_{eta_{x,lambda}(M)} f(y) theta(x + lambda y) dH^n(y), where eta_{x,lambda}(z) = (z - x)/lambda (the quantity in Definition 1.7, i.e. in SimonGMT Chapter03.HasWeightedApproximateTangentSpaceAt n M theta x P).

1. Reduction. mu(A) = integral_{A cap M} theta dH^n and theta > 0 on M, so mu(E) = 0 whenever H^n(E cap M) = 0; hence it suffices to prove (a), (b), (c) for H^n-a.e. x in M (for (b): a map that agrees with a strongly measurable map outside such a set is mu-a.e. strongly measurable). Since U is open, fix open balls W_1, W_2, ... with compact closures cl(W_m) contained in U and union equal to U. Then mu_m := mu restricted to cl(W_m) is a finite Borel regular measure (mu(cl W_m) = integral_{M cap cl W_m} theta dH^n < infinity by V.integrableOn_mult), and it suffices to treat x in M cap W_m for each m. Since theta is H^n-a.e. measurable on M (V.aemeasurable_mult), fix a Borel function theta~ with theta~ = theta at H^n-a.e. point of M, and put N_theta := {x in M : theta(x) != theta~(x)}, an H^n-null set.

2. C^1 cover (Simon Ch. 3, Lemma 1.2). By V.countablyRectifiable, M is contained in M_0' union (union over j of F_j(R^n)) with H^n(M_0') = 0 and F_j : R^n -> R^(n+l) Lipschitz.
 (2a) C^1 approximation (Simon Ch. 2, Thm 1.5, applied to each coordinate function; printed proof): let F : R^n -> R be Lipschitz and epsilon > 0. By Rademacher's theorem (SimonGMT Chapter02.rademacher_ae_differentiableAt) F is differentiable on a set B with L^n(R^n minus B) = 0. By Lusin's theorem there is a closed set C contained in B with grad F restricted to C continuous and L^n(R^n minus C) < epsilon/2. For x, y in C let R(x,y) := (F(y) - F(x) - grad F(x).(y - x))/|x - y| and eta_k(x) := sup{|R(x,y)| : y in C cap B_{1/k}(x), y != x}; eta_k decreases to 0 pointwise on C (differentiability), so by Egoroff's theorem on the sets C cap B_j(0) there is a closed set A contained in C with L^n(R^n minus A) < epsilon on whose bounded subsets eta_k -> 0 uniformly, i.e. Whitney's condition 1.6(*) holds on A. Whitney's extension theorem (Simon Ch. 2, Thm 1.6; SimonGMT Chapter02.exists_contDiff_one_extension_of_whitney) gives g in C^1(R^n) with g = F and grad g = grad F on A, so L^n({F != g}) < epsilon.
 (2b) Hence for each j and i >= 1 there is G_ij in C^1(R^n; R^(n+l)) with L^n({F_j != G_ij}) < 1/i. With Z_j := R^n minus (union over i of {F_j = G_ij}) we get L^n(Z_j) = 0, hence H^n(F_j(Z_j)) <= (Lip F_j)^n L^n(Z_j) = 0, and F_j(R^n) is contained in F_j(Z_j) union (union over i of G_ij(R^n)).
 (2c) For a C^1 map G : R^n -> R^(n+l) let JG := sqrt(det(DG^T DG)); JG(v) = 0 iff DG(v) is not injective. The image of the critical set {JG = 0} is H^n-null (Sard-type consequence of the area formula; SimonGMT Chapter02.area_image_criticalSet_eq_zero). If JG(v) > 0, then by the inverse function theorem there is r_v > 0 such that G is injective with injective differential on B_{2 r_v}(v) and G restricted to B^o_{2 r_v}(v) is a homeomorphism onto its image; then N := G(B^o_{r_v}(v)) is an embedded n-dimensional C^1 submanifold, it is sigma-compact (union of the compact sets G(B_{r_v - 1/k}(v))) hence Borel, H^n(N) <= integral_{B_{r_v}(v)} JG dL^n < infinity (area formula for the injective Lipschitz map G on B_{r_v}(v); SimonGMT Chapter02.injective_area_formula_lipschitz_simon), T_z N = DG(w)(R^n) for z = G(w), and z -> p_{T_z N} = DG(w)(DG(w)^T DG(w))^(-1) DG(w)^T with w = G^(-1)(z) is continuous on N. By the Lindelof property countably many such balls cover {JG > 0}.
 (2d) Collecting: M is contained in N_0 union (union over j >= 1 of N_j), where N_0 is a Borel set with H^n(N_0) = 0 (enlarge the null set to a Borel null set, H^n being Borel regular) and each N_j (j >= 1) is a Borel embedded n-dimensional C^1 submanifold with H^n(N_j) < infinity on which z -> p_{T_z N_j} is continuous.

3. Disjoint pieces (Simon Ch. 3, Remark 1.3; SimonGMT Chapter03.simon_remark_1_3_nullMeasurable). Put M_0 := M cap N_0 and M_j := (M cap N_j) minus (union over i < j of N_i) for j >= 1. These sets are pairwise disjoint and H^n-null-measurable (M is, the N_i are Borel), M is their union, H^n(M_0) = 0, and M_j is contained in N_j.

4. Blow-up of a C^1 submanifold. Let N be one of the N_j and x in N. Claim: for every f in C_c(R^(n+l)), lambda^(-n) integral_N f((z - x)/lambda) dH^n(z) -> integral_{T_x N} f dH^n as lambda -> 0+, and for each R > 0 the quantity lambda^(-n) H^n(N cap B_{R lambda}(x)) stays bounded as lambda -> 0+. Proof: choose an orthogonal map Q of R^(n+l) with Q(T_x N) = R^n x {0}. By the implicit function theorem (applied in a local parametrization G of N to w -> p_{T_x N}(G(w) - x), whose differential at G^(-1)(x) is invertible) there are r > 0, an open set W containing x and a C^1 map u : B^n_r(0) -> R^l with u(0) = 0, Du(0) = 0 and N cap W = {x + Q^(-1)(v, u(v)) : v in B^n_r(0)}; as N is embedded there is epsilon > 0 with N cap B_epsilon(x) contained in N cap W. Let f be supported in B_R(0) and 0 < lambda < epsilon/R. By the area formula for the injective Lipschitz graph map v -> (v, u(v)) (Jacobian J_u(v) = sqrt(det(I + Du(v)^T Du(v))), continuous with J_u(0) = 1) and the substitution v = lambda w,
 lambda^(-n) integral_N f((z - x)/lambda) dH^n(z) = integral_{B^n_{r/lambda}(0)} f(Q^(-1)(w, u(lambda w)/lambda)) J_u(lambda w) dw.
The integrand vanishes for |w| > R, and for |w| <= R we have u(lambda w)/lambda -> Du(0) w = 0 and J_u(lambda w) -> 1 uniformly, while f is bounded and uniformly continuous; hence the right side tends to integral_{R^n} f(Q^(-1)(w, 0)) dw = integral_{T_x N} f dH^n (H^n on the n-plane T_x N is the image of L^n under the isometry w -> Q^(-1)(w, 0); Mathlib normalizes mu_HE[n] to agree with volume on EuclideanSpace R (Fin n)). Choosing f >= 1 on B_R(0) gives the boundedness claim.

5. Lusin sets and upper-density sets (Simon Ch. 3, Remark 1.8(1)). Fix j >= 1 and m and put A_{j,m} := (M_j cap W_m) minus N_theta, so H^n(A_{j,m}) <= H^n(N_j) < infinity. By Lusin's theorem (Simon Ch. 1, 1.17; SimonGMT Chapter01 IsBorelRegularOuterMeasure.simon_theorem_1_17; H^n is Borel regular) applied to the Borel function theta~ on A_{j,m}, for each k there is a compact set K_{j,m,k} contained in A_{j,m} with H^n(A_{j,m} minus K_{j,m,k}) < 1/k and theta~ restricted to K_{j,m,k} continuous; on K_{j,m,k} we have theta = theta~, so theta restricted to K_{j,m,k} is continuous, and H^n(A_{j,m} minus (union over k of K_{j,m,k})) = 0. By the upper density theorem (Simon Ch. 1, Thm 3.6; SimonGMT Chapter01.simon_theorem_3_6), writing K := K_{j,m,k}:
 (i) applied to the finite Borel regular measure mu_m and the mu_m-measurable set M minus K: limsup_{lambda -> 0+} lambda^(-n) mu_m((M minus K) cap B_lambda(x)) = 0 for H^n-a.e. x outside M minus K, in particular for H^n-a.e. x in K;
 (ii) applied to the finite Borel regular measure H^n restricted to N_j and the set N_j minus K: limsup_{lambda -> 0+} lambda^(-n) H^n((N_j minus K) cap B_lambda(x)) = 0 for H^n-a.e. x in K.
Let E be the union, over all j >= 1, m, k, of the exceptional H^n-null sets of (i) and (ii) and of the sets A_{j,m} minus (union over k of K_{j,m,k}), together with M_0 and N_theta. Then H^n(E) = 0, and every x in M minus E lies in some K_{j,m,k}.

6. Existence of the weighted approximate tangent space (proof of Thm 1.6 '=>' combined with Remark 1.8(1), i.e. Thm 1.9 '=>'). Let x in M minus E, so x in K := K_{j,m,k}, contained in M_j cap W_m, for some j >= 1, m, k. Put P := T_x N_j, an n-dimensional subspace. Let f in C_c(R^(n+l)) be supported in B_R(0), and let lambda > 0 be so small that B_{R lambda}(x) is contained in W_m. The homothety z -> (z - x)/lambda maps H^n restricted to M onto lambda^n times H^n restricted to eta_{x,lambda}(M) (scaling law H^n(x + lambda S) = lambda^n H^n(S); Mathlib hausdorffMeasure_homothety_image), so y -> theta(x + lambda y) is a.e. measurable for H^n restricted to eta_{x,lambda}(M) (composition of the a.e.-measurable theta with this homothety), the integrand y -> f(y) theta(x + lambda y) is integrable there (bounded by sup|f| times theta(x + lambda y) on the blow-up of M cap B_{R lambda}(x), and integral_{M cap B_{R lambda}(x)} theta dH^n < infinity), and
 Lambda_lambda(f) = lambda^(-n) integral_M f((z - x)/lambda) theta(z) dH^n(z).
Split M as K union (M minus K):
 (a) |lambda^(-n) integral_{M minus K} f((z - x)/lambda) theta(z) dH^n(z)| <= sup|f| lambda^(-n) mu((M minus K) cap B_{R lambda}(x)) -> 0 by 5(i);
 (b) |lambda^(-n) integral_K f((z - x)/lambda) (theta(z) - theta(x)) dH^n(z)| <= sup|f| e(lambda) lambda^(-n) H^n(N_j cap B_{R lambda}(x)) -> 0, where e(lambda) := sup{|theta(z) - theta(x)| : z in K cap B_{R lambda}(x)} -> 0 by continuity of theta on K at x, and the last factor is bounded by Step 4;
 (c) theta(x) lambda^(-n) integral_K f((z - x)/lambda) dH^n(z) = theta(x) [lambda^(-n) integral_{N_j} f((z - x)/lambda) dH^n(z) - lambda^(-n) integral_{N_j minus K} f((z - x)/lambda) dH^n(z)] -> theta(x) [integral_P f dH^n - 0] by Step 4 and 5(ii).
Adding (a), (b), (c): Lambda_lambda(f) -> theta(x) integral_P f dH^n as lambda -> 0+. Together with finrank P = n this is exactly HasWeightedApproximateTangentSpaceAt n M theta x P. Since theta(x) > 0 (x in M), weighted approximate tangent spaces at x are unique (SimonGMT Chapter03.HasWeightedApproximateTangentSpaceAt.unique), so by the definition of V.tangentProj, p_x = P.starProjection, the orthogonal projection onto the n-dimensional subspace P = T_x N_j. Since H^n(E) = 0, Step 1 gives (a).

7. Measurability (b). For each j >= 1 choose a Borel set B_j contained in M_j with H^n(M_j minus B_j) = 0 (M_j is H^n-null-measurable). Define q(x) := p_{T_x N_j} if x in B_j (j >= 1) and q(x) := 0 otherwise. Each map x -> p_{T_x N_j} is continuous on the Borel set N_j (Step 2) and the B_j are pairwise disjoint Borel sets, so q is Borel measurable; its values lie in the finite-dimensional, hence second countable, normed space of linear maps of R^(n+l), so q is strongly measurable. By Step 6, p_x = p_{T_x N_j} = q(x) for every x in B_j minus E, and M minus (union over j >= 1 of (B_j minus E)) is H^n-null. By Step 1, p = q mu-a.e., so x -> p_x is AEStronglyMeasurable with respect to mu.

8. Density (c) (Simon Ch. 3, Remark 1.8(2)). Let x in M minus E with P as in Step 6, and let 0 < epsilon < 1. Choose continuous compactly supported f_+, f_- : R^(n+l) -> [0,1] with f_+ = 1 on B_1(0), f_+ = 0 off B_{1+epsilon}(0), f_- = 1 on B_{1-epsilon}(0), f_- = 0 off B^o_1(0). Then f_- <= indicator of B_1(0) <= f_+, and since theta > 0 on M, the change of variables of Step 6 gives, for small lambda, Lambda_lambda(f_-) <= lambda^(-n) integral_{M cap B_lambda(x)} theta dH^n = lambda^(-n) mu(B_lambda(x)) <= Lambda_lambda(f_+). By Step 6, Lambda_lambda(f_+-) -> theta(x) integral_P f_+- dH^n, and omega_n (1-epsilon)^n = H^n(P cap B_{1-epsilon}(0)) <= integral_P f_- dH^n and integral_P f_+ dH^n <= H^n(P cap B_{1+epsilon}(0)) = omega_n (1+epsilon)^n (H^n on the n-plane P is n-dimensional Lebesgue measure and the unit ball of R^n has volume pi^(n/2)/Gamma(n/2+1) = omega_n, Mathlib EuclideanSpace.volume_ball). Hence theta(x) omega_n (1-epsilon)^n <= liminf lambda^(-n) mu(B_lambda(x)) <= limsup lambda^(-n) mu(B_lambda(x)) <= theta(x) omega_n (1+epsilon)^n, and letting epsilon -> 0, mu(B_lambda(x))/(omega_n lambda^n) -> theta(x) as lambda -> 0+. All quantities are finite and theta(x) > 0, so in [0,infinity] we get mu(closedBall x lambda)/ofReal(omega_n lambda^n) -> ofReal(theta(x)) as lambda -> 0+, i.e. V.HasDensity x (theta x). This holds for every x in M minus E, hence mu-a.e. by Step 1, which is (c).

## Key steps

1. Reduce (a)-(c) to H^n-a.e. x in M, localize to balls W_m with compact closure in U, and fix a Borel representative theta~ of theta (null set N_theta).
2. Lemma 1.2 (with the printed proof of the C^1 approximation theorem 1.5 of Ch. 2): cover M, up to an H^n-null Borel set, by countably many Borel embedded C^1 n-submanifolds N_j of finite H^n-measure (critical images are null; inverse function theorem).
3. Remark 1.3: split M into disjoint null-measurable pieces M_j contained in N_j.
4. Blow-ups of a C^1 submanifold at x converge to H^n on T_xN; local H^n-density of N is bounded.
5. Lusin compacts K_k with theta continuous; upper density theorem for mu restricted to M minus K_k and for H^n restricted to N_j minus K_k.
6. At H^n-a.e. x the weighted blow-up integrals converge to theta(x) times the integral over T_xN_j; uniqueness gives p_x = p_{T_xN_j}.
7. p agrees mu-a.e. with a Borel map assembled from the continuous maps x -> p_{T_xN_j}: AEStronglyMeasurable.
8. Remark 1.8(2): test functions squeezing the unit ball give mu(B_r(x))/(omega_n r^n) -> theta(x).

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
