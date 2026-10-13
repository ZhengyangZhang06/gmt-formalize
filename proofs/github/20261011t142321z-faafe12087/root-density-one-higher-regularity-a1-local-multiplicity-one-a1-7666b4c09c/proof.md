# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.local_multiplicity_one-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the second half of Step 2 and Step 3 of the parent-supplied proof (Simon, Ch. 5, proof of Theorem 7.1, p. 128: 'Since theta is integer valued and < 2 a.e., we have theta = 1 H^n-a.e. on graph u; but graph u is a C^1 submanifold so then Theta^n(mu_V, x) = 1 at every point of graph u'), with the multiplicity-one step done by the monotonicity formula with the corrected constant kappa = (p-n)/(4p) and the omega_n-normalized additive error. The only change from the parent text is that the bound A_h R^{1-n/p} mu(B_{2t0}(xi))^{1/p} for the scaled L^p norm of H is replaced by the equivalent bound R^{1-n/p} (integral over B_{2t0}(xi) of |H|^p dmu)^{1/p}, which needs only H in L^p_loc. The identity Theta = theta mu-a.e. (fact F1 of the parent) and the lower bound Theta >= 1 on spt V (Simon 4.10(1)) are derived here inside the graph region from (Leb), the sibling dohr_c1_graph_density_one and the sibling dohr_local_monotonicity; the tangent-plane hypothesis of the latter is supplied by the sibling dohr_graph_tangent_planes, so no general existence theorem for approximate tangent spaces is used.

Notation. mu := V.weight, M := V.carrier, theta := V.mult, Sigma := V.support = U cap spt mu, H^n := muHE[n], omega_n := unitBallVolume n > 0, kappa := (p - n)/(4p) > 0. Balls are closed unless called open; B_r(y) denotes the closed ball, Bo_r(y) the open ball. T(y) := Q(y - xi) is an isometric bijection of R^(n+l) with inverse A(z) := xi + Q^{-1} z, and T maps Bo_r(xi), B_r(xi) onto Bo_r(0), B_r(0). G(x) := (x, u(x)), Gamma := G(Bo^n_R(0)). The graph hypothesis T(Sigma) cap Bo_R(0) = Gamma cap Bo_R(0) is equivalent to Sigma cap Bo_R(xi) = A(Gamma cap Bo_R(0)). By hypothesis theta is a positive integer mu-a.e.; in particular theta >= 1 mu-a.e.

Facts and siblings used. (F2) mu(R^(n+l) minus spt mu) = 0 (Mathlib Measure.measure_compl_support); mu = theta H^n restricted to M with theta > 0 on M, so for measurable S: mu(S) = integral over S cap M of theta dH^n, and mu(S cap M) = 0 iff H^n(S cap M) = 0. (TP) Sibling dohr_graph_tangent_planes (applied with s := R, using B_R(xi) contained in U): x -> V.tangentProj x is a.e.-strongly measurable for V.weight restricted to Bo_R(xi), and for mu-a.e. y in Bo_R(xi), V.tangentProj y is the orthogonal projection onto Q^{-1}(range DG(x)) where T(y) = G(x); this subspace has dimension n because DG(x) v = (v, Du(x) v) is injective. Since mu(Bo_R(xi) minus Sigma) = 0 and every y in Sigma cap Bo_R(xi) has T(y) = G(x) for some x in Bo^n_R(0), we get: for mu-a.e. y in Bo_R(xi) there is an n-dimensional subspace P with V.tangentProj y = P.starProjection. Both properties pass to every open ball Bo_{R'}(y') contained in Bo_R(xi) (for measurability: AEStronglyMeasurable.mono_measure with Measure.restrict_mono). (M) Sibling dohr_local_monotonicity: if y' in U, R' > 0, B_{R'}(y') contained in U, the tangent-plane condition holds mu-a.e. on Bo_{R'}(y') and x -> V.tangentProj x is a.e.-strongly measurable for V.weight restricted to Bo_{R'}(y') (by (TP) both hold whenever Bo_{R'}(y') is contained in Bo_R(xi)), 0 < Lambda <= 1 and (R'^{p-n} integral over B_{R'}(y') of |H|^p dmu)^{1/p} <= kappa Lambda, then there is F with |F(r) - 1| <= Lambda and e^{-Lambda} <= F(r) <= e^{Lambda} on (0, R') such that Phi(r) := F(r) r^{-n} mu(B_r(y')) + F(r) - 1 is nondecreasing on (0, R'), and the density Theta(y') := lim_{r -> 0+} mu(B_r(y'))/(omega_n r^n) exists (V.HasDensity y' Theta(y')) with omega_n Theta(y') = lim_{r -> 0+} Phi(r). (Leb) Besicovitch differentiation [Simon Ch. 1, 3.11-3.17; Mathlib Besicovitch.ae_tendsto_rnDeriv]: if lambda and nu are finite Borel measures on R^(n+l) with lambda = f nu (f >= 0 nu-integrable), then for nu-a.e. y, lambda(B_r(y))/nu(B_r(y)) -> f(y) as r -> 0+. (C4) Sibling dohr_c1_graph_density_one: for every x in Bo^n_R(0), H^n(Gamma cap B_r(G(x)))/(omega_n r^n) -> 1 as r -> 0+. (Iso) H^n(T(S)) = H^n(S) for every S (isometry invariance).

1. A finite graph piece. Put R1 := R/2 and B1 := Bo_{R1}(xi), contained in U since B_R(xi) is. Gamma1 := Sigma cap B1 = A(G(D1)) with D1 := {x in Bo^n_R(0) : |G(x)| < R1}, contained in Bo^n_{R1}(0) because |G(x)| >= |x|. On the compact convex ball B^n_{R1}(0) (inside Bo^n_R(0)) Du is continuous, hence bounded, so G is Lipschitz there and H^n(Gamma1) = H^n(G(D1)) < infinity (Lipschitz image bound for Hausdorff measure and (Iso)). Gamma1 is relatively closed in B1, hence Borel. Let nu := H^n restricted to Gamma1, a finite Borel measure.

2. Density of nu at its points. Let y in Gamma1. Then T(y) is in T(Sigma) cap Bo_R(0) = Gamma cap Bo_R(0), so T(y) = G(x) with x in Bo^n_R(0). For 0 < r < R1 - |y - xi| we have B_r(y) contained in B1 and B_r(T(y)) contained in Bo_{R1}(0), which is contained in Bo_R(0); hence nu(B_r(y)) = H^n(Sigma cap B_r(y)) = H^n(A(Gamma cap Bo_R(0)) cap B_r(y)) = H^n(Gamma cap B_r(G(x))) by (Iso). By (C4), nu(B_r(y))/(omega_n r^n) -> 1. In particular nu(B_r(y)) > 0 and nu(B_r(y)) <= 2 omega_n r^n for all small r > 0.

3. mu on B1 has density theta 1_M with respect to nu. B1 is contained in U, so B1 minus Sigma = B1 minus spt mu and mu(B1 minus Sigma) = 0 by (F2). For Borel S contained in B1: mu(S) = mu(S cap Sigma) = integral over S cap Sigma cap M of theta dH^n = integral over S of f dnu with f := theta 1_M (>= 0 on Gamma1). mu(B1) <= mu(B_R(xi)) < infinity (the closed ball B_R(xi) is a compact subset of U, so theta is H^n-integrable on M cap B_R(xi)). So lambda := mu restricted to B1 is a finite Borel measure and lambda = f nu, with f nu-integrable.

4. Theta = theta mu-a.e. on B1. By (Leb), for nu-a.e. y in Gamma1: lambda(B_r(y))/nu(B_r(y)) -> f(y). For y in B1 and small r, lambda(B_r(y)) = mu(B_r(y)). Multiplying by nu(B_r(y))/(omega_n r^n) -> 1 (step 2): for nu-a.e. y in Gamma1, mu(B_r(y))/(omega_n r^n) -> f(y), i.e. Theta(y) = f(y) = theta(y) 1_M(y). The exceptional nu-null set is mu-null (lambda << nu by step 3), mu(B1 minus Gamma1) = 0 and mu(complement of M) = 0. Hence: for mu-a.e. y in B1, y is in Gamma1 cap M and Theta(y) = theta(y) (in contract terms, V.HasDensity y (theta y)); in particular Theta(y) >= 1 for mu-a.e. y in B1.

5. Theta >= 1 on Gamma1 (Simon 4.10(1), proved locally with (M)). Let A1 := integral over B_R(xi) of |H|^p dmu < infinity (V.LocallyLp H p; B_R(xi) is a compact subset of U). For t > 0 put Lambda(t) := max{t^{1 - n/p} A1^{1/p}/kappa, t}; Lambda(t) > 0 and Lambda(t) -> 0 as t -> 0+. Let y in Gamma1 and choose t1 in (0, R/8] with Lambda(t) <= 1 for t <= t1. For 0 < t <= t1 and z with |z - y| <= t: Bo_t(z) and B_t(z) lie in Bo_{R/2 + 2t}(xi), contained in Bo_R(xi), contained in U, and (t^{p-n} integral over B_t(z) of |H|^p dmu)^{1/p} <= t^{1-n/p} A1^{1/p} <= kappa Lambda(t), so (M) applies at z with R' := t and Lambda := Lambda(t). For 0 < r < t and d := |z - y| this gives omega_n Theta(z) <= Phi_z(r) <= e^{Lambda(t)} r^{-n} mu(B_{r+d}(y)) + Lambda(t); letting r -> t-, omega_n Theta(z) <= e^{Lambda(t)} (1 + d/t)^n omega_n S(2t) + Lambda(t), where S(sigma0) := sup over 0 < sigma <= sigma0 of mu(B_sigma(y))/(omega_n sigma^n) (here t + d <= 2t). By (M) at y, Theta(y) exists and S(sigma0) -> Theta(y) as sigma0 -> 0+. Suppose Theta(y) < 1. Choose eps in (0, 1) with (1 + eps)^n Theta(y) < 1, and then t in (0, t1] so small that c := e^{Lambda(t)} (1 + eps)^n S(2t) + Lambda(t)/omega_n < 1 (possible because, as t -> 0+, Lambda(t) -> 0 and S(2t) -> Theta(y), so c -> (1 + eps)^n Theta(y) < 1). Then Theta(z) <= c < 1 for every z with |z - y| <= eps t. But Bo_{eps t}(y) is contained in B1 for small t (y is in the open set B1) and mu(Bo_{eps t}(y)) > 0 because y is in spt mu, so by step 4 there is z in Bo_{eps t}(y) with Theta(z) = theta(z) >= 1, a contradiction. Hence Theta(y) >= 1 for every y in Gamma1.

6. Carrier versus support on B1. (a) H^n((M cap B1) minus Sigma) = 0: mu((M cap B1) minus Sigma) <= mu(complement of spt mu) = 0 (F2), and these points lie in M where theta > 0, so their H^n measure is 0 (F2). (b) H^n(Gamma1 minus M) = 0: by step 4's application of (Leb), for nu-a.e. y in Gamma1 minus M we have lambda(B_r(y))/nu(B_r(y)) -> f(y) = 0, and nu(B_r(y)) <= 2 omega_n r^n for small r (step 2), so mu(B_r(y))/(omega_n r^n) <= 2 lambda(B_r(y))/nu(B_r(y)) -> 0, i.e. Theta(y) = 0, contradicting step 5. Hence nu(Gamma1 minus M) = 0, i.e. H^n((Sigma cap B1) minus M) = 0. Together: H^n((M cap B1) symmetric-difference (Sigma cap B1)) = 0.

7. Theta < 2 near xi (monotonicity, corrected constant, omega_n-normalized error). Fix t0 in (0, R1/2]; then B_{2 t0}(xi) is contained in B_R(xi), which is contained in U. Let A0 := integral over B_{2 t0}(xi) of |H|^p dmu < infinity (V.LocallyLp H p) and Lambda := min{omega_n, 1}/100, so 0 < Lambda <= 1/100 and Lambda/omega_n <= 1/100. For y in B_{t0}(xi) and 0 < R' <= t0, B_{R'}(y) is contained in B_{2 t0}(xi), so (R'^{p-n} integral over B_{R'}(y) of |H|^p dmu)^{1/p} <= R'^{1 - n/p} A0^{1/p}. Choose t in (0, t0] with (a) t^{1 - n/p} A0^{1/p} <= kappa Lambda (possible since 1 - n/p > 0) and (b) mu(B_sigma(xi)) <= (11/10) omega_n sigma^n for all 0 < sigma <= 2t (possible since V.HasDensity xi 1). Let d0 := t/(100 n) and let y in U with d := |y - xi| <= d0. Then Bo_t(y) and B_t(y) are contained in B_{2 t0}(xi), contained in Bo_R(xi) (2 t0 <= R/2), contained in U, so by (a) and (TP) the hypotheses of (M) hold at y with R' := t and this Lambda. For 0 < r < t: omega_n Theta(y) <= Phi(r) (Phi nondecreasing, omega_n Theta(y) = lim at 0) <= e^{Lambda} r^{-n} mu(B_r(y)) + Lambda (F <= e^{Lambda}, F - 1 <= Lambda) <= e^{Lambda} r^{-n} mu(B_{r+d}(xi)) + Lambda (B_r(y) is contained in B_{r+d}(xi)) <= e^{Lambda} (11/10) omega_n (1 + d/r)^n + Lambda (by (b), as r + d <= 2t). Letting r -> t-: Theta(y) <= e^{Lambda} (11/10)(1 + d/t)^n + Lambda/omega_n <= e^{1/100} (11/10)(1 + 1/(100 n))^n + 1/100 <= e^{1/50} (11/10) + 1/100 < 1.14 < 2, using (1 + 1/(100n))^n <= e^{1/100}. (The additive error Lambda is divided by omega_n; this is why Lambda <= omega_n/100 was imposed.)

8. Choice of s and multiplicity one. Let s := min{R1, d0}. Then s > 0, s <= R1 < R, and Bo_s(xi) is contained in B1 and in {y : |y - xi| <= d0}. For mu-a.e. y in Bo_s(xi): theta(y) is a positive integer (hypothesis), Theta(y) = theta(y) (step 4) and Theta(y) < 2 (step 7; both are the limit of mu(B_r(y))/(omega_n r^n)). Hence theta(y) = 1. This proves: for mu-a.e. x, x in ball xi s implies V.mult x = 1.

9. Symmetric difference on ball xi s. (M cap Bo_s(xi)) symmetric-difference (Sigma cap Bo_s(xi)) equals ((M cap B1) symmetric-difference (Sigma cap B1)) cap Bo_s(xi), which is H^n-null by step 6.

10. Weight on ball xi s. By step 8 the set N := {x in M cap Bo_s(xi) : theta(x) != 1} is mu-null; choose a measurable mu-null set N' containing N. Then H^n(N' cap M) = 0 (by (F2), as theta > 0 on M), so theta = 1 H^n-a.e. on M cap Bo_s(xi). For Borel S: mu(S cap Bo_s(xi)) = integral over S cap Bo_s(xi) cap M of theta dH^n = H^n(S cap Bo_s(xi) cap M) = H^n(S cap Bo_s(xi) cap Sigma), the last equality by step 9 (the two sets differ by an H^n-null set). Hence V.weight.restrict (ball xi s) = (muHE[n]).restrict (V.support cap ball xi s) (two measures agreeing on Borel sets).

11. Density one on Sigma cap ball xi s. Let y in Bo_s(xi) cap Sigma. For 0 < r < s - |y - xi|, B_r(y) is contained in Bo_s(xi), contained in B1, so by step 10 mu(B_r(y)) = H^n(Sigma cap B_r(y)) = nu(B_r(y)), and step 2 gives mu(B_r(y))/(omega_n r^n) -> 1, i.e. V.HasDensity y 1.

12. Carrier versus graph on ball 0 rho. Let 0 < rho <= s and W_rho := {x in Bo^n_rho(0) : |G(x)| < rho}. (a) Q((M - xi)) cap Bo_rho(0) = T(M) cap Bo_rho(0) = T(M cap Bo_rho(xi)) since T is a bijection with T^{-1}(Bo_rho(0)) = Bo_rho(xi). (b) graphOver u W_rho = G(W_rho) = Gamma cap Bo_rho(0): if x in Bo^n_R(0) and |G(x)| < rho then |x| <= |G(x)| < rho, and Bo^n_rho(0) is contained in Bo^n_R(0) because rho <= s < R. By the graph hypothesis, Gamma cap Bo_rho(0) = Gamma cap Bo_R(0) cap Bo_rho(0) = T(Sigma) cap Bo_rho(0) = T(Sigma cap Bo_rho(xi)). (c) T is injective, so T(X) symmetric-difference T(Y) = T(X symmetric-difference Y). (d) By (Iso), H^n of the symmetric difference in the claim equals H^n((M cap Bo_rho(xi)) symmetric-difference (Sigma cap Bo_rho(xi))), which is at most H^n((M cap Bo_s(xi)) symmetric-difference (Sigma cap Bo_s(xi))) = 0 (step 9; intersect with the smaller ball). This is the last conjunct.

Steps 8-12 give s > 0 with s <= R and all five asserted properties.

## Key steps

1. finite graph piece Gamma1 in B1 = open B_{R/2}(xi) and nu := H^n restricted to Gamma1
2. density of nu at graph points from dohr_c1_graph_density_one
3. mu restricted to B1 equals theta 1_M nu
4. Besicovitch differentiation: Theta = theta mu-a.e. on B1
5. Theta >= 1 on Gamma1 via monotonicity at nearby points (dohr_local_monotonicity, tangent planes from dohr_graph_tangent_planes)
6. carrier and support differ by an H^n-null set
7. monotonicity with kappa = (p-n)/(4p) and Lambda <= omega_n/100 gives Theta < 2 near xi
8. theta integer with Theta = theta < 2 forces theta = 1
9. measure identity, density one on spt V, and transport of the null symmetric difference

## Reference use

### local-project

Queries:
- `rg -l 'dohr_' <snapshot> .lake/packages/simongmt GMT .humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json .humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes`
- `rg -n '^import' <snapshot>/project/GMT/Ch05/Contract.lean`
- `lean /tmp/dohr-check/src/T1.lean (#check ContinuousLinearMap.adjoint and LinearMap.normDet after import GMT.Ch05.Submission)`
- `rg -n 'theorem ae_tendsto_rnDeriv \(' <snapshot>/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `rg -n 'lemma measure_compl_support :' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `rg -n 'theorem hausdorffMeasure_image \(e : X ≃ᵢ Y\)|theorem hausdorffMeasure_homothety_image' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `for pat in Schauder Campanato 'difference quotient' '[Vv]arifold' 'Legendre-Hadamard'; do rg -l "$pat" <snapshot>/mathlib/Mathlib | wc -l; done`
- `grep -rn 'def normDet' .lake/packages/mathlib/Mathlib`
- `grep -n 'HasWeightedApproximateTangentSpaceAt' -r .lake/packages/simongmt/Poincare/SimonGMT`
- `grep -n 'theorem injective_area_formula_lipschitzOn' -A 12 .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `grep -rn 'def areaJacobianAt' .lake/packages/simongmt/Poincare/SimonGMT/Chapter02`
- `rg -n 'def lpMeanCurvatureKappa' .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpMeanCurvature.lean`
- `lake env lean -o /tmp/dohr-check/build/GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean`
- `lake env bash -c 'LEAN_PATH=$LEAN_PATH:/tmp/dohr-check/build lean /tmp/dohr-check/final/Children.lean'`
- `lake env bash -c 'LEAN_PATH=$LEAN_PATH:/tmp/dohr-check/build lean /tmp/dohr-check/final/Assembly.lean'`
- `lake env bash -c 'LEAN_PATH=$LEAN_PATH:/tmp/dohr-check/build lean /tmp/dohr-check/final/Glue.lean'`
- `grep -n '7.1|Schauder' book/chapter-05.txt; sed -n 455,575p book/chapter-04.txt; sed -n 595,724p book/chapter-01.txt`
- `python3 -I /tmp/dohr-scripts/pdftext.py gm.pdf gm.txt, then regex search for 'Theorem 5.19', 'Theorem 5.20', 'Proposition 8.6', 'Theorem 4.9', '(8.5)', '(3.17)' in the Giaquinta-Martinazzi text (https://www2.karlin.mff.cuni.cz/~kaplicky/pages/pages/2020z/gm.pdf)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpMeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpLowerDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/tmp/dohr-check/final/Children.lean`
- `/tmp/dohr-check/final/Assembly.lean`
- `/tmp/dohr-check/final/Glue.lean`
- `/tmp/dohr-check/final/stmts.json`
- `/tmp/dohr-scripts/gm.txt`

Pinned snapshot (manifest.json): project ea5607598f3133b40a13241f2e51517a8c6423cd, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The snapshot Contract.lean is byte-identical to the workspace copy. No prior proof or 'dohr_' name exists in the snapshot, simongmt, GMT/ or the DAG (rg returns no matches), so all 9 proposed names are free.

The contract's imports reach neither ContinuousLinearMap.adjoint nor LinearMap.normDet (Lean reports 'Unknown constant'). The graph area element is therefore written as sqrt(Matrix.det (1 + Gram matrix)). Lean examples confirm that 1 is the identity matrix and + is entrywise.

Usable Mathlib items: Besicovitch.ae_tendsto_rnDeriv (Besicovitch.lean:1078), VitaliFamily differentiation (Differentiation.lean), Measure.measure_compl_support (Support.lean:202), and IsometryEquiv.hausdorffMeasure_image / hausdorffMeasure_homothety_image (Hausdorff.lean:845, 1060).

Mathlib has no Schauder, Campanato, Legendre-Hadamard or varifold theory: 'Schauder' matches only Schauder-basis files, the other patterns match nothing, and 'difference quotient' matches only UniformLimitsDeriv.lean.

simongmt provides HasWeightedApproximateTangentSpaceAt and its .unique (Chapter03/Rectifiable.lean:330, 345), injective_area_formula_lipschitzOn (Chapter02/AreaDomain.lean:147), areaJacobianAt = normDet of the derivative (Chapter02/Area.lean:26), and lpMeanCurvatureKappa = (p-n)/(4p) (Chapter04/LpMeanCurvature.lean:76). Its Chapter 4 monotonicity is stated only for the stronger Chapter04.RectifiableVarifold, hence the local monotonicity and tangent-plane children.

Lean checks with the pinned toolchain against a compiled scratch GMT.Ch05.Submission:
- all 9 child statements elaborate (Children.lean);
- Assembly.lean proves DensityOneHigherRegularity from them and allard_regularity_theorem with no sorry of its own (axioms: propext, sorryAx, Classical.choice, Quot.sound);
- Glue.lean confirms that the measurability conjunct restricts to sub-balls.

Book: Theorem 7.1 and its proof are at chapter-05.txt l.1312-1366, monotonicity 4.1-4.10 at chapter-04.txt l.455-575, and comparison/density theorems at chapter-01.txt 3.3-3.6.

Giaquinta-Martinazzi (2nd ed., 2012), extracted text, confirms: Theorem 5.19 (Hoelder coefficients and C^{0,sigma} data give Du in C^{0,sigma}_loc), Theorem 5.20 (C^{k+1,sigma}_loc for k >= 1), Proposition 8.6 (difference quotients for D_alpha A(Du) = 0 under (8.5)), Theorem 4.9, and Definition 3.36 / Remark 3.37 (Legendre implies Legendre-Hadamard).
