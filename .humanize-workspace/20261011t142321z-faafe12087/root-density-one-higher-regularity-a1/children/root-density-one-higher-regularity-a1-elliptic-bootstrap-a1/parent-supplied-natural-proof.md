# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 5 of the parent-supplied proof (Simon, Ch. 5, proof of Theorem 7.1, p. 128: 'Then by the Schauder theory for elliptic equations we see that h in C^{q,alpha} implies u in C^{q+2,alpha}'), with the Schauder step made explicit as in the parent. References: M. Giaquinta and L. Martinazzi, An Introduction to the Regularity Theory for Elliptic Systems, Harmonic Maps and Minimal Graphs, 2nd ed., Edizioni della Normale, 2012 [GM]: Definition 3.36 (Legendre condition (3.16), Legendre-Hadamard condition (3.17)) and Remark 3.37 (Legendre implies Legendre-Hadamard); Section 4.3 (difference quotients: Definition 4.6, Proposition 4.8, Theorem 4.9); Proposition 8.6 (difference-quotient differentiation of a nonlinear system D_alpha(A^alpha_i(Du)) = 0, giving u in W^{2,2}_loc and the differentiated system), whose model proof Theorem 8.7 combines with Theorems 5.17, 5.19, 5.20; Theorem 5.19 (if v in W^{1,2}_loc solves D_alpha(A^{alpha beta}_{ij} D_beta v^j) = -D_alpha F^alpha_i with A in C^{0,sigma}_loc satisfying (3.17) and F in C^{0,sigma}_loc, sigma in (0,1), then Dv in C^{0,sigma}_loc); Theorem 5.20 (same system with k >= 1, A in C^{k,sigma}_loc, F in C^{k,sigma}_loc and lower-order term f in C^{k-1,sigma}_loc: then v in C^{k+1,sigma}_loc).

Notation. Omega := Bo^n_r(0) (open ball), G(x) := (x, u(x)) = graphPoint x (u x). For linear P : R^n -> R^l, |P| is the Hilbert-Schmidt norm (||P||_op <= |P| <= sqrt(n) ||P||_op), g(P)_{ab} := delta_{ab} + <P e_a, P e_b> and J(P) := det(g(P))^{1/2}, the inline expression of the statement. g(P) >= I, so det g(P) >= 1 and J is C-infinity (indeed real-analytic) on L(R^n, R^l). A(P) := DJ(P) (a linear form on L(R^n, R^l)) and B(P) := D^2 J(P) (a symmetric bilinear form). Since det(I + S) = 1 + trace S + O(|S|^2) and trace(P^T P) = |P|^2, J(P) = 1 + |P|^2/2 + O(|P|^4); hence A(0) = 0 and B(0)[Psi, Psi] = |Psi|^2. Write F_v(z) := (F^{n+1}(z), ..., F^{n+l}(z)) for the last l components of F, so that <graphPoint 0 w, F(z)> = w . F_v(z). The hypothesis is the weak system
 (E) integral over Omega of A(Du)[Dphi] dx = - integral over Omega of g_rhs . phi dx for all phi in C^1_c(Omega; R^l) with tsupport in Omega, where g_rhs(x) := J(Du(x)) F_v(G(x)).
In coordinates A(Du)[Dphi] = sum_{j,a} A_{ja}(Du) D_a phi^j, i.e. (E) says sum_a D_a(A_{ja}(Du)) = g_rhs_j weakly, the system (2) of Simon p. 128.

1. Ellipticity near 0. By continuity of B and B(0)[Psi, Psi] = |Psi|^2, choose eps0 in (0, 1] such that for |P| <= eps0: B(P)[Psi, Psi] >= |Psi|^2/2 and |B(P)| <= 2 (the Legendre condition (3.16) of [GM] with constant 1/2). Du is continuous on Omega with Du(0) = 0 (u is C^1 on Omega, fderiv u 0 = 0), so choose r1 in (0, r) with |Du(x)| <= eps0 for |x| <= r1. Put Omega1 := Bo^n_{r1}(0); its closure is a compact subset of Omega.

2. Data on the closure of Omega1. (a) By hypothesis ||Du(x) - Du(y)|| <= K|x - y|^beta on Omega with alpha <= beta <= 1, and |x - y|^beta <= (2 r1)^{beta - alpha} |x - y|^alpha on Omega1, so Du is alpha-Hoelder on Omega1 (and on its closure by continuity), and |Du| <= eps0 there. (b) G is Lipschitz on the closure of Omega1 and G(closure of Omega1) is a compact subset of O (G maps Omega into O). F_v is alpha-Hoelder on compact subsets of O: for q = 0 this is the Hoelder part of IsLocallyHolderCkα 0 alpha F O; for q >= 1, F is C^1 on the open set O, hence Lipschitz on a compact neighbourhood of each compact set, which gives an alpha-Hoelder bound (short distances by the Lipschitz bound, long distances by 2 sup|F| / delta^alpha). Hence F_v o G is alpha-Hoelder on Omega1. (c) J and B are smooth, hence Lipschitz on {|P| <= eps0}, so J o Du and a(x) := B(Du(x)) are alpha-Hoelder on Omega1. Hence g_rhs = (J o Du)(F_v o G) is in C^{0,alpha}(closure of Omega1), and the coefficients a are in C^{0,alpha}(closure of Omega1) and satisfy the Legendre condition with constant 1/2, hence (Remark 3.37 of [GM]) the Legendre-Hadamard condition (3.17).

3. Difference quotients ([GM] Proposition 8.6 and Section 4.3, with the right-hand side of (E)). Fix k in {1, ..., n}, open Omega' with compact closure in Omega1, and 0 < |d| < dist(Omega', boundary of Omega1). For zeta in C^1_c(Omega'; R^l), testing (E) with zeta(. - d e_k) and with zeta and subtracting gives integral of [A(Du(x + d e_k)) - A(Du(x))][Dzeta(x)] dx = - integral of [g_rhs(x + d e_k) - g_rhs(x)] . zeta(x) dx. Write A(Du(x + d e_k)) - A(Du(x)) = d a_d(x)[D w_d(x), .] with w_d := (u(. + d e_k) - u)/d and a_d(x) := integral over t in [0,1] of B(Du(x) + t(Du(x + d e_k) - Du(x))) dt; the segment stays in {|P| <= eps0} (convex), so a_d satisfies the Legendre condition with constant 1/2 and |a_d| <= 2. Dividing by d and moving the difference quotient onto zeta: integral of a_d[D w_d, D zeta] dx = integral of g_rhs . Delta_{-d} zeta dx, with Delta_{-d} zeta(x) := (zeta(x - d e_k) - zeta(x))/(-d). Testing with zeta := eta^2 w_d (eta a cutoff equal to 1 on Omega'' compactly contained in Omega') and using |integral of g_rhs . Delta_{-d} zeta| <= ||g_rhs||_{L^2} ||Delta_{-d} zeta||_{L^2} <= c ||g_rhs||_{L^2} ||D zeta||_{L^2} and ||w_d||_{L^2(Omega')} <= c ||Du||_{L^2(Omega1)} ([GM] Proposition 4.8(i)), the Legendre condition and Young's inequality give sup over d of ||D w_d||_{L^2(Omega'')} < infinity. By [GM] Proposition 4.8(ii), D_k u is in W^{1,2}(Omega''), and along a sequence d_j -> 0 the gradients D w_{d_j} converge weakly in L^2(Omega'') to D(D_k u). Passing to the limit along this sequence (a_{d_j} -> a uniformly on supp zeta, so a_{d_j} D zeta -> a D zeta strongly in L^2, and Delta_{-d_j} zeta -> D_k zeta uniformly) yields, for v := D_k u in W^{1,2}_loc(Omega1; R^l),
 (D_k) integral of a(x)[Dv, Dzeta] dx = integral of g_rhs . D_k zeta dx for all zeta in C^1_c(Omega1; R^l),
i.e. sum_a D_a(sum_{i,b} a_{ja}^{ib} D_b v^i) = D_a(delta_{ak} g_rhs_j) weakly: the system (5.29) of [GM] with coefficients a and F^alpha_j := -delta_{alpha k} g_rhs_j. Thus u is in W^{2,2}_loc(Omega1).

4. C^{2,alpha}. By step 2 the coefficients of (D_k) are in C^{0,alpha} and satisfy (3.17), and F is in C^{0,alpha}; [GM] Theorem 5.19 (sigma := alpha in (0,1)) gives D(D_k u) in C^{0,alpha}_loc(Omega1) for every k. A W^{1,2}_loc function whose weak gradient is continuous is C^1 with that gradient, so D_k u is C^1 and D^2 u is in C^{0,alpha}_loc(Omega1): u is in C^{2,alpha}_loc(Omega1).

5. Induction. Claim: u is in C^{m+2,alpha}_loc(Omega1) for m = 0, ..., q. The case m = 0 is step 4. Let 1 <= m <= q and assume u in C^{m+1,alpha}_loc(Omega1). Then Du is in C^{m,alpha}_loc, so a = B o Du and J o Du are in C^{m,alpha}_loc (composition of a C-infinity map with a C^{m,alpha}_loc map). G = (id, u) is in C^{m+1,alpha}_loc (in particular C^1) with values in O, and F_v is in C^{q,alpha}_loc(O), contained in C^{m,alpha}_loc(O) since m <= q; for m >= 1 the chain rule (Faa di Bruno) and the product rule for Hoelder functions give F_v o G in C^{m,alpha}_loc(Omega1). Products of C^{m,alpha}_loc functions are C^{m,alpha}_loc, so g_rhs is in C^{m,alpha}_loc(Omega1). [GM] Theorem 5.20, applied to (D_k) with its order parameter (called k in [GM]) equal to m >= 1, coefficients a in C^{m,alpha}_loc satisfying (3.17), F^alpha_j = -delta_{alpha k} g_rhs_j in C^{m,alpha}_loc and f = 0, gives v = D_k u in C^{m+1,alpha}_loc(Omega1) for every direction k = 1, ..., n, i.e. u in C^{m+2,alpha}_loc(Omega1). After m = q: u is in C^{q+2,alpha}_loc(Omega1).

6. Conclusion. Put r' := r1/2, so 0 < r' <= r and the closed ball B^n_{r'}(0) is a compact subset of Omega1. On the open ball Bo^n_{r'}(0), u is C^{q+2} (ContDiffOn (q+2)), and iteratedFDeriv u agrees there with the classical derivatives. Each D^i u (i <= q+2) is continuous on the compact closed ball, hence bounded there; take B as the maximum of these bounds. D^{q+2} u is alpha-Hoelder on the compact closed ball (step 5), hence on the open ball with a finite constant. All norms on multilinear maps are equivalent, so these are the three conditions of IsHolderCkα (q + 2) alpha u (ball 0 r'). This gives r' > 0 with r' <= r and IsHolderCkα (q + 2) alpha u (ball 0 r').

## Key steps

1. Legendre ellipticity of D^2 J near 0 and a small-gradient ball Omega1
2. the coefficients D^2 J(Du) and the right side J(Du) F_v(x, u) are C^{0,alpha}
3. difference quotients: u in W^{2,2}_loc and the differentiated system for D_k u
4. Schauder estimate (Giaquinta-Martinazzi Thm 5.19): u in C^{2,alpha}_loc
5. induction with Giaquinta-Martinazzi Thm 5.20 up to C^{q+2,alpha}_loc
6. global bounds on a smaller ball give IsHolderCkα (q + 2) alpha u (ball 0 r')

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
