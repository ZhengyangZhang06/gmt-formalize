# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.c1_graph_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the last sentence of Step 3 of the parent-supplied proof ('the H^n-density of a C^1 graph is 1 at each of its points'; Simon p. 128: 'graph u is a C^1 submanifold so then Theta^n(mu_V, x) = 1 at every point of graph u'), proved from the area formula. Notation: G(x) := graphPoint x (u x) = (x, u(x)); Gamma := G(open B^n_R(0)); x0 in open B^n_R(0) (so R > 0); y0 := G(x0); P0 := Du(x0); L := DG(x0), i.e. L v = (v, P0 v); H^n := muHE[n]; omega_n := unitBallVolume n = L^n(unit ball of R^n) > 0. For a linear P : R^n -> R^l let J(P) := (det(I_n + (<P e_a, P e_b>)_{a,b}))^{1/2}; this is >= 1 and continuous in P, and J(Du(x)) = normDet(DG(x)) is the area Jacobian of G at x, because DG(x)^T DG(x) = I_n + Du(x)^T Du(x). Put J0 := J(P0) = normDet(L).

Facts used. (A1) Area formula for maps that are injective and Lipschitz on a set: if G is injective and Lipschitz on a closed ball D' contained in Bo^n_R(0) and S is a Borel subset of D', then H^n(G(S)) = integral over S of J(Du(x)) dx. (Apply simongmt Chapter02.injective_area_formula_lipschitzOn (AreaDomain.lean, Mathlib normalization H^n = L^n on R^n) with s := S; by simongmt ae_fderivWithin_eq_of_lipschitz_extension, applied to a Lipschitz extension of G from D' that coincides with G on D', the within-derivative of G on S equals the derivative of the extension a.e. on S, and at every interior point of D' this derivative is DG(x); the boundary sphere of D' is Lebesgue-null, so areaJacobianWithin G S x = normDet DG(x) = J(Du(x)) for a.e. x in S.) (A2) Linear area formula: for injective linear L : R^n -> R^(n+l) and Borel S, H^n(L(S)) = normDet(L) L^n(S); and H^n restricted to the n-plane L(R^n) is n-dimensional Lebesgue measure, so H^n(L(R^n) cap closed B_t(0)) = omega_n t^n.

1. For all x, x': |G(x) - G(x')| >= |x - x'| (compare first coordinates), and |L v|^2 = |v|^2 + |P0 v|^2 >= |v|^2.

2. Fix eps in (0, 1/2). Since Du is continuous at x0 and J is continuous, choose eta > 0 with closed B^n_eta(x0) contained in open B^n_R(0), ||Du(x) - P0|| <= eps and |J(Du(x)) - J0| <= eps J0 for |x - x0| <= eta. On the convex ball closed B_eta(x0), Du is bounded, so u (hence G) is Lipschitz there, and by the mean value inequality |G(x) - y0 - L(x - x0)| = |u(x) - u(x0) - P0(x - x0)| <= eps |x - x0| <= eps |L(x - x0)|.

3. Consequently (1 - eps)|L(x - x0)| <= |G(x) - y0| <= (1 + eps)|L(x - x0)| for x in closed B_eta(x0).

4. Localization and sandwich. Let 0 < r <= (1 - eps) eta. Put D_r := {x in open B^n_R(0) : |G(x) - y0| <= r}. By step 1, D_r is contained in closed B_r(x0), which is contained in closed B_eta(x0); D_r is closed (preimage of a closed ball under G restricted to the closed ball), hence Borel, and Gamma cap closed B_r(y0) = G(D_r). With E_t := {x : |L(x - x0)| <= t} (contained in closed B_t(x0) by step 1), step 3 gives E_{r/(1+eps)} contained in D_r contained in E_{r/(1-eps)}, all inside closed B_eta(x0).

5. Volume of the ellipsoids. L maps E_t - x0 bijectively onto L(R^n) cap closed B_t(0), so by (A2), J0 L^n(E_t) = H^n(L(R^n) cap closed B_t(0)) = omega_n t^n, i.e. L^n(E_t) = omega_n t^n / J0.

6. By (A1) on closed B_eta(x0) (G injective and Lipschitz there) and step 2: H^n(Gamma cap closed B_r(y0)) = integral over D_r of J(Du) dx, which is >= (1 - eps) J0 L^n(E_{r/(1+eps)}) = (1 - eps)(1 + eps)^{-n} omega_n r^n and <= (1 + eps) J0 L^n(E_{r/(1-eps)}) = (1 + eps)(1 - eps)^{-n} omega_n r^n.

7. Hence for 0 < r <= (1 - eps) eta: (1 - eps)(1 + eps)^{-n} <= H^n(graphOver u (ball 0 R) cap closedBall (graphPoint x0 (u x0)) r) / (omega_n r^n) <= (1 + eps)(1 - eps)^{-n}. Both bounds tend to 1 as eps -> 0 and eps was arbitrary, so the quotient (an extended-real quotient by ofReal(omega_n r^n) > 0, with finite numerator) tends to 1 as r decreases to 0, which is the claim.

## Key steps

1. fix eps and eta with |Du - Du(x0)| <= eps and |J(Du) - J0| <= eps J0 near x0
2. (1 - eps)|L(x - x0)| <= |G(x) - G(x0)| <= (1 + eps)|L(x - x0)|
3. sandwich the parameter set between ellipsoids E_{r/(1+eps)} and E_{r/(1-eps)}
4. L^n(E_t) = omega_n t^n / J0 by the linear area formula
5. area formula bounds, then let eps -> 0

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
