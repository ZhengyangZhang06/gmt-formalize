# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.allard_graph-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 2 of the parent-supplied proof, i.e. the first paragraph of Simon's printed proof of Theorem 7.1 (Ch. 5, p. 127): 'Since the scaled L^p norm of H tends to 0 and omega_n^{-1} rho^{-n} mu_V(B_rho(xi)) tends to 1, we can choose rho > 0 such that the hypotheses of Theorem 5.2 hold, so, after applying the appropriate translation and orthogonal transformation, the required u exists with graph u = spt V cap B_{gamma rho}(0)'. Uses the hypothesis AllardRegularityTheorem (Simon 5.2) and the sibling dohr_translate_varifold. Notation: mu := V.weight, theta := V.mult, omega_n := unitBallVolume n > 0, balls closed unless called open, beta := 1 - n/p.

1. Constants. Apply AllardRegularityTheorem to n, l (1 <= n) and p (n < p): there are delta0 in (0,1), gamma in (0,1) and C such that, for every open U0, every varifold V0 in U0, every H0, and all delta, rho with 0 < delta <= delta0 and V0.AllardHypotheses H0 p delta rho, AllardConclusion V0 p delta rho gamma C holds. Put delta := delta0. Note 0 < beta < 1.

2. Translation. Let tau(x) := x - xi. By dohr_translate_varifold there is a varifold V' in U' := tau(U) with V'.mult y = theta(y + xi), mu' := V'.weight = mu.map tau, V'.support = tau(V.support), and, because V has generalized mean curvature H in U, V' has generalized mean curvature H' := H(. + xi) in U'. U' is open since tau is a homeomorphism. Because tau is a measurable equivalence, mu'(S) = mu(tau^{-1}(S)) for Borel S and integral of g dmu' = integral of g(tau x) dmu(x) for Borel g >= 0; in particular mu'(B_r(0)) = mu(B_r(xi)) and integral over B_r(0) of ||H'||_e^p dmu' = integral over B_r(xi) of ||H||_e^p dmu.

3. Choice of the scale rho. Since U is open and xi in U, fix r0 > 0 with B_{r0}(xi) contained in U, and put L := integral over B_{r0}(xi) of ||H||_e^p dmu, which is finite by V.LocallyLp H p (B_{r0}(xi) is a compact subset of U). V.HasDensity xi 1 says mu(B_r(xi)) / (omega_n r^n) -> 1 as r decreases to 0. Hence we may choose rho in (0, r0] such that for every r in (0, rho]: (a) 0 < mu(B_r(xi)) <= (1 + delta) omega_n r^n; and moreover (b) rho^beta L^{1/p} <= delta (possible because beta > 0, so rho^beta -> 0).

4. xi lies in spt V. xi is in U. If N is an open set containing xi, then B_r(xi) is contained in N for some r in (0, rho], so mu(N) >= mu(B_r(xi)) > 0 by 3(a); hence xi is in spt mu and so in V.support. Therefore 0 = tau(xi) belongs to tau(V.support) = V'.support.

5. Allard hypotheses for V' at (p, delta, rho). (i) rho > 0. (ii) V' has generalized mean curvature H' in U' (step 2). (iii) theta' >= 1 mu'-a.e.: since mu' is the image of mu under the measurable equivalence tau, 'for mu'-a.e. y, 1 <= V'.mult y' is equivalent to 'for mu-a.e. x, 1 <= V'.mult(tau x) = theta(x)', which is a hypothesis. (iv) 0 is in V'.support (step 4). (v) B_rho(0) = tau(B_rho(xi)) is contained in tau(U) = U'. (vi) mu'(B_rho(0)) = mu(B_rho(xi)) <= ofReal((1 + delta) omega_n rho^n) by 3(a). (vii) integral over B_rho(0) of ||H'||_e^p dmu' = integral over B_rho(xi) of ||H||_e^p dmu <= L (B_rho(xi) is contained in B_{r0}(xi)), so (rho^{p-n} * that integral)^{1/p} <= (rho^{p-n})^{1/p} L^{1/p} = rho^beta L^{1/p} <= delta by 3(b); i.e. V'.scaledLpNorm H' p 0 rho <= ofReal(delta). Thus V'.AllardHypotheses H' p delta rho holds with 0 < delta <= delta0, and step 1 gives AllardConclusion V' p delta rho gamma C.

6. Unpacking the conclusion. Put R := gamma rho > 0 and Bbar := closed ball B^n_R(0) in R^n. There are a linear isometry q of R^(n+l) and u : R^n -> R^l with u C^1 on Bbar (ContDiffOn on the closed ball), u(0) = 0, D_Bbar u(0) = 0 (derivative within Bbar), V'.support cap B_R(0) = q(graph of u over Bbar) cap B_R(0) (closed balls), and rho^{-1} sup_Bbar |u| + sup_Bbar |D_Bbar u|_HS + rho^beta sup_{x != y in Bbar} |D_Bbar u(x) - D_Bbar u(y)|_HS / |x - y|^beta <= C delta^{1/(2n+2)} < infinity (sums of suprema in [0, infinity]). Set Q := q^{-1}, again a linear isometry. Since R < rho <= r0, closed B_R(xi) is contained in closed B_rho(xi), which is contained in U.

7. Regularity on the open ball B := open B^n_R(0). B is open and contained in Bbar, so u is C^1 on B. For x in B the closed ball Bbar is a neighbourhood of x, hence the derivative within Bbar equals the derivative: D_Bbar u(x) = Du(x) (fderivWithin of a neighbourhood equals fderiv). In particular fderiv u 0 = 0, because 0 is in B.

8. Hoelder bound. The third summand in step 6 is finite and rho^beta > 0, so K := sup_{x != y in Bbar} |D_Bbar u(x) - D_Bbar u(y)|_HS / |x - y|^beta is a finite real number >= 0. For x != y in B, using step 7 and the inequality ||A||_op <= |A|_HS (for v = sum v_i e_i, |Av| <= sum |v_i| |A e_i| <= |v| (sum |A e_i|^2)^{1/2} by Cauchy-Schwarz) we get ||Du(x) - Du(y)|| <= K |x - y|^beta. For x = y both sides are 0 because beta > 0. Hence there is K with ||fderiv u x - fderiv u y|| <= K ||x - y||^(1 - n/p) for all x, y in B.

9. Graph identity on the open ball. Q is a bijective linear isometry with Q(closed B_R(0)) = closed B_R(0); applying Q to the identity of step 6 gives Q(V'.support) cap closed B_R(0) = graph of u over Bbar cap closed B_R(0). Intersecting both sides with the open ball B_R(0) (contained in the closed ball) gives Q(V'.support) cap B_R(0) = graph of u over Bbar cap B_R(0). Since |(x, u(x))|^2 = |x|^2 + |u(x)|^2 >= |x|^2, a graph point (x, u(x)) in the open ball B_R(0) has |x| < R, i.e. x in B; hence graph of u over Bbar cap B_R(0) = graph of u over B cap B_R(0). Finally V'.support = tau(V.support), so Q '' ((fun x => x - xi) '' V.support) cap ball 0 R = graphOver u (ball 0 R) cap ball 0 R.

Steps 6-9 give R > 0, Q, u with closed B_R(xi) contained in U, u C^1 on ball 0 R, u(0) = 0, fderiv u 0 = 0, the (1 - n/p)-Hoelder bound for fderiv u on ball 0 R, and the graph identity, as claimed.

## Key steps

1. Allard constants delta0, gamma, C for (n, l, p); take delta := delta0
2. translate V by -xi with dohr_translate_varifold
3. choose rho with mass ratio <= 1 + delta and scaled L^p norm <= delta
4. xi lies in spt V, so the Allard hypotheses hold for V' at (p, delta, rho)
5. unpack AllardConclusion with R := gamma rho and Q := q^{-1}
6. on the open ball: u is C^1, Du(0) = 0, Hoelder bound since operator norm <= Hilbert-Schmidt norm
7. rotate the support identity and pass from closed to open balls

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
