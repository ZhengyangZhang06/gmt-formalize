# Parent-supplied natural-language proof

- Parent DAG node: `root.affine_approximation-a1`
- Child DAG node: `root.affine_approximation-a1.pinched_density_bounds-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 5, 2.4 ('by the monotonicity formula 4.7 and the semi-continuity 4.9 of Ch. 4 ...'), in the explicit form (P) of the parent proof, with the corrections: Lambda = delta/kappa, kappa = (p-n)/(4p), the bounds used only for delta <= delta_P(n,p), centres y in B_{3 delta rho}(0), and outer radius R = (1 - 4 delta) rho inside the ball B_{(1-3 delta) rho}(y), which lies in B_rho(0).

Notation (contract). mu := V.weight = theta H^n restricted to M (M = V.carrier, theta = V.mult); spt V := V.support = U cap spt mu; p_x := V.tangentProj x and p_x^perp v := v - p_x v; B_s(y) := closedBall y s (closed), B^o_s(y) := ball y s (open); omega_n := unitBallVolume n > 0; for z and s > 0, K(z,s) := V.scaledLpNorm H p z s = (s^(p-n) integral_{B_s(z)} |H|^p dmu)^(1/p) in [0,infinity]; kappa := (p-n)/(4p) > 0; g_y(x) := |x - y - p_x(x - y)|^2 / |x - y|^(n+2) (= 0 at x = y by the convention a/0 = 0).
(K-mono) If 0 < s <= t and B_s(z) is contained in B_t(w), then K(z,s) <= K(w,t): indeed s^(p-n) <= t^(p-n) (p > n), the integral of |H|^p over B_s(z) is at most that over B_t(w), and a -> a^(1/p) is monotone on [0,infinity].
(A) Under AllardHypotheses H p delta rho: rho > 0, V has generalized mean curvature H in U, theta >= 1 mu-a.e., 0 in spt V, B_rho(0) contained in U, mu(B_rho(0)) <= (1+delta) omega_n rho^n, and K(0,rho) <= delta; since rho^(p-n) > 0 the last bound gives integral_{B_rho(0)} |H|^p dmu < infinity, and by (K-mono) K(z,s) <= K(0,rho) <= delta whenever 0 < s <= rho and B_s(z) is contained in B_rho(0).

1. Constants. Let kappa := (p-n)/(4p), A := 1 + n 2^(n+4),
 C_+ := A + (9 e^2 2^n/4 + 2e/omega_n)/kappa, C_- := (1 + 1/omega_n)/kappa, C_c := e A + (9 e^2 2^n/8 + e/omega_n)/kappa,
 C_P := max{1, C_+, C_-, C_c}, delta_P := min{1/8, kappa, 1/(2 C_P)}.
These depend only on n, p, and C_P >= 1, 0 < delta_P <= 1/8, C_P delta_P <= 1/2.

2. Elementary inequalities. For t in [0, min{1/8, kappa}] put Lambda_t := t/kappa in [0,1] and a(t) := (1 + t)(1 - 4t)^(-n) (note 1 - 4t >= 1/2).
 (E1) For x in [0,1]: e^x <= 1 + x e^x <= 1 + e x and e^(2x) <= 1 + 2x e^(2x) <= 1 + 2 e^2 x (mean value theorem); e^(-x) >= 1 - x.
 (E2) For u in [0,1): (1 - u)^(-n) - 1 <= n u (1 - u)^(-n-1) (mean value theorem; the derivative n(1-v)^(-n-1) is increasing). With u = 4t <= 1/2: (1 - 4t)^(-n) <= 1 + n 2^(n+3) t, so a(t) <= (1 + t)(1 + n 2^(n+3) t) <= 1 + (1 + (9/8) n 2^(n+3)) t <= 1 + A t; also a(t) <= (9/8) 2^n.
 Put g_+(t) := e^(2 Lambda_t) a(t) + 2 e^(Lambda_t) Lambda_t/omega_n, g_-(t) := e^(-Lambda_t)(1 - Lambda_t/omega_n), g_c(t) := e^(Lambda_t)(e^(Lambda_t) a(t) - 1) + e^(Lambda_t) Lambda_t/omega_n.
 (E3) g_+(t) <= (1 + 2 e^2 Lambda_t) a(t) + 2 e Lambda_t/omega_n <= 1 + A t + 2 e^2 (9/8) 2^n Lambda_t + 2 e Lambda_t/omega_n = 1 + C_+ t <= 1 + C_P t.
 (E4) Let c := 1 - Lambda_t/omega_n <= 1. If c >= 0 then e^(-Lambda_t) c >= (1 - Lambda_t) c >= c - Lambda_t; if c < 0 then e^(-Lambda_t) c >= c >= c - Lambda_t. Hence g_-(t) >= 1 - Lambda_t - Lambda_t/omega_n = 1 - C_- t >= 1 - C_P t.
 (E5) e^(Lambda_t) a(t) - 1 <= (1 + e Lambda_t) a(t) - 1 <= A t + e (9/8) 2^n Lambda_t, which is >= 0; so e^(Lambda_t)(e^(Lambda_t) a(t) - 1) <= e (A t + (9e/8) 2^n Lambda_t) (if the bracket is negative the left side is negative), and g_c(t) <= e A t + (9 e^2 2^n/8) Lambda_t + e Lambda_t/omega_n = C_c t <= C_P t.

3. Setup and monotonicity. Let U, V, H, delta in (0, delta_P], rho with AllardHypotheses H p delta rho, y with |y| <= 3 delta rho, and s in (0, rho/2] be given. Then delta <= 1/8, delta <= kappa, and Lambda := delta/kappa in (0,1]. Put S := (1 - 3 delta) rho and R := (1 - 4 delta) rho; then rho/2 <= R < S, so s <= R, and B_S(y) is contained in B_rho(0) (|x| <= |y| + S <= rho), hence in U. By (A), integral_{B_S(y)} |H|^p dmu < infinity and K(y,R) <= K(0,rho) <= delta = kappa Lambda. aal_lp_monotonicity at (y, R, S, Lambda) gives F, G and Phi(t) := F(t) t^(-n) mu(B_t(y)) + F(t) - 1 on (0, R] with: e^(-Lambda) <= F <= e^Lambda, |F(t) - 1| <= Lambda (t/R)^(1-n/p) <= Lambda (Lambda <= 1), and, by (ii), Phi(t) - Phi(t') = G(t',t) integral_{B_t(y) minus B_t'(y)} g_y dmu >= 0 for 0 < t' <= t <= R with G in [e^(-Lambda), e^Lambda]; in particular Phi is nondecreasing on (0, R]. By (A), mu(B_R(y)) <= mu(B_rho(0)) <= (1 + delta) omega_n rho^n, so R^(-n) mu(B_R(y)) <= (1 + delta)(1 - 4 delta)^(-n) omega_n = a(delta) omega_n and
 Phi(R) <= e^Lambda a(delta) omega_n + Lambda. (3.1)

4. (P.i). F(s) s^(-n) mu(B_s(y)) = Phi(s) - (F(s) - 1) <= Phi(R) + Lambda <= e^Lambda a(delta) omega_n + 2 Lambda; dividing by F(s) >= e^(-Lambda), s^(-n) mu(B_s(y)) <= e^(2 Lambda) a(delta) omega_n + 2 e^Lambda Lambda = omega_n g_+(delta) <= (1 + C_P delta) omega_n by (E3) (t = delta). As mu(B_s(y)) < infinity this is the first assertion, in [0,infinity].

5. A lower bound for Phi if y in spt V. Assume y in spt V. Since |y| <= 3 delta rho <= 3 rho/8 < rho, y in spt V cap B^o_rho(0), so aal_density_ge_one gives, for every epsilon in (0,1), mu(B_u(y)) >= (1 - epsilon) omega_n u^n for all sufficiently small u > 0. Fix t in (0, R]. For such u <= t, using Phi(t) >= Phi(u) and F(u) >= 1 - Lambda (u/R)^(1-n/p) (which is >= 0 for small u),
 Phi(t) >= F(u) u^(-n) mu(B_u(y)) + F(u) - 1 >= (1 - Lambda (u/R)^(1-n/p))(1 - epsilon) omega_n - Lambda (u/R)^(1-n/p).
Letting u -> 0+ and then epsilon -> 0+ gives Phi(t) >= omega_n for every t in (0, R]. (5.1)

6. (P.ii). Assume y in spt V. For s in (0, R]: F(s) s^(-n) mu(B_s(y)) = Phi(s) - (F(s) - 1) >= omega_n - Lambda by (5.1). By (E4), e^(-Lambda)(1 - Lambda/omega_n) = g_-(delta) >= 1 - C_P delta >= 1/2 > 0, so omega_n - Lambda > 0; since F(s) <= e^Lambda, s^(-n) mu(B_s(y)) >= e^(-Lambda)(omega_n - Lambda) = omega_n g_-(delta) >= (1 - C_P delta) omega_n. Hence ofReal((1 - C_P delta) * (omega_n s^n)) <= mu(B_s(y)).

7. (P.iii). Assume y in spt V and let 0 < t < s (s <= R). By aal_lp_monotonicity (ii), g_y is integrable on B_s(y) minus B_t(y) and A(t) := integral_{B_s(y) minus B_t(y)} g_y dmu satisfies Phi(s) - Phi(t) = G(t,s) A(t) with G(t,s) >= e^(-Lambda). Hence, using Phi(s) <= Phi(R), (5.1) and (3.1),
 A(t) <= e^Lambda (Phi(s) - Phi(t)) <= e^Lambda (Phi(R) - omega_n) <= e^Lambda (e^Lambda a(delta) omega_n + Lambda - omega_n) = omega_n g_c(delta) <= C_P omega_n delta
(by (E5); if A(t) = 0 the bound A(t) <= C_P omega_n delta is trivial). Since g_y >= 0 and integrable on the annulus, integral^-_{B_s(y) minus B_t(y)} ofReal(g_y) dmu = ofReal(A(t)) <= ofReal(C_P omega_n delta). As t = s/k decreases to 0, the sets B_s(y) minus B_t(y) increase to B_s(y) minus {y}, so by monotone convergence integral^-_{B_s(y) minus {y}} ofReal(g_y) dmu <= ofReal(C_P omega_n delta). Finally g_y(y) = 0 (division by zero), so the integral over B_s(y) equals the integral over B_s(y) minus {y}: integral^-_{B_s(y)} ofReal(g_y) dmu <= ofReal(C_P * omega_n * delta). Steps 4, 6, 7 prove the statement for all s in (0, rho/2] (contained in (0, R]).

## Key steps

1. Explicit constants C_P, delta_P from elementary bounds g_+ <= 1 + C_P t, g_- >= 1 - C_P t, g_c <= C_P t on [0, min(1/8, kappa)].
2. Apply aal_lp_monotonicity at y with R = (1-4delta)rho, S = (1-3delta)rho, Lambda = delta/kappa <= 1; Phi nondecreasing, |F-1| <= Lambda.
3. (P.i): F(s)s^-n mu(B_s) <= Phi(R) + Lambda and mu(B_R(y)) <= (1+delta)omega_n rho^n.
4. For y in spt V: aal_density_ge_one and F -> 1 give Phi(t) >= omega_n for all t in (0,R].
5. (P.ii): s^-n mu(B_s) >= e^-Lambda(omega_n - Lambda) = omega_n g_-(delta).
6. (P.iii): annular integral <= e^Lambda(Phi(R) - omega_n) <= omega_n g_c(delta); monotone convergence as the inner radius -> 0.

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
