# Parent-supplied natural-language proof

- Parent DAG node: `root.affine_approximation-a1`
- Child DAG node: `root.affine_approximation-a1.mass_upper_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: correction (a) of the parent proof (step 1a): the mass bound of 2.4 is replaced, for all delta in (0, 1/4], by a bound obtained from the general error estimate (4.5) of Ch. 4, since Lambda = delta/kappa need not be small.

Notation (contract). mu := V.weight = theta H^n restricted to M (M = V.carrier, theta = V.mult); spt V := V.support = U cap spt mu; p_x := V.tangentProj x and p_x^perp v := v - p_x v; B_s(y) := closedBall y s (closed), B^o_s(y) := ball y s (open); omega_n := unitBallVolume n > 0; for z and s > 0, K(z,s) := V.scaledLpNorm H p z s = (s^(p-n) integral_{B_s(z)} |H|^p dmu)^(1/p) in [0,infinity]; kappa := (p-n)/(4p) > 0; g_y(x) := |x - y - p_x(x - y)|^2 / |x - y|^(n+2) (= 0 at x = y by the convention a/0 = 0).
(K-mono) If 0 < s <= t and B_s(z) is contained in B_t(w), then K(z,s) <= K(w,t): indeed s^(p-n) <= t^(p-n) (p > n), the integral of |H|^p over B_s(z) is at most that over B_t(w), and a -> a^(1/p) is monotone on [0,infinity].
(A) Under AllardHypotheses H p delta rho: rho > 0, V has generalized mean curvature H in U, theta >= 1 mu-a.e., 0 in spt V, B_rho(0) contained in U, mu(B_rho(0)) <= (1+delta) omega_n rho^n, and K(0,rho) <= delta; since rho^(p-n) > 0 the last bound gives integral_{B_rho(0)} |H|^p dmu < infinity, and by (K-mono) K(z,s) <= K(0,rho) <= delta whenever 0 < s <= rho and B_s(z) is contained in B_rho(0).

1. Constants. Put Lambda_1 := (1/4)/kappa = p/(p - n) and C_0 := e^(2 Lambda_1) ((3/2)^n (5/4) + e^(Lambda_1/2) Lambda_1/omega_n). C_0 > 0 depends only on n and p.

2. Setup. Let U, V, H, delta in (0, 1/4], rho with AllardHypotheses H p delta rho, y with |y| <= rho/4 and s in (0, rho/2] be given. Put Lambda := delta/kappa in (0, Lambda_1], R := 2 rho/3 and S := 3 rho/4. Then 0 < R < S and B_S(y) is contained in B_rho(0) (|x| <= |y| + S <= rho), hence in U. By (A), integral_{B_S(y)} |H|^p dmu <= integral_{B_rho(0)} |H|^p dmu < infinity, and K(y,R) <= K(0,rho) <= delta = kappa Lambda (R <= rho and B_R(y) is contained in B_rho(0)).

3. Monotonicity. aal_lp_monotonicity at (y, R, S, Lambda) gives F, G with Phi(t) := F(t) t^(-n) mu(B_t(y)) + F(t) - 1. Since s <= rho/2 < R, (ii) gives Phi(R) - Phi(s) = G(s,R) integral_{B_R(y) minus B_s(y)} g_y dmu >= 0. By (i), e^(-Lambda) <= F <= e^Lambda on (0, R] and |F(t) - 1| <= (1/2) e^(Lambda/2) Lambda (t/R)^(1-n/p) <= (1/2) e^(Lambda/2) Lambda for t in (0, R]. Hence
 F(s) s^(-n) mu(B_s(y)) = Phi(s) - (F(s) - 1) <= Phi(R) + |F(s) - 1| = F(R) R^(-n) mu(B_R(y)) + (F(R) - 1) + |F(s) - 1| <= e^Lambda R^(-n) mu(B_R(y)) + e^(Lambda/2) Lambda.

4. Conclusion. By (A) and delta <= 1/4, mu(B_R(y)) <= mu(B_rho(0)) <= (1 + delta) omega_n rho^n <= (5/4) omega_n rho^n, and R^(-n) rho^n = (3/2)^n. Dividing by F(s) >= e^(-Lambda):
 s^(-n) mu(B_s(y)) <= e^(2 Lambda) (3/2)^n (5/4) omega_n + e^(3 Lambda/2) Lambda <= omega_n e^(2 Lambda_1) ((3/2)^n (5/4) + e^(Lambda_1/2) Lambda_1/omega_n) = C_0 omega_n,
using Lambda <= Lambda_1 and e^(3 Lambda/2) Lambda <= e^(2 Lambda_1) e^(Lambda_1/2) Lambda_1. Hence mu(B_s(y)) <= C_0 omega_n s^n; as mu(B_s(y)) < infinity this is mu(B_s(y)) <= ofReal(C_0 * (omega_n s^n)) in [0,infinity].

## Key steps

1. Lambda := delta/kappa <= Lambda_1 = p/(p-n); C_0 := e^(2 Lambda_1)((3/2)^n(5/4) + e^(Lambda_1/2) Lambda_1/omega_n).
2. Apply aal_lp_monotonicity at y with R = 2rho/3, S = 3rho/4 (ball inside B_rho(0), K(y,R) <= delta).
3. Phi(s) <= Phi(R) and the general error bound |F - 1| <= (1/2)e^(Lambda/2)Lambda give F(s)s^-n mu(B_s) <= e^Lambda R^-n mu(B_R) + e^(Lambda/2)Lambda.
4. Use mu(B_R(y)) <= mu(B_rho(0)) <= (5/4)omega_n rho^n and F(s) >= e^-Lambda to get mu(B_s(y)) <= C_0 omega_n s^n.

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
