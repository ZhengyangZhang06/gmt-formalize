# Parent-supplied natural-language proof

- Parent DAG node: `root.affine_approximation-a1`
- Child DAG node: `root.affine_approximation-a1.height_bound_small_delta-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 5, printed proof of Lemma 2.5 (pp. 109-110), steps (1)-(6) and the choice alpha = 1/(2n+2), in the explicit form of steps 4-7 of the parent proof (2.4 used at centres in B_{3 delta rho}(0), correction (c)).

Notation (contract). mu := V.weight = theta H^n restricted to M (M = V.carrier, theta = V.mult); spt V := V.support = U cap spt mu; p_x := V.tangentProj x and p_x^perp v := v - p_x v; B_s(y) := closedBall y s (closed), B^o_s(y) := ball y s (open); omega_n := unitBallVolume n > 0; for z and s > 0, K(z,s) := V.scaledLpNorm H p z s = (s^(p-n) integral_{B_s(z)} |H|^p dmu)^(1/p) in [0,infinity]; kappa := (p-n)/(4p) > 0; g_y(x) := |x - y - p_x(x - y)|^2 / |x - y|^(n+2) (= 0 at x = y by the convention a/0 = 0).
(F2) mu(R^(n+l) minus spt mu) = 0 (Mathlib Measure.measure_compl_support) and mu(R^(n+l) minus U) = 0 (mu is concentrated on M, which is contained in U), so mu-a.e. point lies in spt V; if K is compact and contained in U then mu(K) = integral_{M cap K} theta dH^n < infinity (V.integrableOn_mult).

1. Constants. Let C_P >= 1 and delta_P in (0, 1/8] with C_P delta_P <= 1/2 be the constants of aal_pinched_density_bounds for (n, l, p). Put alpha := 1/(2n+2), C_4 := 4^(n+1), C_5 := C_4 2^(n+2) C_P omega_n, C_6 := (4 C_5/omega_n)^(1/2), and define delta_1 := delta_P > 0 and C_1 := C_6 + 2 > 0 (depending only on n, l, p). Note 1/2 - alpha n = 1/(2n+2) = alpha.

2. Setup. Let U, V, H, delta in (0, delta_1], rho with AllardHypotheses H p delta rho (so rho > 0), xi in spt V with |xi| <= delta rho, and sigma in (0, 2 delta rho] be given. As delta <= 1/8: 2 sigma <= 4 delta rho <= rho/2, C_P delta <= 1/2 and 0 < delta < 1. Every y in B_sigma(xi) has |y| <= |xi| + sigma <= 3 delta rho. Hence aal_pinched_density_bounds applies at every y in B_sigma(xi) (in particular at xi) with every radius t in (0, 2 sigma]:
 mu(B_t(y)) <= (1 + C_P delta) omega_n t^n <= 2 omega_n t^n; and if y in spt V: mu(B_t(y)) >= (1 - C_P delta) omega_n t^n >= (1/2) omega_n t^n and integral^-_{B_t(y)} g_y dmu <= C_P omega_n delta.

3. Conical excess (book (1)). Let y in spt V cap B_sigma(xi). For x in B_{2 sigma}(y) with x != y, |p_x^perp(x - y)|^2 = |x - y|^(n+2) g_y(x) <= (2 sigma)^(n+2) g_y(x), and both sides vanish at x = y. By Step 2 with t = 2 sigma,
 integral^-_{B_{2 sigma}(y)} |p_x^perp(x - y)|^2 dmu <= (2 sigma)^(n+2) C_P omega_n delta.

4. Covering (book (2), (3)). Put A := delta^alpha in (0,1). Call a finite set {y_1, ..., y_N} contained in spt V cap B_sigma(xi) admissible if the closed balls B_{A sigma/2}(y_j) are pairwise disjoint. For an admissible set, each B_{A sigma/2}(y_j) is contained in B_{2 sigma}(xi) (A sigma/2 + sigma <= 2 sigma) and has measure >= (1/2) omega_n (A sigma/2)^n (Step 2 at y_j in spt V, radius A sigma/2 in (0, 2 sigma]), while mu(B_{2 sigma}(xi)) <= 2 omega_n (2 sigma)^n (Step 2 at xi, radius 2 sigma). By disjointness N (1/2) omega_n (A sigma/2)^n <= 2 omega_n (2 sigma)^n, i.e. N <= 4^(n+1) A^(-n) = C_4 delta^(-alpha n). Since {xi} is admissible, there is an admissible set {y_1, ..., y_N} (N >= 1) of maximal cardinality. By maximality, every y in spt V cap B_sigma(xi) satisfies |y - y_j| <= A sigma for some j: otherwise B_{A sigma/2}(y) is disjoint from every B_{A sigma/2}(y_j) (two closed balls of radius A sigma/2 with centres at distance > A sigma are disjoint) and y differs from every y_j, so adding y gives a larger admissible set. Thus spt V cap B_sigma(xi) is contained in the union of the B_{A sigma}(y_j), and N <= C_4 delta^(-alpha n).

5. Choice of a good point (book (4), (5)). Let f(x) := sum_{j=1}^N |p_x^perp(x - y_j)|^2 >= 0, which is mu-a.e. measurable (aal_tangent_structure (b)). B_sigma(xi) is contained in each B_{2 sigma}(y_j) (|x - y_j| <= |x - xi| + |xi - y_j| <= 2 sigma), so by Step 3,
 integral^-_{B_sigma(xi)} f dmu <= N (2 sigma)^(n+2) C_P omega_n delta <= C_5 delta^(1 - alpha n) sigma^(n+2).
Let lambda := (4 C_5/omega_n) delta^(1 - 2 alpha n) sigma^2 > 0. By Chebyshev's (Markov's) inequality, mu({x in B_sigma(xi) : f(x) >= lambda}) <= lambda^(-1) C_5 delta^(1 - alpha n) sigma^(n+2) = (1/4) omega_n delta^(alpha n) sigma^n = (1/4) omega_n (A sigma)^n. By Step 2 at xi in spt V with radius A sigma <= sigma, mu(B_{A sigma}(xi)) >= (1/2) omega_n (A sigma)^n. Since B_{A sigma}(xi) is contained in B_sigma(xi), the set Y := {x in B_{A sigma}(xi) : f(x) < lambda} has mu(Y) >= (1/4) omega_n (A sigma)^n > 0. By aal_tangent_structure (a), for mu-a.e. x there is an n-dimensional subspace P with p_x = P.starProjection; as mu(Y) > 0, there is x_0 in Y and an n-dimensional subspace T with p_{x_0} = p_T := T.starProjection.

6. The points y_j are close to T (book (5), (6)). For each j, p_{x_0}^perp(x_0 - y_j) = p_{T^perp}(x_0 - y_j) is one of the summands of f(x_0) < lambda, so |p_{T^perp}(x_0 - y_j)| <= lambda^(1/2) = C_6 delta^(1/2 - alpha n) sigma = C_6 delta^alpha sigma. Since |x_0 - xi| <= A sigma = delta^alpha sigma and |p_{T^perp} v| <= |v|, |p_{T^perp}(y_j - xi)| <= |p_{T^perp}(y_j - x_0)| + |p_{T^perp}(x_0 - xi)| <= (C_6 + 1) delta^alpha sigma for all j.

7. Height bound. Let x in spt V cap B_sigma(xi) and choose j with |x - y_j| <= A sigma (Step 4). Then, using dist(v, T) = |v - p_T v| = |p_{T^perp} v| (Mathlib Submodule.dist_starProjection_eq_infDist),
 dist(x - xi, T) = |p_{T^perp}(x - xi)| <= |p_{T^perp}(y_j - xi)| + |p_{T^perp}(x - y_j)| <= (C_6 + 1) delta^alpha sigma + delta^alpha sigma = C_1 delta^(1/(2n+2)) sigma.
T is n-dimensional, which proves the statement with delta_1 = delta_P and C_1 = C_6 + 2.

## Key steps

1. delta_1 := delta_P, alpha = 1/(2n+2), C_1 := (4 C_5/omega_n)^(1/2) + 2 with C_5 = 4^(n+1) 2^(n+2) C_P omega_n.
2. Pinched bounds (aal_pinched_density_bounds) at all centres in B_sigma(xi) (|y| <= 3 delta rho) and radii <= 2 sigma <= rho/2.
3. Conical excess: int_{B_2sigma(y)} |p_x^perp(x - y)|^2 <= (2sigma)^(n+2) C_P omega_n delta for y in spt V cap B_sigma(xi).
4. Maximal disjoint family of balls B_(A sigma/2)(y_j), A = delta^alpha: N <= 4^(n+1) delta^(-alpha n), and every support point is within A sigma of some y_j.
5. Chebyshev on f = sum_j |p_x^perp(x - y_j)|^2 and the lower mass bound on B_(A sigma)(xi) give x_0 near xi with f(x_0) < lambda and p_(x_0) = p_T (aal_tangent_structure).
6. Triangle inequalities with 1/2 - alpha n = alpha give dist(x - xi, T) <= (C_6 + 2) delta^alpha sigma.

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
