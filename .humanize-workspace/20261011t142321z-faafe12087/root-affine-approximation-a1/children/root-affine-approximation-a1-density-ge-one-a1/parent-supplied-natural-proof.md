# Parent-supplied natural-language proof

- Parent DAG node: `root.affine_approximation-a1`
- Child DAG node: `root.affine_approximation-a1.density_ge_one-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 4, 3.9-3.11 and 3.12-3.13 (existence and upper semicontinuity of the density), 4.9 and Remark 4.10(1) (the L^p case, theta >= 1), with Theta = theta mu-a.e. from Ch. 3, Remark 1.8(2); this is fact (M.iv) of the parent proof, applied with W = B^o_rho(0).

Notation (contract). mu := V.weight = theta H^n restricted to M (M = V.carrier, theta = V.mult); spt V := V.support = U cap spt mu; p_x := V.tangentProj x and p_x^perp v := v - p_x v; B_s(y) := closedBall y s (closed), B^o_s(y) := ball y s (open); omega_n := unitBallVolume n > 0; for z and s > 0, K(z,s) := V.scaledLpNorm H p z s = (s^(p-n) integral_{B_s(z)} |H|^p dmu)^(1/p) in [0,infinity]; kappa := (p-n)/(4p) > 0; g_y(x) := |x - y - p_x(x - y)|^2 / |x - y|^(n+2) (= 0 at x = y by the convention a/0 = 0).
(F2) mu(R^(n+l) minus spt mu) = 0 (Mathlib Measure.measure_compl_support) and mu(R^(n+l) minus U) = 0 (mu is concentrated on M, which is contained in U), so mu-a.e. point lies in spt V; if K is compact and contained in U then mu(K) = integral_{M cap K} theta dH^n < infinity (V.integrableOn_mult).
(K-mono) If 0 < s <= t and B_s(z) is contained in B_t(w), then K(z,s) <= K(w,t): indeed s^(p-n) <= t^(p-n) (p > n), the integral of |H|^p over B_s(z) is at most that over B_t(w), and a -> a^(1/p) is monotone on [0,infinity].
(A) Under AllardHypotheses H p delta rho: rho > 0, V has generalized mean curvature H in U, theta >= 1 mu-a.e., 0 in spt V, B_rho(0) contained in U, mu(B_rho(0)) <= (1+delta) omega_n rho^n, and K(0,rho) <= delta; since rho^(p-n) > 0 the last bound gives integral_{B_rho(0)} |H|^p dmu < infinity, and by (K-mono) K(z,s) <= K(0,rho) <= delta whenever 0 < s <= rho and B_s(z) is contained in B_rho(0).

1. Uniform curvature bound on W := B^o_rho(0) (open, contained in U). Put Lambda := max(delta, 0)/kappa + 1 > 0, so kappa Lambda = max(delta,0) + kappa >= delta. If z in W, 0 < t < S and B_S(z) is contained in B_rho(0), then by (A): integral_{B_S(z)} |H|^p dmu <= integral_{B_rho(0)} |H|^p dmu < infinity and K(z,t) <= K(0,rho) <= ofReal(delta) <= ofReal(kappa Lambda) (note t <= rho).

2. Existence of the density at points of W (Simon 3.9, 4.9). For z in W let d(z) := rho - |z| > 0, R_z := d(z)/4 and S_z := d(z)/2; then B_{S_z}(z) is contained in B^o_rho(0). By Step 1, aal_lp_monotonicity applies at (z, R_z, S_z, Lambda) and gives F_z, G_z; put Phi_z(t) := F_z(t) t^(-n) mu(B_t(z)) + F_z(t) - 1 for t in (0, R_z]. By (ii) (G_z >= 0 and the annular integral of g_z >= 0), Phi_z is nondecreasing on (0, R_z]. By (i), F_z(t) >= e^(-Lambda) and |F_z(t) - 1| <= c(t/R_z), where c(u) := (1/2) e^(Lambda/2) Lambda u^(1-n/p) is increasing in u >= 0 with c(u) -> 0 as u -> 0+. Since Phi_z(t) >= F_z(t) - 1 >= e^(-Lambda) - 1, the monotone limit l_z := lim_{t -> 0+} Phi_z(t) exists in R and l_z <= Phi_z(t) for all t in (0, R_z]. As t^(-n) mu(B_t(z)) = (Phi_z(t) - F_z(t) + 1)/F_z(t) and F_z(t) -> 1, we get t^(-n) mu(B_t(z)) -> l_z. Define Theta(z) := l_z/omega_n; thus mu(B_t(z))/(omega_n t^n) -> Theta(z) as t -> 0+.

3. Upper semicontinuity of Theta on W (Simon 3.11, 4.9). Fix z in W and put r_1 := d(z)/8. If z' in R^(n+l) with |z' - z| <= r_1, then z' in W, d(z') >= 7 d(z)/8, so R_{z'} >= 7 d(z)/32 > r_1; hence for 0 < t <= r_1, |F_{z'}(t) - 1| <= c(t/R_{z'}) <= c(t/r_1) and
 omega_n Theta(z') = l_{z'} <= Phi_{z'}(t) <= (1 + c(t/r_1)) t^(-n) mu(B_t(z')) + c(t/r_1).
For 0 < eta <= r_1 and |z' - z| <= eta, B_t(z') is contained in B_{t+eta}(z), so omega_n Theta(z') <= (1 + c(t/r_1)) t^(-n) mu(B_{t+eta}(z)) + c(t/r_1). Therefore limsup_{z' -> z} omega_n Theta(z') <= (1 + c(t/r_1)) t^(-n) mu(B_{t+eta}(z)) + c(t/r_1) for every such eta; letting eta -> 0+ (the closed balls B_{t+eta}(z) decrease to B_t(z) and have finite measure) and then t -> 0+ (c(t/r_1) -> 0 and t^(-n) mu(B_t(z)) -> omega_n Theta(z) by Step 2) gives limsup_{z' -> z} Theta(z') <= Theta(z).

4. Theta >= 1 mu-a.e. on W (Simon 3.12 with Ch. 3, Remark 1.8(2)). By aal_tangent_structure (c), for mu-a.e. x, V.HasDensity x (theta(x)), i.e. mu(B_t(x))/ofReal(omega_n t^n) -> ofReal(theta(x)) in [0,infinity] as t -> 0+; by (A), theta(x) >= 1 for mu-a.e. x. Let x in W be such a point. By Step 2, mu(B_t(x))/(omega_n t^n) -> Theta(x) in R (all quantities finite), so ofReal(mu(B_t(x))/(omega_n t^n)) -> ofReal(Theta(x)); by uniqueness of limits ofReal(Theta(x)) = ofReal(theta(x)) >= 1, which forces Theta(x) = theta(x) >= 1. Hence mu({x in W : Theta(x) < 1}) = 0.

5. Conclusion (Simon 4.10(1)). The set O := {x in W : Theta(x) < 1} is open, because W is open and Theta is upper semicontinuous on W (Step 3), and mu(O) = 0 (Step 4). A point of spt mu has no open neighbourhood of measure zero, so O does not meet spt mu. Now let y in spt V cap B^o_rho(0); then y in spt mu cap W, so Theta(y) >= 1. Let epsilon > 0. Since mu(B_s(y))/(omega_n s^n) -> Theta(y) >= 1 > 1 - epsilon as s -> 0+, there is s_0 > 0 such that mu(B_s(y)) >= (1 - epsilon) omega_n s^n for all s in (0, s_0); as mu(B_s(y)) is finite, this is ofReal((1 - epsilon) * (omega_n s^n)) <= mu(B_s(y)) in [0,infinity], for all s in (0, s_0), which is the asserted eventual inequality along s -> 0+.

## Key steps

1. Uniform curvature bound on W = B^o_rho(0) with Lambda = max(delta,0)/kappa + 1.
2. At each z in W apply aal_lp_monotonicity with R = d/4, S = d/2: Phi_z is monotone, so Theta(z) = lim mu(B_t(z))/(omega_n t^n) exists.
3. Upper semicontinuity of Theta on W from the uniform monotonicity bound and B_t(z') contained in B_(t+eta)(z).
4. Theta = theta >= 1 mu-a.e. on W from aal_tangent_structure (c) and theta >= 1 a.e.
5. {Theta < 1} cap W is open and mu-null, hence misses spt mu; Theta(y) >= 1 gives the eventual lower bound.

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
