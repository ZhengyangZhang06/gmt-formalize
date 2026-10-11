# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.tilt_excess_height_estimate-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 5, Lemma 2.1 and its printed proof (pp. 107-108), with the test field taken smooth and integrability made explicit. Notation: mu := V.weight, p_x := V.tangentProj x, T^perp the orthogonal complement of T, x' := p_{T^perp}(x - xi), |.| the Hilbert-Schmidt norm (hsNorm), ||.|| the operator norm (||A|| <= |A|).

Facts used (cited from the book):
(F1) [Ch. 3, Def. 1.7, Rem. 1.8, Thm. 1.9; contract tangentProj] For mu-a.e. x the approximate tangent space T_xM of M with respect to theta exists, so p_x is the orthogonal projection onto an n-dimensional subspace; x -> p_x is mu-measurable.
(F2) mu(K) < infinity for every compact K in U (structure field integrableOn_mult); mu-a.e. point of U lies in spt V.
(F3) For orthogonal projections P, Q of rank n: trace(P o (I - Q)) = n - trace(PQ) = (1/2)|P - Q|^2.

Proof.
1. Put C := 146 * 2^(n+1) (it depends only on n). Fix l, U, V, H, xi, rho > 0 with B_rho(xi) contained in U (closed ball), and T with dim T = n. If the extended integral of |H|^2 over B_rho(xi) is infinite, the right side is infinite because ofReal(C rho^(2-n)) > 0, and there is nothing to prove. Assume it is finite, so H is in L^2(mu restricted to B_rho(xi)).
2. Choose phi in C^infinity(R, [0,1]) with phi = 1 on (-infinity, 1/2], phi = 0 on [1, infinity), |phi'| <= 3, and put zeta(x) := phi(|x - xi|/rho) (smooth, since phi is constant near 0). Then zeta = 1 on B_{rho/2}(xi), zeta = 0 off the open ball B^o_rho(xi), |grad zeta| <= 3/rho. Let X(x) := zeta(x)^2 x'. X is C^infinity, has compact support, and tsupport X is contained in B_rho(xi), a subset of U; so X is admissible in the definition of HasGeneralizedMeanCurvature.
3. Divergence. DX(x)v = zeta^2 p_{T^perp} v + 2 zeta (grad zeta . v) x', hence at every x where p_x is a rank-n projection (mu-a.e. by F1): div_M X = trace(DX o p_x) = zeta^2 trace(p_{T^perp} p_x) + 2 zeta (p_x grad zeta) . x' = zeta^2 s(x) + 2 zeta grad zeta . (p_x - p_T) x', where s(x) := (1/2)|p_x - p_T|^2 by F3, and we used that p_x is symmetric and p_T x' = 0.
4. First variation (book (1)-(3)): all integrands are bounded measurable functions supported in B_rho(xi), which has finite measure (F1, F2), and |x'||H| is integrable since H is in L^2 there; the defining identity of H gives
 integral zeta^2 s dmu = - integral 2 zeta grad zeta . (p_x - p_T) x' dmu - integral zeta^2 x' . H dmu.
5. Since |(p_x - p_T) x'| <= ||p_x - p_T|| |x'| <= |p_x - p_T| |x'| = sqrt(2 s) |x'|, and 2 sqrt(2 s) zeta |x'| |grad zeta| <= (1/2) zeta^2 s + 4 |x'|^2 |grad zeta|^2 (ab <= a^2/2 + b^2/2), we get, after subtracting the finite quantity (1/2) integral zeta^2 s:
 integral zeta^2 s dmu <= 8 integral |x'|^2 |grad zeta|^2 dmu + 2 integral zeta^2 |x'||H| dmu.
6. |x'||H| = (rho^-1 |x'|)(rho |H|) <= (1/2) rho^-2 |x'|^2 + (1/2) rho^2 |H|^2. With zeta = 1 on B_{rho/2}(xi), 0 <= zeta <= 1, |grad zeta| <= 3/rho and support in B_rho(xi):
 (1/2) integral_{B_{rho/2}(xi)} |p_x - p_T|^2 dmu <= 73 rho^-2 integral_{B_rho(xi)} |x'|^2 dmu + rho^2 integral_{B_rho(xi)} |H|^2 dmu.
7. |x'| = dist(x - xi, T) (infDist to the subspace). Multiplying by 2 (rho/2)^-n = 2^(n+1) rho^-n: E(xi, rho/2, T) <= 146 * 2^n rho^-n integral_{B_rho(xi)} (dist(x - xi, T)/rho)^2 dmu + 2^(n+1) rho^(2-n) integral_{B_rho(xi)} |H|^2 dmu, which gives the claim with C = 146 * 2^(n+1) (C dominates both coefficients). Both real integrals are finite and nonnegative, so ofReal of the sum splits into ofReal of the two terms, ofReal(C rho^(2-n) * integral |H|^2) = ofReal(C rho^(2-n)) * (lintegral of ||H||_e^2) in the finite case of step 1, and ofReal is monotone; this is the stated ENNReal inequality.

## Key steps

1. Infinite |H|^2 integral: trivial; otherwise H in L^2 on the ball
2. C^1 cutoff test field X = zeta^2 p_{T^perp}(x - xi) is admissible
3. div_M X = zeta^2 (1/2)|p_x - p_T|^2 + 2 zeta grad zeta.(p_x - p_T)x' mu-a.e.
4. First variation identity plus Young's inequality
5. |x'||H| <= rho^-2|x'|^2/2 + rho^2|H|^2/2 gives the bound with C = 146*2^(n+1)

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
