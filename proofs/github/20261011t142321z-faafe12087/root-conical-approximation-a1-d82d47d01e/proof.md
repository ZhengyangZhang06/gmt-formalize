# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.conical_approximation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 5, Theorem 6.1 and its printed proof (p. 124-127), steps (1)-(12). Repairs: the trivial case delta^(1/4)|log lambda| > 1 is separated (this gives the mass bounds needed for the Cauchy-Schwarz step (7)); the piecewise-linear cutoff gamma is replaced by C^1 cutoffs and a limit; the homogeneous functions h = h_t are constructed explicitly with |Dh(x)| <= 2/(delta^(1/4) rho |x|); in the printed (1) the integrand is r^-n |D^perp r|^2 = r^(-n-2) |x^perp|^2; tau = 1 is trivial and every tau in [2 lambda, 1) is allowed (printed 'tau in [lambda, 1/2]' is a typo). Notation: mu = V.weight, r = |x|, x^perp := p_{T_x^perp} x, grad^M r = p_x(x/r) with |grad^M r|^2 = 1 - r^-2 |x^perp|^2 (mu-a.e.), integral_{dB_t} g := integral_{M cap dB_t} g theta dH^(n-1); balls closed; |log lambda| >= log 4 > 1. No lower bound on theta is used.

Facts used: (F1),(F2) (tangent planes a.e., measurability, local finiteness); (3.18) [Ch. 4, 3.18]: if tau^(1-n) integral_{B_tau(0)} |H| dmu <= delta for sigma <= tau <= rho' (B_{rho'}(0) in U), then |(rho'^-n mu(B_{rho'}) - sigma^-n mu(B_sigma)) - integral_{B_{rho'} minus B_sigma} r^-n |D^perp r|^2 dmu| <= delta log(rho'/sigma); (4.11) [Ch. 4, 4.11] layer-cake for integrals of r^(1-n)|H| and r^-n; (CoA) [Ch. 3, 2.9] coarea for r on the countably n-rectifiable M: integral_A g |grad^M r| theta dH^n = integral_0^infinity integral_{M cap A cap dB_t} g theta dH^(n-1) dt for nonnegative measurable g.

Proof. C denotes constants depending on n, l, Lambda.
0. Trivial case. If delta^(1/4)|log lambda| > 1: B_{(1-delta^(1/4))rho}(xi) is in B_1(0), so the left side of the first inequality is <= Lambda < Lambda delta^(1/4)|log lambda|; and B_{tau rho}(tau xi) is in B_tau(0), so by (3.18) tau^-n mu(B_{tau rho}(tau xi)) <= mu(B_1) + delta |log lambda| <= (Lambda + 1) delta^(1/4)|log lambda|. So both inequalities hold if C >= Lambda + 1. Henceforth delta^(1/4)|log lambda| <= 1, hence delta |log lambda| <= 1.
1. By (3.18) with sigma = lambda, rho' = 1 and the hypothesis: integral_{B_1 minus B_lambda} r^(-n-2) |x^perp|^2 dmu <= C delta |log lambda| (1); and tau^-n mu(B_tau) <= mu(B_1) + delta |log lambda| <= Lambda + 1 for tau in [lambda, 1] (2). With (4.11): integral_{B_1 minus B_lambda} r^(1-n) |H| dmu <= C delta |log lambda| (3) (write r^(1-n) = 1 + (n-1) integral_r^1 t^-n dt and use t^(1-n) integral_{B_t} |H| <= delta), and integral_{B_1 minus B_lambda} r^-n dmu <= C (Lambda + 1) |log lambda| (by (2)).
2. First variation identity (book (5)). Let h in C^1(R^(n+l) minus {0}; [0,1]) be homogeneous of degree 0 with |Dh(x)| <= k/|x|. Since x . Dh(x) = 0: |x . p_x(Dh)| = |x^perp . Dh| <= k |x^perp|/r (4). For psi in C^1_c((0,1]) put X := h r^-n psi(r) x (in C^1_c(U), support in B_1(0)); mu-a.e. div_M X = n psi h r^(-n-2)|x^perp|^2 + psi'(r) h r^(1-n) |grad^M r|^2 + psi r^-n x . grad^M h. Insert into the definition of generalized mean curvature, let psi increase to the indicator of [s,t] (lambda <= s < t <= 1) with psi' concentrating at s and -t, and use (CoA) with g = h r^(1-n)|grad^M r|: for a.e. such s, t, with A(s) := integral_{dB_s} h r^(1-n) |grad^M r|,
 A(s) - A(t) + n integral_{B_t minus B_s} h r^(-n-2) |x^perp|^2 dmu = - integral_{B_t minus B_s} r^-n (h x . H + x . grad^M h) dmu.
 By (3), (4): |A(s) - A(t) + n integral_{B_t minus B_s} h r^(-n-2)|x^perp|^2| <= C delta|log lambda| + k integral_{B_1 minus B_lambda} r^(-n-1) |x^perp| dmu.   (5)
3. Homogeneity (book (6),(7)). Take s = tau t with tau in [2 lambda, 1) and t >= 1/2 (then s >= lambda). Multiply by t^(n-1) <= 1 and use h(tau x) = h(x); by Cauchy-Schwarz, (1) and step 1:
 | tau^(1-n) integral_{dB_{tau t}} h |grad^M r| - integral_{dB_t} h |grad^M r| | <= C delta |log lambda| + C k (Lambda+1)^(1/2) delta^(1/2) |log lambda|.   (7)
4. Choice of h (book (8)). For rho in (0, theta], |xi| = 1 - theta, t in (|xi| - rho, |xi| + rho) (so t >= 1 - 2 theta >= 1/2), let phi in C^infinity(R; [0,1]) with phi = 1 on (-inf, (1 - delta^(1/4)) rho], phi = 0 on [rho, inf), |phi'| <= 2/(delta^(1/4) rho), and h_t(x) := phi(|t x/|x| - xi|). Then h_t = 1 on dB_t cap B_{(1-delta^(1/4))rho}(xi), h_t = 0 on dB_t minus B_rho(xi), on dB_{tau t} the set {h_t > 0} lies in B_{tau rho}(tau xi), and |Dh_t(x)| <= 2/(delta^(1/4) rho |x|), i.e. k = 2 delta^(-1/4) rho^-1. (7) gives for a.e. such t:
 integral_{dB_t cap B_{(1-delta^(1/4))rho}(xi)} |grad^M r| <= tau^(1-n) integral_{dB_{tau t} cap B_{tau rho}(tau xi)} |grad^M r| + C rho^-1 (Lambda+1)^(1/2) delta^(1/4) |log lambda| + C delta |log lambda|.   (8)
(Rigour of the pointwise-in-t statements: since h_t depends on t, keep psi_eps with psi_eps' = 1/eps on [tau t - eps, tau t] and -1/eps on [t, t + eps], write the identity of step 2 for (h_t, psi_eps), integrate it over t in (|xi| - rho, |xi| + rho) first (all integrands are jointly measurable and integrable), and let eps -> 0 only at the end; by (CoA) the averaged boundary terms converge for these integrated quantities.)
5. Integrate (8) over t in (|xi| - rho, |xi| + rho) and use (CoA) twice (the substitution t' = tau t turns the first right-hand term into tau^-n integral_{B_{tau rho}(tau xi)} |grad^M r|^2 dmu; B_{(1-delta^(1/4))rho}(xi) lies in the shell |xi| - rho < r < |xi| + rho):
 integral_{B_{(1-delta^(1/4))rho}(xi)} |grad^M r|^2 dmu <= tau^-n integral_{B_{tau rho}(tau xi)} |grad^M r|^2 dmu + C delta^(1/4) |log lambda|.   (9)
 Since |grad^M r|^2 = 1 - r^-2 |x^perp|^2 and r <= 1, (1) gives mu(B_{(1-delta^(1/4))rho}(xi)) <= tau^-n mu(B_{tau rho}(tau xi)) + C delta^(1/4) |log lambda|.   (11)
6. Reverse inequality (book (12)). Use (7) with phi = 1 on (-inf, rho], phi = 0 on [(1+delta^(1/4)) rho, inf), |phi'| <= 2/(delta^(1/4) rho): h_t = 1 on dB_{tau t} cap B_{tau rho}(tau xi) and h_t = 0 on dB_t minus B_{(1+delta^(1/4))rho}(xi). Integrating over t as in step 5 (the shell contains B_{tau rho}(tau xi) after scaling) gives tau^-n integral_{B_{tau rho}(tau xi)} |grad^M r|^2 <= mu(B_{(1+delta^(1/4))rho}(xi)) + C delta^(1/4)|log lambda|, and tau^-n integral_{B_{tau rho}(tau xi)} r^-2 |x^perp|^2 <= integral_{B_1 minus B_lambda} r^(-n-2)|x^perp|^2 (as r <= tau there and B_{tau rho}(tau xi) is in B_1 minus B_lambda). Hence tau^-n mu(B_{tau rho}(tau xi)) <= mu(B_{(1+delta^(1/4))rho}(xi)) + C delta^(1/4)|log lambda|.   (12)
7. tau = 1: both inequalities are trivial by monotonicity of mu in the radius. With C := max(Lambda + 1, constants above), C = C(n, l, Lambda), the statement holds for all rho in (0, theta] and tau in [2 lambda, 1] (the ENNReal form 'a <= b + c' is (11), (12) with finite quantities).

## Key steps

1. Trivial case delta^(1/4)|log lambda| > 1
2. 3.18 and 4.11 give (1)-(3) and the mass bounds
3. First variation with homogeneous h and radial C^1 cutoffs, limits taken after averaging
4. Coarea formula for r = |x| on M
5. Homogeneous cutoffs h_t with |Dh_t| <= 2/(delta^(1/4) rho |x|)
6. Integrate over t to get both inequalities; tau = 1 is trivial

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
