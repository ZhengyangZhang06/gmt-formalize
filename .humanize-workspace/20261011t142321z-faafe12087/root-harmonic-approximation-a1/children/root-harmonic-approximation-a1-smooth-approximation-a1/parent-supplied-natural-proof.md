# Parent-supplied natural-language proof

- Parent DAG node: `root.harmonic_approximation-a1`
- Child DAG node: `root.harmonic_approximation-a1.smooth_approximation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source and role. This is standard interior mollification (Friedrichs); cf. Evans, Partial Differential Equations, 5.3.1 (interior approximation by smooth functions), and Gilbarg-Trudinger, Elliptic PDE of Second Order, 7.2-7.3 (mollifiers, weak derivatives). It supplies the smooth approximants behind facts (P) and (R) of the parent proof (Simon Ch. 5, Lemma 3.1). The siblings w12_ball_poincare_inequality, w12_ball_boundary_layer_estimate and w12_ball_translation_estimate depend on it.

Notation.
- B_s := ball(0,s) in R^n (open); B := B_1; |E| := Lebesgue measure of E; grad := Mathlib's gradient.
- A test function is zeta in C^infinity(R^n) with compact support and tsupport zeta contained in B.
- Integrals of nonnegative functions are lintegrals with values in [0, infinity]; ||u||_{2,E} := (int_E |u|^2)^{1/2}.
- Hypothesis: f in L^2(B), g in L^2(B;R^n), and int_B f grad zeta = - int_B zeta g (Bochner integrals in R^n) for every test function zeta.
Fix r in (0,1).

Proof.
0. Measurability. f and g are a.e.-strongly measurable for Lebesgue measure restricted to B. Replace them by strongly measurable functions equal to them a.e. on B (e.g. AEStronglyMeasurable.mk). This changes neither the hypothesis (all integrals are over B) nor the conclusion (the two integrals see f and g only a.e. on B_r, a subset of B).

1. Zero extensions. Put F := 1_B f and G := 1_B g, the extensions by 0. Then F = f and G = g on B. Since |B| < infinity, Cauchy-Schwarz gives int|F| <= |B|^{1/2} ||f||_{2,B} < infinity, and likewise for G. Hence F is in L^1(R^n) and L^2(R^n), and G is in L^1(R^n;R^n) and L^2(R^n;R^n).

2. Mollifiers. For eps > 0 choose rho_eps in C^infinity(R^n) with rho_eps >= 0, rho_eps(z) = 0 for |z| >= eps, and int rho_eps = 1. Then tsupport rho_eps lies in closedBall(0,eps) and is compact. A concrete choice is Mathlib's normalized bump with rIn = eps/2 and rOut = eps (ContDiffBump.normed volume; lemmas contDiff_normed, nonneg_normed, tsupport_normed_eq, integral_normed). For H in L^1(R^n;V), with V = R or R^n, write (rho_eps * H)(x) := int rho_eps(x-y) H(y) dy = int rho_eps(z) H(x-z) dz.

3. Smoothness and first derivative. f_eps := rho_eps * F is C^infinity on R^n and may be differentiated under the integral sign: D f_eps(x) v = int (D rho_eps(x-y) v) F(y) dy for all x, v. Equivalently, grad f_eps(x) = int F(y) grad rho_eps(x-y) dy. This uses Mathlib's HasCompactSupport.contDiff_convolution_left and HasCompactSupport.hasFDerivAt_convolution_left, since rho_eps is C^infinity with compact support and F is locally integrable.

4. grad f_eps is the mollified weak gradient on B_{1-eps}. Let |x| < 1 - eps and zeta_x(y) := rho_eps(x-y). Then zeta_x is C^infinity with compact support, and tsupport zeta_x lies in closedBall(x,eps), which lies in B because every y there has |y| <= |x| + eps < 1. So zeta_x is a test function, and grad zeta_x(y) = - grad rho_eps(x-y) by the chain rule. The weak-gradient identity for zeta_x reads - int_B f(y) grad rho_eps(x-y) dy = - int_B rho_eps(x-y) g(y) dy. Since F = 1_B f and G = 1_B g, step 3 gives grad f_eps(x) = int_B f(y) grad rho_eps(x-y) dy = int_B rho_eps(x-y) g(y) dy = (rho_eps * G)(x).

5. L^2 contraction. For H in L^1 and L^2 of R^n (values in V): int |rho_eps * H|^2 <= int |H|^2. Indeed |(rho_eps * H)(x)| <= int rho_eps(x-y) |H(y)| dy. Cauchy-Schwarz with the weight rho_eps(x - .), of total mass 1, gives (int rho_eps(x-y)|H(y)| dy)^2 <= int rho_eps(x-y) |H(y)|^2 dy. Integrating in x and using Tonelli and int rho_eps(x-y) dx = 1 gives the claim.

6. Approximate identity in L^2. For H in L^1 and L^2 of R^n: ||rho_eps * H - H||_{2,R^n} -> 0 as eps -> 0+. Let eta > 0.
(a) Choose Phi : R^n -> V continuous with compact support and ||H - Phi||_{2,R^n} <= eta (Mathlib MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le).
(b) Phi is uniformly continuous, so omega(eps) := sup{|Phi(a) - Phi(b)| : |a - b| <= eps} -> 0 as eps -> 0+. For 0 < eps <= 1, |(rho_eps * Phi)(x) - Phi(x)| = |int rho_eps(z)(Phi(x-z) - Phi(x)) dz| <= omega(eps). Moreover rho_eps * Phi - Phi vanishes outside the compact set K1 := {x : dist(x, tsupport Phi) <= 1}. Hence ||rho_eps * Phi - Phi||_{2,R^n}^2 <= omega(eps)^2 |K1| -> 0.
(c) H - Phi is in L^1, so rho_eps * H - rho_eps * Phi = rho_eps * (H - Phi). By Minkowski and step 5, ||rho_eps * H - H||_2 <= ||rho_eps * (H - Phi)||_2 + ||rho_eps * Phi - Phi||_2 + ||Phi - H||_2 <= 2 eta + ||rho_eps * Phi - Phi||_2. By (b) this is <= 3 eta for all sufficiently small eps > 0.

7. Conclusion. Let eps_j := (1-r)/(j+2), so 0 < eps_j < 1 - r and eps_j -> 0. Put phi_j := rho_{eps_j} * F, which is C^infinity by step 3.
- Since F = f on B_r (a subset of B), int_{B_r} |phi_j - f|^2 <= int_{R^n} |rho_{eps_j} * F - F|^2 -> 0 by step 6 with H = F.
- For x in B_r we have |x| < r < 1 - eps_j, so grad phi_j(x) = (rho_{eps_j} * G)(x) by step 4, and G = g on B_r. Hence int_{B_r} |grad phi_j - g|^2 <= int_{R^n} |rho_{eps_j} * G - G|^2 -> 0 by step 6 with H = G.
These are the two required limits in [0, infinity], so (phi_j) is the required sequence. QED

Formalization note. Some cited lemmas live in Mathlib modules the contract does not import (e.g. Mathlib.Analysis.Calculus.BumpFunction.Convolution, Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension, Mathlib.MeasureTheory.Function.ContinuousMapDense). Import them in GMT/Ch05/Submission.lean; the comparator byte-checks only the contract and build inputs.

## Key steps

1. Replace f, g by strongly measurable representatives and zero-extend them to F, G in L^1 and L^2 of R^n
2. Mollify: f_eps = rho_eps * F is C^infinity with grad f_eps(x) = int F(y) grad rho_eps(x-y) dy
3. Testing the weak identity with zeta_x = rho_eps(x - .) gives grad f_eps = rho_eps * G on B_{1-eps}
4. L^2 contraction plus density of compactly supported continuous functions gives rho_eps * H -> H in L^2(R^n)
5. Take eps_j = (1-r)/(j+2) and phi_j = rho_{eps_j} * F; both errors on B_r tend to 0

## Reference use

### local-project

Queries:
- `for pat in 'Rellich' 'Kondrachov' 'Poincar' 'Weyl' 'weakly harmonic|weaklyHarmonic|WeaklyHarmonic' 'mean value property|meanValue|mean_value' 'Sobolev' 'weak derivative|weakDeriv|WeakDeriv|HasWeakDeriv' 'mollif|Mollif'; do rg -l -i "$pat" <snapshot>/mathlib/Mathlib; done`
- `rg -n 'theorem .*isSeqCompact|theorem .*exists_tendsto.*weak|seqCompact.*WeakDual|WeakDual.*SeqCompact' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem .*ae_eq_zero_of_integral_contDiff|theorem .*ae_eq_of_integral_contDiff' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem .*convolution_tendsto|theorem .*ae_convolution_tendsto|theorem .*tendsto_convolution' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem arzela_ascoli' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable|theorem integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable|theorem integral_bilinear_fderiv_right_eq_neg_left_of_integrable' <snapshot>/mathlib/Mathlib`
- `rg -n 'instance.*SecondCountableTopology.*Lp|SeparableSpace.*Lp|instance.*Lp.*SecondCountable|theorem .*secondCountableTopology' <snapshot>/mathlib/Mathlib/MeasureTheory`
- `rg -n 'theorem MemLp.exists_hasCompactSupport|theorem .*exists_contDiff.*eLpNorm|theorem .*_dense' <snapshot>/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `rg -n '^(theorem|lemma|noncomputable def|def) ' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean`
- `rg -n 'theorem _root_\.HasCompactSupport\.(contDiff|hasFDerivAt|hasDerivAt|fderiv)' <snapshot>/mathlib/Mathlib/Analysis`
- `rg -n 'theorem (normed|nonneg_normed|integral_normed|support_normed_eq|hasCompactSupport_normed|contDiff_normed|tsupport_normed_eq)' <snapshot>/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `rg -n 'theorem tendsto_integral_smul_of_tendsto_average_norm_sub' -A 12 <snapshot>/mathlib/Mathlib`
- `rg -n -e 'def toDual' -e 'theorem contDiff_norm_sq' -e 'theorem tendstoInMeasure_of_tendsto_eLpNorm' -e 'theorem TendstoInMeasure.exists_seq_tendsto_ae' -e 'theorem cauchy_complete_eLpNorm' -e 'theorem IsCompact.tendsto_subseq' -e 'theorem integral_comp_inv_smul_of_nonneg' -e 'expNegInvGlue.contDiff' <snapshot>/mathlib/Mathlib/{Analysis,MeasureTheory,Topology}`
- `rg -n -e 'theorem convolution_symm' -e 'theorem convolution_flip' -e 'theorem integral_comp_smul ' -e 'theorem setIntegral_comp_smul' <snapshot>/mathlib/Mathlib/Analysis/Convolution.lean <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `rg -l -i 'rellich|poincare_ineq|poincaré inequality|weyl|weakly harmonic|mollif|meanValue|mean_value|IsW12|weak gradient|weakGradient' .lake/packages/simongmt/Poincare`
- `rg -n '^(theorem|lemma|def|noncomputable def|structure)' .lake/packages/simongmt/Poincare/SimonGMT/Chapter05/*.lean`
- `cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean; cmp <snapshot>/project/GMT/Ch05/Submission.lean GMT/Ch05/Submission.lean`
- `grep -n -i 'harmonic approximation|Lemma 3.1|Rellich' book/sources/chapter-05-source.txt; sed -n 580,660p book/sources/chapter-05-source.txt`
- `lake env lean /tmp/hal-decomp-check/Check.lean (frozen-contract copy + the 7 child declarations + a HarmonicApproximationLemma assembly skeleton)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Harmonic/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Module/WeakDual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Distribution/Sobolev.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/ContinuousMap/Bounded/ArzelaAscoli.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/SeparableMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/L2Space.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LpSpace/Complete.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Average.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/Poincare.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-05-source.txt`
- `/tmp/hal-decomp-check/Check.lean`

Pinned snapshot: project ea5607598f3133b40a13241f2e51517a8c6423cd, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json). The snapshot's GMT/Ch05/Contract.lean and Submission.lean are byte-identical to the workspace copies (cmp; Contract sha256 c966f51efddb5a68ce15ef2a2a322fd9df0ca69da4626c7acef05b05d1691e12), so the Lean check below applies to the frozen contract.

No usable matches:
- Mathlib has no Rellich/Kondrachov, weakly-harmonic, weak-derivative or mollifier API (0 files each).
- 'Poincar' hits only unrelated files (curve-integral Poincare lemma, Poincare conjecture, the hyperbolic metric).
- 'Weyl' hits only Lie-algebra and root-system files.
- 'Sobolev' hits only SobolevInequality.lean (Gagliardo-Nirenberg-Sobolev for compactly supported C^1 functions) and the Fourier-side Bessel-potential spaces (Analysis/Distribution/Sobolev.lean, BesselPotentialSpace.lean). Neither gives W^{1,2}(B) Poincare or Rellich.
- Mean-value hits are one-dimensional or complex only (Analysis/Complex/Harmonic/MeanValue.lean); there is no n-dimensional mean value property.
So Poincare, Rellich, weak compactness and Weyl must be proved; hence the children.

Usable Mathlib items cited in the child proofs, all verified to exist:
- Harmonic functions and Laplacian: HarmonicAt/HarmonicOnNhd and harmonicAt_congr_nhds (Harmonic/Basic.lean); laplacian_eq_iteratedFDeriv_orthonormalBasis (Laplacian.lean:171).
- Convolution: HasCompactSupport.contDiff_convolution_left and hasFDerivAt_convolution_left (ContDiff/Convolution.lean:427,91); convolution_assoc and convolution_symm (Convolution.lean:925,688).
- Bump functions: the ContDiffBump.normed API (BumpFunction/Normed.lean); ContDiffBump.convolution_tendsto_right_of_continuous and ae_convolution_tendsto_right_of_locallyIntegrable (BumpFunction/Convolution.lean:94,103).
- Distributions and integration by parts: IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (AEEqOfIntegralContDiff.lean:205); integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (LineDeriv/IntegrationByParts.lean:226).
- Compactness: BoundedContinuousFunction.arzela_ascoli (Bounded/ArzelaAscoli.lean:109); IsCompact.tendsto_subseq (Sequences.lean:298); WeakDual.isSeqCompact_closedBall (WeakDual.lean:369).
- Hilbert and Lp spaces: InnerProductSpace.toDual (Dual.lean:136); L2.inner_def (L2Space.lean:136); instance Lp.SecondCountableTopology (SeparableMeasure.lean:426); MemLp.exists_hasCompactSupport_eLpNorm_sub_le (ContinuousMapDense.lean:141); tendstoInMeasure_of_tendsto_eLpNorm and TendstoInMeasure.exists_seq_tendsto_ae (ConvergenceInMeasure.lean:452,273); cauchy_complete_eLpNorm (LpSpace/Complete.lean:370).
- Smooth functions and scaling: expNegInvGlue.contDiff (SmoothTransition.lean); contDiff_norm_sq (InnerProductSpace/Calculus.lean:140); integral_comp_inv_smul_of_nonneg and integral_comp_smul (Haar/NormedSpace.lean).
- Lebesgue differentiation with general kernels: tendsto_integral_smul_of_tendsto_average_norm_sub (Integral/Average.lean:835).
Several of these live in modules the contract does not import. The comparator byte-checks only the contract and build inputs, so they may be imported in GMT/Ch05/Submission.lean; the proofs note this.

simongmt (pinned package, outside the snapshot):
- No Rellich, no W^{1,2} Poincare, no Weyl lemma.
- Chapter04/Poincare.lean is Simon's varifold Poincare-type inequality, a different statement.
- Chapter08/DistributionalConstancy.lean (WeakDerivativesZero.fderiv_convolution_eq_zero, ae_constancyMollifier_convolution_tendsto) is a usable Lean template for the Weyl child's mollification steps.
- Chapter05 contains only graph-area and harmonic-energy algebra.

Book source (chapter-05-source.txt, about lines 588-645): the printed proof of Lemma 3.1 cites the Poincare inequality and Rellich's theorem ([GT01]) and weak L^2 convergence of the gradients with int|grad w|^2 <= 1, and concludes 'w is harmonic'. This matches the supplied proof and the children.

Lean check (/tmp/hal-decomp-check/Check.lean, lake env lean, exit 0): all seven child types elaborate in namespace GMT.Ch05.Submission after the frozen contract. An assembly skeleton of HarmonicApproximationLemma from the Poincare, Rellich, weak-compactness and Weyl children type-checks; the glue is left as sorry, and the only warnings are sorry and a push_neg deprecation.

Public sources consulted: Wikipedia 'Weyl's lemma (Laplace equation)'; University of Hamburg PDE lecture notes (radial-kernel mean value argument); TauCeti PR #14110, which cites Hormander ALPDO I Thm 4.4.1 and Folland Cor. 2.20. Textbook citations in the proofs either follow the parent proof (GT (7.45), Thm 7.26) or are section-level (Evans sections 5.3, 5.7, 5.8, App. D).
