# Parent-supplied natural-language proof

- Parent DAG node: `root.harmonic_approximation-a1`
- Child DAG node: `root.harmonic_approximation-a1.weyl_lemma-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source and role. This covers facts (Weyl) and (U) of the parent proof (Simon p. 114: 'Thus w is harmonic in B'). It is Weyl's lemma (H. Weyl 1940), proved via mollification and the mean value property; cf. Hormander, ALPDO I, Thm 4.4.1 and Folland, Introduction to PDE, Cor. 2.20. The mean value property is proved below using only integration by parts on R^n. No sibling is used. A Lean template for the mollification steps is simongmt Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean (WeakDerivativesZero.fderiv_convolution_eq_zero, ae_constancyMollifier_convolution_tendsto).

Notation.
- B_s := ball(0,s), B := B_1. A test function is zeta in C^infinity(R^n) with compact support and tsupport zeta in B.
- Measurability: replace w and g by strongly measurable functions equal to them a.e. on B; this changes neither the hypotheses nor the conclusions.
- W := 1_B w. W is in L^1(R^n), since w is in L^2(B) and |B| < infinity.
- For a C^infinity kernel kappa with compact support, (kappa * W)(x) := int kappa(x-y) W(y) dy = int kappa(y) W(x-y) dy. It is C^infinity in x, and every partial derivative of kappa * W is the corresponding partial derivative of kappa convolved with W (Mathlib HasCompactSupport.contDiff_convolution_left and HasCompactSupport.hasFDerivAt_convolution_left, iterated).
- d_i denotes the derivative along the i-th standard basis vector e_i. On C^2 functions the Laplacian is sum_i d_i d_i (Mathlib InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis with the standard orthonormal basis).

Proof.
1. Weak harmonicity in Laplacian form: int_B w Laplacian(zeta) = 0 for every test function zeta. For each i, d_i zeta is a test function (C^infinity, compact support, tsupport d_i zeta inside tsupport zeta, inside B). The weak-gradient identity for d_i zeta gives int_B w grad(d_i zeta) = - int_B (d_i zeta) g. Its i-th coordinate is int_B w d_i d_i zeta = - int_B (d_i zeta) g_i. Summing over i: int_B w Laplacian(zeta) = - int_B <g, grad zeta> = 0, by hypothesis.

2. Mollifications are harmonic away from the sphere. Let 0 < eps < 1 and let kappa be in C^infinity(R^n) with kappa(z) = 0 for |z| >= eps. Then v := kappa * W is C^infinity on R^n, and Laplacian(v)(x) = 0 for every x in B_{1-eps}. Indeed, Laplacian(v)(x) = (Laplacian(kappa) * W)(x) = int_B w(y) Laplacian(kappa)(x-y) dy. The function zeta(y) := kappa(x-y) is C^infinity with compact support, tsupport zeta lies in closedBall(x,eps), which lies in B since |x| + eps < 1, and Laplacian(zeta)(y) = Laplacian(kappa)(x-y). So Laplacian(v)(x) = int_B w Laplacian(zeta) = 0 by step 1.

3. A radial mollifier and its potential.
- Let E(sigma) := expNegInvGlue(1 - sigma). Then E(sigma) = exp(-1/(1-sigma)) for sigma < 1 and E(sigma) = 0 for sigma >= 1. E is C^infinity (Mathlib expNegInvGlue.contDiff), E >= 0, and E(0) > 0.
- Let c := (int E(|z|^2) dz)^{-1}. The integral is finite and positive: the integrand is continuous, nonnegative, zero outside closedBall(0,1), and positive near 0. Put rho(z) := c E(|z|^2). Then rho is C^infinity (|z|^2 is smooth, contDiff_norm_sq), rho >= 0, rho(-z) = rho(z), rho(z) = 0 for |z| >= 1, and int rho = 1.
- For t > 0 let rho_t(y) := t^{-n} rho(y/t). It is C^infinity, even, nonnegative, zero for |y| >= t, and int rho_t = 1 by scaling (integral_comp_inv_smul_of_nonneg).
- Let P(sigma) := - int_sigma^1 E(s) ds for sigma in R. P is C^infinity with P' = E, and P(sigma) = 0 for sigma >= 1 because E vanishes on [1, infinity).
- Put Psi(z) := (c/2) P(|z|^2). Then Psi is C^infinity, Psi(z) = 0 for |z| >= 1 (so Psi has compact support), and grad Psi(z) = (c/2) P'(|z|^2) 2z = rho(z) z.

4. Mean value property for rho_t. Let h be in C^2(R^n), x0 in R^n and t > 0, and suppose Laplacian(h)(y) = 0 for all y in closedBall(x0,t). Then int h(x0 - y) rho_t(y) dy = h(x0), i.e. (rho_t * h)(x0) = h(x0).
(a) For each z, the FTC along sigma -> h(x0 + sigma z) gives h(x0 + tz) - h(x0) = int_0^t <grad h(x0 + sigma z), z> dsigma. Multiply by rho(z), integrate in z, and use int rho = 1 and Fubini. The integrand (sigma,z) -> <grad h(x0 + sigma z), z> rho(z) is continuous and vanishes outside [0,t] x closedBall(0,1), hence is integrable. This gives int h(x0 + tz) rho(z) dz - h(x0) = int_0^t I(sigma) dsigma, with I(sigma) := int <grad h(x0 + sigma z), z> rho(z) dz.
(b) Fix sigma in (0,t] and let H_sigma(z) := h(x0 + sigma z). H_sigma is C^2 with grad H_sigma(z) = sigma grad h(x0 + sigma z) and d_i d_i H_sigma(z) = sigma^2 (d_i d_i h)(x0 + sigma z). By step 3, I(sigma) = int <grad h(x0 + sigma z), grad Psi(z)> dz = sigma^{-1} sum_i int d_i H_sigma(z) d_i Psi(z) dz. Integration by parts on R^n gives int d_i H_sigma d_i Psi = - int (d_i d_i H_sigma) Psi; here d_i H_sigma is C^1, Psi is C^1 with compact support, and all products are integrable (Mathlib integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable). Hence I(sigma) = - sigma^{-1} int Laplacian(H_sigma)(z) Psi(z) dz = - sigma int Laplacian(h)(x0 + sigma z) Psi(z) dz = 0. The last equality holds because Psi(z) != 0 forces |z| < 1, so x0 + sigma z lies in closedBall(x0,t), where Laplacian(h) = 0.
(c) Hence int h(x0 + tz) rho(z) dz = h(x0). The substitution y = tz and the evenness of rho give int h(x0 - y) rho_t(y) dy = int h(x0 + y) rho_t(y) dy = int h(x0 + tz) rho(z) dz = h(x0).

5. Each w_eps equals w a.e. on B_{1-2eps}. Fix eps in (0,1/2) and put w_eps := rho_eps * W. By step 2 with kappa = rho_eps, w_eps is C^infinity with Laplacian 0 on B_{1-eps}.
- For j in N let s_j := eps/(j+2), which lies in (0,eps). Let psi_j be Mathlib's normalized ContDiffBump centred at 0 with rIn = s_j/2 and rOut = s_j (C^infinity, nonnegative, zero outside closedBall(0,s_j), integral 1), and let v_j := psi_j * W. By step 2, v_j is C^infinity with Laplacian 0 on B_{1-s_j}.
- Fix x0 in B_{1-2eps}. Since |x0| + eps < 1 - eps < 1 - s_j, the Laplacian of v_j vanishes on closedBall(x0,eps). Step 4 (with h = v_j and t = eps) gives v_j(x0) = (rho_eps * v_j)(x0).
- By Fubini, (rho_eps * (psi_j * W))(x0) = (psi_j * (rho_eps * W))(x0): both sides equal int int rho_eps(a) psi_j(b) W(x0 - a - b) da db, which converges absolutely since its absolute value is at most sup rho_eps * int psi_j * int |W| (Mathlib convolution_assoc and convolution_symm). Thus v_j(x0) = (psi_j * w_eps)(x0) for all j.
- As j -> infinity: (psi_j * w_eps)(x0) -> w_eps(x0) because w_eps is continuous (Mathlib ContDiffBump.convolution_tendsto_right_of_continuous). Also (psi_j * W)(x0) -> W(x0) for a.e. x0 in R^n, by Lebesgue's differentiation theorem (Mathlib ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable, with rOut <= 2 rIn and rOut -> 0; cf. simongmt ae_constancyMollifier_convolution_tendsto).
- For x0 in B, W(x0) = w(x0). Hence w = w_eps a.e. on B_{1-2eps}.

6. Compatibility. For eps, eps' in (0,1/2), w_eps and w_eps' are continuous and both equal w a.e. on the open set B_{1-2max(eps,eps')}. Lebesgue measure charges every nonempty open set, so w_eps = w_eps' at every point of B_{1-2max(eps,eps')}.

7. Definition of u, and harmonicity. For x in B put eps(x) := (1 - |x|)/4, which lies in (0,1/4], and u(x) := w_{eps(x)}(x); for x outside B put u(x) := 0.
Fix x0 in B and put d0 := 1 - |x0|, eps0 := eps(x0) = d0/4 and delta0 := d0/4. Let x be in ball(x0,delta0).
- |x| < |x0| + d0/4 < 1, so x is in B.
- |eps(x) - eps0| <= |x - x0|/4 < d0/16, so max(eps(x), eps0) < 5 d0/16.
- Hence 1 - 2 max(eps(x), eps0) > 1 - 5 d0/8 >= |x0| + d0/4 > |x|, using 1 - |x0| = d0 >= 7 d0/8.
By step 6, u(x) = w_{eps(x)}(x) = w_{eps0}(x). So u = w_{eps0} on the neighbourhood ball(x0,delta0) of x0. Moreover ball(x0,delta0) lies in B_{1-eps0}, since |x| < 1 - 3 d0/4 < 1 - d0/4; and the Laplacian of w_{eps0} vanishes there by step 2. Therefore u is C^infinity (in particular C^2) on ball(x0,delta0) with Laplacian 0 there, i.e. u is harmonic at x0 (Mathlib InnerProductSpace.harmonicAt_congr_nhds, comparing with w_{eps0}, which is harmonic at x0). As x0 in B is arbitrary, InnerProductSpace.HarmonicOnNhd u B.

8. u = w a.e. on B. For integers m >= 3 let N_m := {x in B_{1-2/m} : w(x) != w_{1/m}(x)}, a null set by step 5. Let x be in B but in no N_m, and choose m >= 3 with 1/m <= eps(x) and |x| < 1 - 2/m. Since |x| < (1 + |x|)/2 = 1 - 2 eps(x) = 1 - 2 max(eps(x), 1/m), step 6 gives u(x) = w_{eps(x)}(x) = w_{1/m}(x). Since x is in B_{1-2/m} but not in N_m, w_{1/m}(x) = w(x). So u = w on B outside the null set given by the union of the N_m.

9. grad u = g a.e. on B. Let zeta be a test function. Its tsupport is a compact subset of B, so there is eps in (0,1/4) with tsupport zeta inside B_{1-4eps}. For x in B_{1-4eps} we have eps(x) > eps and |x| < 1 - 2 eps(x), so u(x) = w_eps(x) by step 6. Thus u = w_eps on the open set B_{1-4eps}, and grad u = grad w_eps there. Since zeta and grad zeta vanish outside tsupport zeta:
int_B zeta grad u = int_{R^n} zeta grad w_eps
 = - int_{R^n} w_eps grad zeta (integration by parts on R^n, coordinatewise; w_eps is C^infinity and zeta is C^infinity with compact support)
 = - int_B w grad zeta (w_eps = w a.e. on B_{1-2eps}, which contains tsupport zeta, by step 5)
 = int_B zeta g (weak-gradient identity).
Hence int zeta (grad u - g) = 0 for every test function zeta; this is an integral over R^n of a function vanishing outside tsupport zeta, inside B. The function grad u - g is locally integrable on B: grad u is continuous on B by step 7, and g is in L^2(B), hence in L^1(B). By the fundamental lemma of the calculus of variations on the open set B (Mathlib IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero), grad u = g a.e. on B.

Steps 7, 8 and 9 give the three conclusions. QED

Formalization note. If needed, import Mathlib.Analysis.Calculus.BumpFunction.Convolution, Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension and Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts in GMT/Ch05/Submission.lean. The mean value property (steps 3-4) is a natural sub-lemma if this node is split further.

## Key steps

1. Weak identity with test functions d_i zeta: int_B w Laplacian(zeta) = - int_B <g, grad zeta> = 0
2. kappa * (1_B w) is C^infinity and harmonic on B_{1-eps} for kernels kappa supported in closedBall(0,eps)
3. Mean value property (rho_t * h)(x0) = h(x0) for the radial rho = c E(|z|^2), via Psi with grad Psi = rho(z) z and integration by parts
4. MVP, associativity of convolution and Lebesgue differentiation give w = rho_eps * W a.e. on B_{1-2eps}; mollifications agree pointwise on overlaps
5. Patch u(x) = w_{(1-|x|)/4}(x): u locally equals a harmonic w_{eps0}, and u = w a.e. on B
6. grad u = g a.e. via integration by parts and IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero

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
