# Parent-supplied natural-language proof

- Parent DAG node: `root.harmonic_approximation-a1.weyl_lemma-a1`
- Child DAG node: `root.harmonic_approximation-a1.weyl_lemma-a1.mollifier_harmonic-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation (used throughout). B_s := ball(0,s) (open), B := B_1, |.| the Euclidean norm, <.,.> the inner product of R^n = EuclideanSpace R (Fin n). A test function is zeta in C^infinity(R^n) (ContDiff R (top : N-infinity)) with compact support and tsupport zeta contained in B. (e_i)_{i<n} is the standard orthonormal basis (EuclideanSpace.basisFun). For a function f differentiable at x and v in R^n, Df(x)[v] := fderiv R f x v and d_v f(x) := Df(x)[v]; d_i := d_{e_i}. <grad f(x), v> = Df(x)[v] (gradient is the Riesz transport of fderiv; InnerProductSpace.toDual_symm_apply). D^2 f(x)[a,b] := iteratedFDeriv R 2 f x ![a,b] = (D(Df)(x)[a])[b] (iteratedFDeriv_two_apply). For f in C^2 the Laplacian is Laplacian(f)(x) = sum_i D^2 f(x)[e_i,e_i] (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis with the orthonormal basis (e_i)). Fact (D2): if f is C^2 and e in R^n, the derivative of x -> Df(x)[e] in the direction e equals D^2 f(x)[e,e] (fderiv_clm_apply with the constant vector e, then iteratedFDeriv_two_apply).

Source. This is step 2 of the parent proof ("mollifications are harmonic away from the sphere"), including the facts from its Notation paragraph that derivatives of a convolution with a smooth compactly supported kernel fall on the kernel. A Lean template for steps 4-5 is simongmt Chapter08/DistributionalConstancy.lean, WeakDerivativesZero.fderiv_convolution_eq_zero (hasFDerivAt_convolution_right followed by convolution_precompR_apply).

Additional notation. W := 1_B w (the indicator of B times w). For phi : R^n -> R put (W * phi)(x) := int W(t) phi(x - t) dt; this is Mathlib's convolution `convolution W phi (ContinuousLinearMap.lsmul R R) volume` (convolution_def, lsmul_apply, smul_eq_mul). Let v(x) := int_B kappa(x - y) w(y) dy.

Proof.
1. W is integrable on R^n (integrable_indicator_iff, B measurable), hence locally integrable. For every phi and x, (W * phi)(x) = int 1_B(t) w(t) phi(x - t) dt = int_B phi(x - t) w(t) dt (integral_indicator and commutativity of the product). In particular v = W * kappa.

2. Compact supports. Put r := max(eps, 0). If kappa(z) != 0 then |z| < eps, so support kappa is contained in closedBall(0, r), which is compact; thus kappa has compact support and tsupport kappa lies in closedBall(0, r). (If eps <= 0, kappa = 0 identically.) For any vectors a, b the functions d_a kappa and d_b d_a kappa are C^infinity and vanish off tsupport kappa (fderiv_of_notMem_tsupport), so they also have compact support (HasCompactSupport.fderiv_apply).

3. Smoothness. By HasCompactSupport.contDiff_convolution_right (kappa C^infinity with compact support, W locally integrable), v = W * kappa is C^infinity. This is the first conclusion.

4. Derivatives fall on the kernel. Let phi : R^n -> R be C^infinity with compact support and e in R^n. Then for every x,
   D(W * phi)(x)[e] = (W * d_e phi)(x).
Proof: HasCompactSupport.hasFDerivAt_convolution_right gives that W * phi has derivative at x equal to the convolution of W with the operator-valued kernel Dphi (via the bilinear map lsmul.precompR); evaluating this derivative at e (convolution_precompR_apply, valid because Dphi is continuous with compact support and W is locally integrable; it rests on ContinuousLinearMap.integral_apply) gives (W * (z -> Dphi(z)[e]))(x) = (W * d_e phi)(x). Concretely D(W * phi)(x)[e] = int W(t) Dphi(x - t)[e] dt (differentiation under the integral sign, dominated by sup|Dphi| |W|).

5. Second derivatives. Let e in R^n. Since v is C^2, Fact (D2) gives D^2 v(x)[e,e] = D(x' -> Dv(x')[e])(x)[e]. By step 4 with phi = kappa, the function x' -> Dv(x')[e] equals W * d_e kappa; by step 4 again with phi = d_e kappa (C^infinity with compact support by step 2), its derivative at x in the direction e is (W * d_e d_e kappa)(x). By Fact (D2) for kappa, d_e d_e kappa(z) = D^2 kappa(z)[e,e]. Hence, using step 1,
   D^2 v(x)[e,e] = (W * D^2 kappa(.)[e,e])(x) = int_B D^2 kappa(x - t)[e,e] w(t) dt.

6. Laplacian of v. By the Laplacian formula for v and step 5,
   Laplacian(v)(x) = sum_i int_B D^2 kappa(x - t)[e_i,e_i] w(t) dt = int_B Laplacian(kappa)(x - t) w(t) dt,
where the finite sum and the integral commute because each t -> D^2 kappa(x - t)[e_i,e_i] w(t) is integrable on B (a bounded continuous factor times the integrable w), and sum_i D^2 kappa(z)[e_i,e_i] = Laplacian(kappa)(z) by the Laplacian formula for kappa.

7. The reflected translate is a test function. Fix x with |x| < 1 - eps and put zeta(y) := kappa(x - y). zeta is C^infinity (kappa composed with the affine map y -> x - y). If zeta(y) != 0 then |x - y| < eps; hence support zeta is contained in ball(x, eps) and tsupport zeta in closedBall(x, eps), so zeta has compact support. For y in closedBall(x, eps), |y| <= |x| + |y - x| <= |x| + eps < 1, so tsupport zeta lies in B. Thus zeta is a test function. (If eps <= 0 then zeta = 0 identically and everything below is trivial.)

8. Laplacian(zeta)(y) = Laplacian(kappa)(x - y). Put kappa_x(z) := kappa(x + z), which is C^infinity, so that zeta = kappa_x o (-id). First, ContinuousLinearMap.iteratedFDeriv_comp_right with the continuous linear map -id (order 2 <= infinity) gives D^2 zeta(y)[a,b] = D^2 kappa_x(-y)[-a,-b] = D^2 kappa_x(-y)[a,b], by bilinearity (the two signs cancel). Second, iteratedFDeriv_comp_add_left (translation by x) gives D^2 kappa_x(-y) = D^2 kappa(x + (-y)) = D^2 kappa(x - y). Hence D^2 zeta(y)[a,b] = D^2 kappa(x - y)[a,b]; summing over a = b = e_i gives the claim.

9. Conclusion. For |x| < 1 - eps, by steps 6 and 8 and the hypothesis applied to the test function zeta of step 7,
   Laplacian(v)(x) = int_B Laplacian(kappa)(x - t) w(t) dt = int_B w(t) Laplacian(zeta)(t) dt = 0.
Together with step 3 this proves both conclusions. QED

## Key steps

1. v = W * kappa with W = 1_B w integrable; kappa and all its derivatives have compact support
2. v is C^infinity (HasCompactSupport.contDiff_convolution_right)
3. Directional derivatives fall on the kernel: D(W * phi)(x)[e] = (W * d_e phi)(x) (hasFDerivAt_convolution_right, convolution_precompR_apply); iterate to get D^2 v(x)[e,e] = int_B D^2 kappa(x-t)[e,e] w(t) dt
4. Sum over the orthonormal basis: Laplacian(v)(x) = int_B Laplacian(kappa)(x - t) w(t) dt
5. For |x| < 1 - eps, zeta(y) := kappa(x - y) is a test function with Laplacian(zeta)(y) = Laplacian(kappa)(x - y), so Laplacian(v)(x) = int_B w Laplacian(zeta) = 0

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean; cmp <snapshot>/project/GMT/Ch05/Submission.lean GMT/Ch05/Submission.lean; sha256sum <snapshot>/project/GMT/Ch05/Contract.lean`
- `rg -l -i "weyl's lemma|weyl lemma|weakly harmonic|weaklyHarmonic|distributional.*harmonic" <snapshot>/mathlib/Mathlib`
- `rg -l -i "mean.value" <snapshot>/mathlib/Mathlib/Analysis`
- `rg -l "laplacian" <snapshot>/mathlib/Mathlib | xargs rg -l "convolution"`
- `rg -l "HarmonicOnNhd" <snapshot>/mathlib/Mathlib; rg -n "HarmonicOnNhd|laplacian" <snapshot>/project/GMT`
- `rg -n "^theorem|^lemma" <snapshot>/mathlib/Mathlib/Analysis/Complex/Harmonic/MeanValue.lean <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Harmonic/HarmonicContOnCl.lean`
- `grep -n "^theorem\|^lemma\|^noncomputable def\|notation" <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Harmonic/Basic.lean`
- `grep -rn "theorem _root_.HasCompactSupport.contDiff_convolution_left\|hasFDerivAt_convolution_left\|hasFDerivAt_convolution_right\|contDiff_convolution_right\|theorem convolution_eq_swap\|theorem convolution_assoc\|theorem convolution_symm\|theorem convolution_precompR_apply" <snapshot>/mathlib/Mathlib/Analysis/Convolution.lean <snapshot>/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `grep -n "theorem\|lemma" <snapshot>/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean; grep -n "theorem (normed|nonneg_normed|integral_normed|support_normed_eq|contDiff_normed)" <snapshot>/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `grep -n "^theorem\|^lemma" <snapshot>/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean <snapshot>/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `grep -rn "theorem eqOn_open_of_ae_eq\|theorem integral_comp_inv_smul_of_nonneg\|protected theorem contDiff\|theorem contDiff_norm_sq\|iteratedFDeriv_two_apply\|iteratedFDeriv_comp_sub\|iteratedFDeriv_comp_right\|theorem fderiv_of_notMem_tsupport\|theorem integral_pos_iff_support_of_nonneg\|theorem sum_inner_mul_inner\|theorem ContDiffAt.continuousAt_fderiv" <snapshot>/mathlib/Mathlib`
- `grep -rhoE '"lean_name": *"[^"]*"' .humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087 | sort -u (collision check for the six proposed names)`
- `sed -n 25,135p .lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `cmp of 7 consulted Mathlib files in the snapshot vs lake-packages-25730c7c/mathlib; git rev-parse HEAD of the compile-time mathlib package`
- `lake env lean /tmp/weyl-decomp-check/src/Check2.lean, Check3.lean, Check4.lean, Check5.lean, Check6.lean (against a scratch olean of the frozen GMT/Ch05/Submission.lean)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Harmonic/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Distribution/DerivNotation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Complex/Harmonic/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/L2Space.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-weyl-lemma-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/tmp/weyl-decomp-check/src/Check2.lean`
- `/tmp/weyl-decomp-check/src/Check4.lean`
- `/tmp/weyl-decomp-check/src/Check5.lean`
- `/tmp/weyl-decomp-check/src/Check6.lean`

Pinned snapshot and compile check:
- The snapshot pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d.
- The workspace Contract.lean and Submission.lean are byte-identical to the snapshot copies (sha256 c966f51efddb5a68ce15ef2a2a322fd9df0ca69da4626c7acef05b05d1691e12).
- The seven consulted Mathlib files are byte-identical to the compile-time package, whose HEAD is 25730c7c. So the Lean checks below apply to the frozen contract.

No relevant matches:
- Mathlib has no Weyl lemma and no weakly or distributionally harmonic API.
- Its only harmonic mean value theorem is the complex-plane circle average (HarmonicOnNhd.circleAverage_eq in Analysis/Complex/Harmonic/MeanValue.lean). The other mean-value hits are calculus mean value theorems. There is no n-dimensional mean value property.
- No file mentions both laplacian and convolution, so there is no Laplacian-of-convolution lemma.
- The project's GMT files use HarmonicOnNhd only in the frozen HarmonicApproximationLemma.

Usable API, all checked to exist and to match how the child proofs use it:
- Harmonic/Basic.lean: HarmonicAt, HarmonicOnNhd, harmonicAt_congr_nhds, HarmonicOnNhd.continuousOn.
- Laplacian.lean: Laplacian.laplacian on Rn n -> R resolves to InnerProductSpace.instLaplacian (checked by rfl against tensorIteratedFDerivTwo); laplacian_eq_iteratedFDeriv_orthonormalBasis, applied with EuclideanSpace.basisFun.
- ContDiff/Convolution.lean: HasCompactSupport.contDiff_convolution_right/left and hasFDerivAt_convolution_right/left.
- Convolution.lean: convolution_def, convolution_eq_swap, convolution_precompR_apply, convolution_assoc, convolution_symm.
- BumpFunction/Normed.lean and BumpFunction/Convolution.lean: the ContDiffBump.normed API, convolution_tendsto_right_of_continuous, and ae_convolution_tendsto_right_of_locallyIntegrable (K = 2).
- LineDeriv/IntegrationByParts.lean: integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable, which needs differentiability only on the other factor's tsupport.
- Distribution/AEEqOfIntegralContDiff.lean: IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero.
- Measure/OpenPos.lean: Measure.eqOn_open_of_ae_eq.
- Haar/NormedSpace.lean: Measure.integral_comp_inv_smul_of_nonneg.
- SmoothTransition.lean: expNegInvGlue.contDiff.
- FTaylorSeries.lean: iteratedFDeriv_two_apply and iteratedFDeriv_comp_add_left.
- ContDiff/Basic.lean: ContinuousLinearMap.iteratedFDeriv_comp_right.
- FDeriv/Const.lean: fderiv_of_notMem_tsupport and HasCompactSupport.fderiv_apply.

Imports:
- Under the contract's imports, three groups are unreachable: ContDiffBump.normed and its convergence lemmas, integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable, and integral_inner (Check5).
- Adding Mathlib.Analysis.Calculus.BumpFunction.Convolution and Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts to Submission.lean was checked to suffice. ContinuousLinearMap.integral_comp_comm (innerSL R e) replaces integral_inner and was also checked (Check6). The child proofs record both points.

simongmt: Chapter08/DistributionalConstancy.lean is a usable Lean template for the convolution-derivative and Lebesgue-differentiation steps (WeakDerivativesZero.fderiv_convolution_eq_zero, constancyMollifier with rOut = 2 rIn, ae_constancyMollifier_convolution_tendsto).

Lean evidence:
- Check4.lean is generated from the exact child type strings. All six types elaborate as GMT.Ch05.Submission.X after import GMT.Ch05.Submission with the contract's opens.
- Check4 then proves the exact frozen parent type from the six children in nine lines. #print axioms reports propext, Classical.choice, Quot.sound and sorryAx; sorryAx comes only from the stubbed children.
- Check2.lean type-checks the interface between mollifier_harmonic, mean_value_kernel and local_representative: the kernel scaling satisfies the vanishing hypothesis, HarmonicOnNhd follows from mollifier_harmonic's output, and the MVP applies to the bump mollifications on closedBall(x0, eps).

Name check: none of the six proposed names occurs among the 103 lean_name values in the run's artifacts or the DAG.

Public sources follow the same mollify, mean-value, limit route:
- Wikipedia, Weyl's lemma (Laplace equation).
- G. Liang, Weyl's Lemma (Emory notes).
- V. Sverak, PDE course notes (University of Minnesota).
- TauCeti PR #14110, which cites Hormander ALPDO I Thm 4.4.1 and Folland Cor. 2.20.
