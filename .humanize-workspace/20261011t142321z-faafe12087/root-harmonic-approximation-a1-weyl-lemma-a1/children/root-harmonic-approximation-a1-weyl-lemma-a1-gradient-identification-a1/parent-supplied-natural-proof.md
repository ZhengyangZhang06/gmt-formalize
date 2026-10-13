# Parent-supplied natural-language proof

- Parent DAG node: `root.harmonic_approximation-a1.weyl_lemma-a1`
- Child DAG node: `root.harmonic_approximation-a1.weyl_lemma-a1.gradient_identification-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation (used throughout). B_s := ball(0,s) (open), B := B_1, |.| the Euclidean norm, <.,.> the inner product of R^n = EuclideanSpace R (Fin n). A test function is zeta in C^infinity(R^n) (ContDiff R (top : N-infinity)) with compact support and tsupport zeta contained in B. (e_i)_{i<n} is the standard orthonormal basis (EuclideanSpace.basisFun). For a function f differentiable at x and v in R^n, Df(x)[v] := fderiv R f x v and d_v f(x) := Df(x)[v]; d_i := d_{e_i}. <grad f(x), v> = Df(x)[v] (gradient is the Riesz transport of fderiv; InnerProductSpace.toDual_symm_apply). D^2 f(x)[a,b] := iteratedFDeriv R 2 f x ![a,b] = (D(Df)(x)[a])[b] (iteratedFDeriv_two_apply). For f in C^2 the Laplacian is Laplacian(f)(x) = sum_i D^2 f(x)[e_i,e_i] (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis with the orthonormal basis (e_i)). Fact (D2): if f is C^2 and e in R^n, the derivative of x -> Df(x)[e] in the direction e equals D^2 f(x)[e,e] (fderiv_clm_apply with the constant vector e, then iteratedFDeriv_two_apply).

Source. This is step 9 of the parent proof (grad u = g a.e. via integration by parts and the fundamental lemma of the calculus of variations). The parent integrates by parts against the globally smooth w_eps, which coincides with u near tsupport zeta; here the same identity int u d_e zeta = - int (d_e u) zeta is obtained directly from the C^1 regularity of u near tsupport zeta, using Mathlib's integration-by-parts lemma, which only requires differentiability of each factor on the topological support of the other.

Proof.
1. Regularity and local integrability. For x in B, u is C^1 at x, so u is differentiable at x and Du is continuous at x (ContDiffAt.continuousAt_fderiv, order 1 != 0). Hence u and grad u are continuous on B (grad u(x) is Du(x) transported by the Riesz isometry), and grad u is locally integrable on B (ContinuousOn.locallyIntegrableOn, B measurable). Since g is in L^2(B) and |B| < infinity, g is integrable on B (MemLp.integrable), hence locally integrable on B (IntegrableOn.locallyIntegrableOn). Therefore F := grad u - g is locally integrable on B. Likewise w is integrable on B.

2. Products with a test function. Let zeta be a test function and K := tsupport zeta, a compact subset of B. If a : R^n -> R is continuous at every point of B (for instance a = u, or a(x) = Du(x)[e] for a fixed e), then x -> a(x) zeta(x) and x -> a(x) Dzeta(x)[e] are continuous on R^n and vanish outside K: at points of B both factors are continuous; a point x outside B is not in K, and on the open neighbourhood R^n \ K of x both zeta and Dzeta vanish (fderiv_of_notMem_tsupport), so the products vanish near x. Being continuous with compact support, these products are integrable on R^n.

3. Integration by parts. Fix a test function zeta and e in R^n. Apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable with the lemma's first function := u, its second function := zeta (not the weak gradient g) and direction v := e. Its hypotheses hold: u is differentiable at every point of tsupport zeta (which lies in B), zeta is differentiable everywhere (in particular on tsupport u), and x -> Du(x)[e] zeta(x), x -> u(x) Dzeta(x)[e] and x -> u(x) zeta(x) are integrable by step 2. It gives
   (3.1) int u(x) Dzeta(x)[e] dx = - int Du(x)[e] zeta(x) dx.

4. Passing to w and to g. The integrand u Dzeta[e] vanishes outside K, which lies in B, so int u Dzeta[e] = int_B u Dzeta[e] = int_B w Dzeta[e], because u = w a.e. on B. The weak-gradient identity int_B w grad zeta = - int_B zeta g, paired with e (integral_inner, or ContinuousLinearMap.integral_comp_comm with innerSL R e under the current imports; w grad zeta and zeta g are integrable on B because w and g are integrable on B and zeta, grad zeta are bounded), gives int_B w(x) Dzeta(x)[e] dx = - int_B zeta(x) <g(x), e> dx, using <grad zeta(x), e> = Dzeta(x)[e]. Since Du[e] zeta vanishes outside B and Du(x)[e] = <grad u(x), e>, (3.1) yields
   int_B zeta(x) <grad u(x), e> dx = int Du(x)[e] zeta(x) dx = - int_B w Dzeta[e] = int_B zeta(x) <g(x), e> dx.
Hence int_B zeta(x) <F(x), e> dx = 0 for every e in R^n.

5. Vector form. zeta F is integrable on B (zeta grad u is continuous with compact support by step 2 applied coordinatewise, and zeta g is integrable on B) and vanishes outside K, which lies in B. Pairing with e commutes with the integral, so <int_{R^n} zeta F, e> = <int_B zeta F, e> = int_B zeta <F, e> = 0 for every e; hence int_{R^n} zeta(x) F(x) dx = 0 (setIntegral_eq_integral_of_forall_compl_eq_zero).

6. Fundamental lemma. Step 5 holds for every C^infinity zeta with compact support and tsupport zeta contained in B, and F is locally integrable on the open set B (step 1). By IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero, F(x) = 0 for almost every x in B, i.e. grad u = g almost everywhere on B (ae_restrict_iff' with the measurable set B). QED

Formalization note. integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable needs the import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts, and integral_inner needs Mathlib.MeasureTheory.Function.L2Space (or use ContinuousLinearMap.integral_comp_comm (innerSL R e)); adding imports to GMT/Ch05/Submission.lean is permitted, as in the parent's formalization note. IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero is available under the current imports.

## Key steps

1. grad u is continuous on B and g is integrable on B, so F := grad u - g is locally integrable on B
2. For a test function zeta, products of zeta or Dzeta with functions continuous on B are continuous with compact support, hence integrable
3. Integration by parts (integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable, differentiability only needed on the other factor's tsupport): int u Dzeta[e] = - int Du[e] zeta
4. u = w a.e. on B and the weak-gradient identity paired with e give int_B zeta <grad u - g, e> = 0 for all e, hence int zeta F = 0
5. Fundamental lemma on the open ball (IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero): grad u = g a.e. on B

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
