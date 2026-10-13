# Parent-supplied natural-language proof

- Parent DAG node: `root.harmonic_approximation-a1.weyl_lemma-a1`
- Child DAG node: `root.harmonic_approximation-a1.weyl_lemma-a1.harmonic_patching-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation (used throughout). B_s := ball(0,s) (open), B := B_1, |.| the Euclidean norm, <.,.> the inner product of R^n = EuclideanSpace R (Fin n). A test function is zeta in C^infinity(R^n) (ContDiff R (top : N-infinity)) with compact support and tsupport zeta contained in B. (e_i)_{i<n} is the standard orthonormal basis (EuclideanSpace.basisFun). For a function f differentiable at x and v in R^n, Df(x)[v] := fderiv R f x v and d_v f(x) := Df(x)[v]; d_i := d_{e_i}. <grad f(x), v> = Df(x)[v] (gradient is the Riesz transport of fderiv; InnerProductSpace.toDual_symm_apply). D^2 f(x)[a,b] := iteratedFDeriv R 2 f x ![a,b] = (D(Df)(x)[a])[b] (iteratedFDeriv_two_apply). For f in C^2 the Laplacian is Laplacian(f)(x) = sum_i D^2 f(x)[e_i,e_i] (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis with the orthonormal basis (e_i)). Fact (D2): if f is C^2 and e in R^n, the derivative of x -> Df(x)[e] in the direction e equals D^2 f(x)[e,e] (fderiv_clm_apply with the constant vector e, then iteratedFDeriv_two_apply).

Source. These are steps 6, 7 and 8 of the parent proof (compatibility of the local representatives, the patched definition of u and its harmonicity, and u = w a.e.), stated for an arbitrary family of local harmonic representatives.

Proof.
0. Choice and continuity. For each eps in (0, 1/2) choose v_eps as in the hypothesis (for instance via Classical.choose on the statement "exists v, (0 < eps -> eps < 1/2 -> property)", taking any function when eps is out of range). Each v_eps is harmonic, hence C^2 and in particular continuous, at every point of B_{1-eps} (HarmonicOnNhd.continuousOn).

1. Compatibility. Let eps, eps' be in (0, 1/2), m := max(eps, eps') and U := B_{1-2m} (open). Then v_eps = v_eps' at every point of U.
Proof: U is contained in B_{1-2eps}, which is contained in B_{1-eps}; likewise for eps'. So v_eps and v_eps' are continuous on U, and both equal w almost everywhere on U, hence v_eps = v_eps' almost everywhere on U. Lebesgue measure charges every nonempty open set, so two functions that are continuous on the open set U and a.e. equal on U agree at every point of U (Measure.eqOn_open_of_ae_eq).

2. Definition of u. For x in B put e(x) := (1 - |x|)/4, which lies in (0, 1/4], and u(x) := v_{e(x)}(x); for x outside B put u(x) := 0.

3. u is harmonic at every point of B. Fix x0 in B and put d0 := 1 - |x0| in (0, 1] and eps0 := e(x0) = d0/4 in (0, 1/4]. Let x be in ball(x0, d0/4). Then
 - |x| < |x0| + d0/4 = 1 - 3 d0/4 < 1, so x lies in B;
 - |e(x) - eps0| = | |x0| - |x| | / 4 <= |x - x0|/4 < d0/16, so m := max(e(x), eps0) < eps0 + d0/16 = 5 d0/16;
 - hence 1 - 2m > 1 - 5 d0/8 > 1 - 3 d0/4 > |x|, i.e. x lies in B_{1-2m}.
By step 1 (with eps = e(x) and eps' = eps0), u(x) = v_{e(x)}(x) = v_{eps0}(x). So u = v_{eps0} on the neighbourhood ball(x0, d0/4) of x0. Since |x0| = 1 - d0 < 1 - d0/4 = 1 - eps0, x0 lies in B_{1-eps0}, so v_{eps0} is harmonic at x0; therefore u is harmonic at x0 (InnerProductSpace.harmonicAt_congr_nhds). As x0 in B was arbitrary, InnerProductSpace.HarmonicOnNhd u B.

4. u = w almost everywhere on B. For each integer m >= 3, 1/m lies in (0, 1/2), so the set N_m := {x in B_{1-2/m} : v_{1/m}(x) != w(x)} is Lebesgue-null by hypothesis. N := union over m >= 3 of N_m is null (countable union). Let x be in B \ N. Choose an integer m >= 3 with 1/m <= e(x) (possible since e(x) > 0). Then 1 - 2/m >= 1 - 2 e(x) = (1 + |x|)/2 > |x|, so x lies in B_{1-2/m}; and max(e(x), 1/m) = e(x), so x lies in B_{1-2 max(e(x), 1/m)}. By step 1, u(x) = v_{e(x)}(x) = v_{1/m}(x), and since x is not in N_m, v_{1/m}(x) = w(x). Hence {x in B : u(x) != w(x)} is contained in the null set N, i.e. u = w almost everywhere on B (ae_restrict_iff' with the measurable set B, ae_all_iff for the countable family). QED

## Key steps

1. Choose v_eps for each eps in (0, 1/2); each is continuous on B_{1-eps}
2. Compatibility: v_eps = v_eps' everywhere on B_{1-2max(eps,eps')} (a.e. equal and continuous on an open set, Measure.eqOn_open_of_ae_eq)
3. Define u(x) := v_{e(x)}(x) with e(x) = (1-|x|)/4 on B, u := 0 off B
4. Near x0 in B, u = v_{eps0} on ball(x0, d0/4) with eps0 = d0/4, so u is harmonic at x0 (harmonicAt_congr_nhds)
5. u = w off the null set union_{m>=3} {x in B_{1-2/m} : v_{1/m}(x) != w(x)}

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
