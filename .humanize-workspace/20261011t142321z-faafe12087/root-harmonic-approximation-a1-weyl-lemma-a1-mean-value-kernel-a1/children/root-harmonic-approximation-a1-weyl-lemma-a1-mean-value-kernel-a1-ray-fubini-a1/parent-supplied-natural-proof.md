# Parent-supplied natural-language proof

- Parent DAG node: `root.harmonic_approximation-a1.weyl_lemma-a1.mean_value_kernel-a1`
- Child DAG node: `root.harmonic_approximation-a1.weyl_lemma-a1.mean_value_kernel-a1.ray_fubini-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation. Dh(y)[v] := fderiv R h y v. Integrals over R^n are with respect to Lebesgue measure, and int_0^t is the interval integral. This is steps 5 and 6 of the parent proof, stated for a general continuous kernel supported in the closed unit ball.

1. Preliminaries.
   - rho vanishes outside the compact set closedBall(0,1), so rho has compact support.
   - Since h is C^1, it is differentiable and continuous, and y -> Dh(y) is continuous (ContDiff.continuous_fderiv).
   - Hence for every continuous g : R^n -> R, the product z -> rho(z) g(z) is continuous with compact support (HasCompactSupport.mul_right), and therefore integrable (Continuous.integrable_of_hasCompactSupport).
   - In particular z -> rho(z) h(x0 + t z), z -> rho(z) h(x0) and rho are integrable.

2. FTC along a ray. Fix z in R^n. The map sigma -> x0 + sigma z has derivative z at every sigma. By the chain rule (HasFDerivAt.comp_hasDerivAt), sigma -> h(x0 + sigma z) has derivative Dh(x0 + sigma z)[z] at every sigma. This derivative is continuous in sigma, hence interval integrable on [0, t]. By the fundamental theorem of calculus (intervalIntegral.integral_eq_sub_of_hasDerivAt),
   h(x0 + t z) - h(x0) = int_0^t Dh(x0 + sigma z)[z] dsigma.
Multiplying by the constant rho(z) and moving it inside the interval integral (intervalIntegral.integral_const_mul) gives
   (2.1) int_0^t rho(z) Dh(x0 + sigma z)[z] dsigma = rho(z) h(x0 + t z) - rho(z) h(x0).

3. Integrability on the product. Let F(sigma, z) := rho(z) Dh(x0 + sigma z)[z].
   - F is continuous on R x R^n: it is built from products and compositions of continuous maps, including evaluation of the continuous family Dh at the continuous vector z.
   - The set K := [0, t] x closedBall(0,1) is compact. Hence F is integrable on K for the product Lebesgue measure (ContinuousOn.integrableOn_compact).
   - Let (sigma, z) be in (0, t] x R^n but not in K. Then z is not in closedBall(0,1), i.e. |z| > 1, so rho(z) = 0 and F(sigma, z) = 0.
   - Hence F is integrable on (0, t] x R^n (IntegrableOn.of_forall_sdiff_eq_zero). Equivalently, F is integrable with respect to (Lebesgue measure restricted to (0, t]) x (Lebesgue measure on R^n). To see this, rewrite that product as the restriction of the full product measure to (0, t] x R^n (Measure.restrict_prod_eq_prod_univ); note that (0, t] = uIoc 0 t because t >= 0.

4. Fubini. By step 3, Fubini's theorem for an interval integral against an ordinary integral applies (MeasureTheory.intervalIntegral_integral_swap; equivalently integral_integral_swap after intervalIntegral.integral_of_le). It gives
   int_0^t ( int_{R^n} F(sigma, z) dz ) dsigma = int_{R^n} ( int_0^t F(sigma, z) dsigma ) dz.

5. Conclusion. By (2.1), the inner integral on the right equals rho(z) h(x0 + t z) - rho(z) h(x0) for every z. Integrate over z, using the integrability from step 1 (integral_sub, then integral_mul_const for the constant h(x0)):
   int_0^t ( int_{R^n} rho(z) Dh(x0 + sigma z)[z] dz ) dsigma = int rho(z) h(x0 + t z) dz - (int rho) h(x0).
Rearranging gives
   int rho(z) h(x0 + t z) dz = (int rho) h(x0) + int_0^t ( int rho(z) Dh(x0 + sigma z)[z] dz ) dsigma. QED

## Key steps

1. rho has compact support in closedBall(0,1). Products of rho with continuous functions are integrable, and Dh is continuous.
2. For each z, the FTC along sigma -> h(x0 + sigma z) gives int_0^t rho(z) Dh(x0 + sigma z)[z] dsigma = rho(z) h(x0 + t z) - rho(z) h(x0).
3. F(sigma,z) = rho(z) Dh(x0 + sigma z)[z] is continuous and vanishes off [0,t] x closedBall(0,1). Hence it is integrable on (0,t] x R^n.
4. Fubini swaps the interval integral and the R^n integral.
5. Integrate (2.1) over z using integral_sub and integral_mul_const, then rearrange.

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; sha256sum GMT/Ch05/Submission.lean GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Submission.lean`
- `grep -n "^theorem\|^lemma\|^noncomputable def\|^instance\|^def\|notation" <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean`
- `rg -l "laplacian" <snapshot>/mathlib/Mathlib; rg -n "laplacian.*comp|comp.*laplacian" <snapshot>/mathlib/Mathlib`
- `rg -n "Green|green's" <snapshot>/mathlib/Mathlib/Analysis <snapshot>/mathlib/Mathlib/MeasureTheory`
- `rg -l -i "laplacian|mean.value|integral_mul_fderiv_eq_neg" .lake/packages/simongmt/Poincare; rg -n "integral_comp_inv_smul|integral_neg_eq_self|integral_mul_fderiv_eq_neg_fderiv_mul" .lake/packages/simongmt/Poincare; rg -l -i laplacian GMT`
- `grep -rn for the declarations of: integral_comp_inv_smul_of_nonneg, integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable, laplacian_eq_iteratedFDeriv_orthonormalBasis, HasCompactSupport.fderiv_apply, contDiff_infty_iff_deriv, hasStrictFDerivAt_norm_sq, map_smul_univ, sum_repr', ContinuousLinearMap.iteratedFDeriv_comp_right, integral_hasDerivAt_right, integral_eq_sub_of_hasDerivAt, restrict_prod_eq_prod_univ, IntegrableOn.of_forall_sdiff_eq_zero, integral_pos_iff_support_of_nonneg, measure_ball_pos, finrank_euclideanSpace_fin, expNegInvGlue zero_of_nonpos/pos_of_pos/nonneg/contDiff, fderiv_clm_apply, intervalIntegral_integral_swap, integral_inv_eq_self, iteratedFDeriv_comp_add_left, iteratedFDeriv_two_apply, Continuous.integrable_of_hasCompactSupport (in <snapshot>/mathlib/Mathlib)`
- `python3 over dag.json: list of all node lean_name values and statuses; grep -rl <name> .humanize GMT for each of the six proposed names; grep -rhoE '"lean_name": *"[^"]*"' <run dir> | sort -u | wc -l; grep -rhoE '"lean_name": *"mvk[^"]*"' .humanize`
- `lean --root=<scratch>/src -o <scratch>/olean/GMT/Ch05/Submission.olean <copy of frozen GMT/Ch05/Submission.lean>; chk.sh Api1.lean (#check of the cited API); chk.sh TypesFinal.lean; chk.sh CombinedFinal.lean; chk.sh ProofA.lean ProofB.lean ProofC.lean ProofF.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Deriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Deriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-weyl-lemma-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-weyl-lemma-a1-mean-value-kernel-a1/parent-child-handoff.json`
- `/tmp/mvk-decomp-I2XPmk/src/TypesFinal.lean`
- `/tmp/mvk-decomp-I2XPmk/src/CombinedFinal.lean`

Pinned snapshot:
- The manifest pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d.
- The workspace GMT/Ch05/Submission.lean and Contract.lean are byte-identical to the snapshot copy (sha256 c966f51efddb5a68ce15ef2a2a322fd9df0ca69da4626c7acef05b05d1691e12).
- The compile-time Mathlib package is the snapshot revision, so the Lean checks apply to the frozen contract.

No relevant matches:
- Laplacian.lean has no lemma for the Laplacian of a right composition or of a dilation. It only has CLM/CLE composition on the left, add/sub/neg/smul, and congr.
- No Mathlib file states Green's identity.
- The only Laplacian integration-by-parts lemma is integral_clm_comp_laplacian_right_eq_left (SchwartzSpace/Deriv.lean). It is for Schwartz functions, so it does not apply to a C^2 function paired with a compactly supported C^1 function.
- simongmt has no Laplacian, n-dimensional mean value or integration-by-parts API; its single hit, in FirstVariation.lean, is a comment about a 1D mean-value step.
- The project's GMT sources do not mention the Laplacian.
- So the children laplacian_rescale and green_identity are genuinely new.

Usable API, all located and used in the scratch proofs:
- SmoothTransition.lean: expNegInvGlue.contDiff, nonneg, zero_of_nonpos, pos_of_pos.
- InnerProductSpace/Calculus.lean: hasStrictFDerivAt_norm_sq. contDiff_norm_sq is also used.
- Bochner/Basic.lean: integral_pos_iff_support_of_nonneg.
- OpenPos.lean: Metric.measure_ball_pos.
- LocallyIntegrable.lean: Continuous.integrable_of_hasCompactSupport.
- FundThmCalculus.lean: intervalIntegral.integral_hasDerivAt_right and integral_eq_sub_of_hasDerivAt.
- ContDiff/Deriv.lean: contDiff_infty_iff_deriv.
- Integral/Prod.lean: MeasureTheory.intervalIntegral_integral_swap.
- Measure/Prod.lean: Measure.restrict_prod_eq_prod_univ.
- IntegrableOn.lean: IntegrableOn.of_forall_sdiff_eq_zero.
- LineDeriv/IntegrationByParts.lean: integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable. This file is not imported by the contract, and green_identity records the needed import.
- Laplacian.lean: InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis.
- PiL2.lean: OrthonormalBasis.sum_repr' and finrank_euclideanSpace_fin.
- FDeriv/Const.lean: HasCompactSupport.fderiv_apply.
- FDeriv/CompCLM.lean: fderiv_clm_apply.
- FTaylorSeries.lean: iteratedFDeriv_two_apply and iteratedFDeriv_comp_add_left.
- ContDiff/Basic.lean: ContinuousLinearMap.iteratedFDeriv_comp_right.
- Multilinear/Basic.lean: ContinuousMultilinearMap.map_smul_univ.
- Haar/NormedSpace.lean: Measure.integral_comp_inv_smul_of_nonneg.
- Group/Integral.lean: integral_neg_eq_self, the additive form of integral_inv_eq_self.

Lean evidence:
- TypesFinal.lean uses the frozen imports only, with the children as sorry stubs. It elaborates the six exact child types and proves the exact frozen parent type from them; sorryAx appears only through the stubs.
- CombinedFinal.lean adds Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts and proves all six children and the parent. Every axiom list is [propext, Classical.choice, Quot.sound].
- An independent reviewer re-ran both files and confirmed the instances: PiLp inner product, WithLp smul, Lebesgue volume via measureSpaceOfInnerProductSpace, and InnerProductSpace.instLaplacian.

Name check: none of the six proposed names occurs in the run's artifacts (421 distinct lean_name values) or in the GMT sources.
