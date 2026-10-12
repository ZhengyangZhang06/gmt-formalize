# Parent-supplied natural-language proof

- Parent DAG node: `root.harmonic_approximation-a1.weyl_lemma-a1.mean_value_kernel-a1`
- Child DAG node: `root.harmonic_approximation-a1.weyl_lemma-a1.mean_value_kernel-a1.kernel_potential-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation. |.| is the Euclidean norm and <.,.> the inner product of R^n = EuclideanSpace R (Fin n); integrals over R^n are with respect to Lebesgue measure (volume); Df(z)[v] := fderiv R f z v. This is the construction in steps 1-3 of the parent proof.

1. The profile E. For sigma in R put E(sigma) := expNegInvGlue(1 - sigma). The function expNegInvGlue is C^infinity (expNegInvGlue.contDiff), nonnegative (expNegInvGlue.nonneg), equal to 0 on (-infinity, 0] (expNegInvGlue.zero_of_nonpos) and positive on (0, infinity) (expNegInvGlue.pos_of_pos). Since sigma -> 1 - sigma is C^infinity, E is C^infinity and in particular continuous. Also E >= 0, E(sigma) = 0 for sigma >= 1 (because then 1 - sigma <= 0), and E(sigma) > 0 for sigma < 1.

2. The unnormalized kernel. Put rho0(z) := E(|z|^2). Because z -> |z|^2 is C^infinity (contDiff_norm_sq), rho0 is C^infinity. If |z| >= 1 then |z|^2 >= 1 and rho0(z) = 0. If |z| < 1 then |z|^2 < 1 and rho0(z) > 0. Moreover rho0 >= 0 everywhere. So rho0 vanishes outside the compact set closedBall(0,1) and has compact support (HasCompactSupport.intro with isCompact_closedBall). Being continuous, it is integrable (Continuous.integrable_of_hasCompactSupport).

3. Positivity of the mass. Let I0 := int rho0. Since rho0 >= 0 and rho0 is integrable, I0 > 0 if and only if the support of rho0 has positive Lebesgue measure (integral_pos_iff_support_of_nonneg). By step 2 the open unit ball ball(0,1) is contained in the support of rho0. It has positive Lebesgue measure, because Lebesgue measure is positive on nonempty open sets (Metric.measure_ball_pos). By monotonicity of measure the support has positive measure, so I0 > 0.

4. The normalized kernel rho. Put c := I0^{-1} > 0 and rho(z) := c E(|z|^2) = c rho0(z).
   - rho is C^infinity, as a constant multiple of rho0.
   - rho(z) = 0 for |z| >= 1, by step 2.
   - rho is even: rho(-z) = c E(|-z|^2) = c E(|z|^2) = rho(z), because |-z| = |z|.
   - int rho = c int rho0 = I0^{-1} I0 = 1. Pull the constant out with integral_const_mul and use I0 != 0.

5. The one-variable primitive. Put P(sigma) := int_1^sigma E(s) ds (interval integral). E is continuous. So by the fundamental theorem of calculus (intervalIntegral.integral_hasDerivAt_right), P has derivative E(sigma) at every sigma. The hypotheses of that lemma follow from continuity of E: Continuous.intervalIntegrable, Continuous.stronglyMeasurableAtFilter and Continuous.continuousAt. Hence P is differentiable with deriv P = E. Since E is C^infinity, P is C^infinity (contDiff_infty_iff_deriv). If sigma >= 1, then E vanishes on [1, sigma] by step 1, so P(sigma) = int_1^sigma 0 ds = 0 (intervalIntegral.integral_congr, then the integral of 0).

6. The potential Psi. Put Psi(z) := (c/2) P(|z|^2). It is C^infinity: a constant times the composition of the C^infinity maps z -> |z|^2 and P. If |z| >= 1 then |z|^2 >= 1, so Psi(z) = (c/2) P(|z|^2) = 0 by step 5.

7. The derivative of Psi. The map z -> |z|^2 has derivative v -> 2<z, v> at z (hasStrictFDerivAt_norm_sq, or HasFDerivAt.norm_sq applied to the identity). By the chain rule (HasDerivAt.comp_hasFDerivAt with step 5), z -> P(|z|^2) has derivative v -> E(|z|^2) 2<z, v> at z. Multiplying by the constant c/2 (HasFDerivAt.const_mul), Psi has derivative v -> (c/2) E(|z|^2) 2<z, v> at z. Therefore, for all z, v,
   DPsi(z)[v] = (c/2) E(|z|^2) 2<z, v> = c E(|z|^2) <z, v> = rho(z) <z, v>.

8. Conclusion. Take rho from step 4 and Psi from step 6. Both are C^infinity and vanish when |z| >= 1 (steps 4 and 6). rho is even and has integral 1 (step 4). DPsi(z)[v] = rho(z)<z, v> for all z, v (step 7). This proves the statement for every n; no lower bound on n is used. QED

## Key steps

1. E(sigma) := expNegInvGlue(1 - sigma) is C^infinity, nonnegative, zero for sigma >= 1 and positive for sigma < 1.
2. rho0(z) := E(|z|^2) is C^infinity, supported in closedBall(0,1) and positive on ball(0,1). Hence it is integrable and I0 := int rho0 > 0.
3. rho := I0^{-1} rho0 is C^infinity, vanishes for |z| >= 1, is even, and has integral 1.
4. P(sigma) := int_1^sigma E satisfies P' = E (FTC). Hence P is C^infinity, and P = 0 on [1, infinity).
5. Psi(z) := (c/2) P(|z|^2) is C^infinity and vanishes for |z| >= 1. By the chain rule, DPsi(z)[v] = (c/2) E(|z|^2) 2<z,v> = rho(z)<z,v>.

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
