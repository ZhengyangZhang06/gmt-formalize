# Parent-supplied natural-language proof

- Parent DAG node: `root.harmonic_approximation-a1.weyl_lemma-a1.mean_value_kernel-a1`
- Child DAG node: `root.harmonic_approximation-a1.weyl_lemma-a1.mean_value_kernel-a1.green_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation.
   - (e_i)_{i<n} is the standard orthonormal basis EuclideanSpace.basisFun (Fin n) R.
   - For f differentiable at z: Df(z)[v] := fderiv R f z v and d_i f(z) := Df(z)[e_i].
   - D^2 f(z)[a,b] := iteratedFDeriv R 2 f z ![a,b].
   - Integrals over R^n are with respect to Lebesgue measure, which is an additive Haar measure.
This is the integration-by-parts part of step 7 of the parent proof.

1. Expansion of w. For every z, w(z) = sum_i <e_i, w(z)> e_i (expansion in an orthonormal basis, OrthonormalBasis.sum_repr'). By symmetry of the real inner product and the hypothesis on w, <e_i, w(z)> = <w(z), e_i> = DPsi(z)[e_i] = d_i Psi(z). By linearity of DH(z),
   (1.1) DH(z)[w(z)] = sum_i d_i H(z) d_i Psi(z).

2. Regularity and integrability.
   - Since H is C^2, z -> DH(z) is C^1 (ContDiff.fderiv_right). So for each i, f_i(z) := d_i H(z) = DH(z)[e_i] is C^1, being a C^1 operator-valued map applied to a constant vector (ContDiff.clm_apply). In particular f_i is differentiable everywhere and z -> Df_i(z)[e_i] is continuous.
   - z -> D^2 H(z)[e_i, e_i] is continuous: apply ContDiff.continuous_iteratedFDeriv with order 2 <= 2, then the continuous evaluation at the fixed pair ![e_i, e_i].
   - Since Psi is C^1, it is differentiable everywhere and DPsi is continuous. Since Psi has compact support, so does z -> d_i Psi(z) (HasCompactSupport.fderiv_apply).
   - Hence each of the functions d_i H d_i Psi, f_i Psi, (z -> Df_i(z)[e_i]) Psi and (z -> D^2 H(z)[e_i,e_i]) Psi is continuous with compact support, since it has a compactly supported factor (HasCompactSupport.mul_left). So each is integrable (Continuous.integrable_of_hasCompactSupport).

3. Second derivative identity. For every i and z, Df_i(z)[e_i] = D^2 H(z)[e_i, e_i]. Indeed, f_i(y) = DH(y)[e_i] is the differentiable operator-valued map y -> DH(y) applied to the constant vector e_i. By the product rule for such applications (fderiv_clm_apply, where the constant factor has derivative 0), Df_i(z)[a] = (D(DH)(z)[a])[e_i] for all a. Also, iteratedFDeriv_two_apply gives D^2 H(z)[e_i, e_i] = (D(DH)(z)[e_i])[e_i].

4. Integration by parts in the direction e_i. Apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts) with f = f_i, g = Psi, v = e_i and Lebesgue measure. Its hypotheses are:
   - integrability of z -> Df_i(z)[e_i] Psi(z), of z -> f_i(z) d_i Psi(z) and of z -> f_i(z) Psi(z), given by step 2;
   - differentiability of f_i at every point of tsupport Psi and of Psi at every point of tsupport f_i, given by step 2 (both are differentiable everywhere).
Together with step 3 it yields
   (4.1) int d_i H(z) d_i Psi(z) dz = - int Df_i(z)[e_i] Psi(z) dz = - int D^2 H(z)[e_i, e_i] Psi(z) dz.

5. Summation. Integrate (1.1). The finitely many summands are integrable (step 2), so the integral commutes with the finite sum (integral_finsetSum). Apply (4.1) to each summand. The summands D^2 H[e_i,e_i] Psi are integrable (step 2), so the sum can be moved back inside:
   int DH(z)[w(z)] dz = sum_i int d_i H d_i Psi = sum_i ( - int D^2 H(z)[e_i,e_i] Psi(z) dz ) = - int ( sum_i D^2 H(z)[e_i,e_i] ) Psi(z) dz.

6. The Laplacian. For every z, Laplacian(H)(z) = sum_i D^2 H(z)[e_i, e_i] (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis with the orthonormal basis (e_i)). Hence (sum_i D^2 H(z)[e_i,e_i]) Psi(z) = Laplacian(H)(z) Psi(z) (Finset.sum_mul), and step 5 becomes
   int DH(z)[w(z)] dz = - int Laplacian(H)(z) Psi(z) dz. QED

Formalization note. integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable lives in Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts, which the frozen contract does not import. Add `import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts` to GMT/Ch05/Submission.lean, as the parent's formalization note permits. Everything else used above is available under the current imports.

## Key steps

1. Expand w(z) in the standard orthonormal basis: DH(z)[w(z)] = sum_i d_iH(z) d_iPsi(z).
2. Regularity: d_iH is C^1, D^2H[e_i,e_i] is continuous, and d_iPsi has compact support. So all relevant products are integrable.
3. Second derivative identity: D(d_iH)(z)[e_i] = D^2H(z)[e_i,e_i].
4. Integration by parts in direction e_i: int d_iH d_iPsi = - int D^2H[e_i,e_i] Psi.
5. Sum over i and use Laplacian(H) = sum_i D^2H[e_i,e_i].

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
