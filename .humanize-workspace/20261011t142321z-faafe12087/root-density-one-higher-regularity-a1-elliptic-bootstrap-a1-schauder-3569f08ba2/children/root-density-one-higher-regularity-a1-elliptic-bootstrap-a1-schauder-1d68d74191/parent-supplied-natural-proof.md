# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.liouville-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.liouville-a1.dir_deriv-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof (partial derivatives of smooth global solutions are global solutions), with e_s replaced by an arbitrary vector v. Parent steps (i), (ii)+(iv) and (iii) appear below as steps 1, 2-3 and 4. Steps 2-3 are the parent's difference-quotient limit, packaged as differentiation under the integral sign of h -> integral of A[DV(x + h v)][Dzeta(x)] dx at h = 0. Indeed, (F(h) - F(0))/h is exactly the parent's integral of A[DV_h][Dzeta].

0. Setup. D^2V(y) := the derivative at y of DV. Since V is C^2, DV is C^1, so DV is differentiable everywhere and y -> D^2V(y)(v) in L is continuous.
 Fix zeta : R^n -> R^l, C^1 with compact support. Dzeta is continuous with compact support T := tsupport(Dzeta), and Dzeta(x) = 0 for x outside T.
 For every continuous G : R^n -> L, the function x -> A[G(x)][Dzeta(x)] is continuous with support in T, hence integrable.

1. Translated equation (parent (i)). For every h in R, F(h) := integral of A[DV(x + h v)][Dzeta(x)] dx = 0.
 The map zeta_h(x) := zeta(x - h v) is C^1, has compact support (it is zeta composed with a translation, which is a homeomorphism), and Dzeta_h(x) = Dzeta(x - h v).
 The hypothesis gives integral of A[DV(x)][Dzeta(x - h v)] dx = 0.
 By translation invariance of Lebesgue measure (substitute x -> x + h v), integral of A[DV(x + h v)][Dzeta(x)] dx = integral of A[DV(x)][Dzeta(x - h v)] dx = 0.

2. Differentiation under the integral sign (parent (ii) and (iv)). Put F(h, x) := A[DV(x + h v)][Dzeta(x)] and F'(h, x) := A[D^2V(x + h v)(v)][Dzeta(x)].
 (a) For fixed x, h -> F(h, x) has derivative F'(h, x) at every h. The map h -> x + h v has derivative v, and DV is differentiable at x + h v with derivative D^2V(x + h v). So h -> DV(x + h v) has derivative D^2V(x + h v)(v) in L. Compose with the continuous linear form P -> A[P][Dzeta(x)].
 (b) For each h, x -> F(h, x) is continuous, hence measurable. x -> F(0, x) is integrable (setup), and x -> F'(0, x) is continuous.
 (c) Domination for |h| < 1. Let K' := {y : dist(y, T) <= |v|}, the closed |v|-thickening of T, which is compact. The map y -> A[D^2V(y)(v)] in L(L, R) is continuous, so M := sup over y in K' of ||A[D^2V(y)(v)]|| is finite. Put M+ := max(M, 0).
  If x is in T and |h| < 1, then x + h v is in K', so |F'(h, x)| <= ||A[D^2V(x + h v)(v)]|| |Dzeta(x)| <= M+ |Dzeta(x)|.
  If x is not in T, then Dzeta(x) = 0 and F'(h, x) = 0.
  The bound x -> M+ |Dzeta(x)| is continuous with compact support, hence integrable.
 (d) By differentiation under the integral sign (hasDerivAt_integral_of_dominated_loc_of_deriv_le, on the neighbourhood B_1(0) of h = 0), h -> integral of F(h, x) dx has derivative at h = 0 equal to integral of F'(0, x) dx = integral of A[D^2V(x)(v)][Dzeta(x)] dx.

3. By step 1, h -> integral of F(h, x) dx is identically 0, so its derivative at 0 is 0. By uniqueness of derivatives, integral of A[D^2V(x)(v)][Dzeta(x)] dx = 0.

4. Identification (parent (iii)). For every x, D(d_vV)(x) = D^2V(x)(v) in L.
 The map d_vV is DV followed by the continuous linear evaluation P -> P v, so by the chain rule D(d_vV)(x)(w) = D^2V(x)(w)(v) for every w.
 Since V is C^2, the sibling lemma snd_deriv_symm gives D^2V(x)(w)(v) = D^2V(x)(v)(w). Hence D(d_vV)(x)(w) = D^2V(x)(v)(w) for all w.

5. Conclusion. By step 4, integral of A[D(d_vV)(x)][Dzeta(x)] dx = integral of A[D^2V(x)(v)][Dzeta(x)] dx, which is 0 by step 3. QED

Lean implementation note: a kernel-checked single-declaration proof of exactly this frozen type, citing Submission.dohr_eb_sch_liou_snd_deriv_symm, is at /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/dohr_eb_sch_liou/dohr_eb_sch_liou_dir_deriv_solution.lean.txt (sha256 53acef55c3dcffe9c45bf4dea28c27f2bf072e53e68beeb46a07c5b5498927d9). It compiles at the frozen proof base imports with no set_option, uses only the axioms propext, Classical.choice and Quot.sound, and passes check_source_delta. Pitfalls it handles:
- ‖A‖ and A.hasFDerivAt on the bilinear-form type fail at default instance depth. Use (A P).le_opNorm Q for the bound in 2(c), (A.flip q).hasFDerivAt.comp_hasDerivAt for 2(a), and (ContinuousLinearMap.apply ℝ (Rn ℓ) v).hasFDerivAt.comp for step 4.
- Translation uses fderiv_comp_add_right, HasCompactSupport.comp_homeomorph (Homeomorph.addRight _) and integral_add_right_eq_self.
- Do not name hypotheses with 'def' right after a prime (such as hF'def): the leaf rule rejects them.

## Key steps

1. translated equation: F(h) := integral of A[DV(x + h v)][Dzeta(x)] dx = 0 for all h, by translation invariance and the test function zeta(. - h v)
2. domination of the h-derivative A[D^2V(x + h v)(v)][Dzeta(x)] on |h| < 1 by M+ |Dzeta(x)|, using compactness of the |v|-thickening of tsupport Dzeta
3. differentiation under the integral sign: F'(0) = integral of A[D^2V(x)(v)][Dzeta(x)] dx, and F = 0 gives F'(0) = 0
4. D(d_vV)(x) = D^2V(x)(v) by the chain rule and snd_deriv_symm, which gives the claim

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Submission.lean`
- `git show e821d88672aa1de5d3985dce6544d905efe7420d:GMT/Ch05/Submission.lean (frozen proof base of this node; identical to the contract, 463 lines)`
- `rg -l -i 'liouville|caccioppoli|mollif|convolution' <snapshot>/project and the pinned simongmt package; rg -n -i 'theorem .*liouville' <snapshot>/mathlib/Mathlib`
- `grep pinned Mathlib for ContDiffBump.normed/integral_normed/support_normed_eq, HasCompactSupport.contDiff_convolution_left, convolution_def, hasFDerivAt_integral_of_dominated_of_fderiv_le, hasDerivAt_integral_of_dominated_loc_of_deriv_le, ContinuousLinearMap.integral_comp_comm, integral_integral_swap, Continuous.integrable_of_hasCompactSupport, integral_add_right_eq_self, fderiv_comp_add_right, hasFDerivAt_comp_sub, support_fderiv_subset, ContDiffAt.isSymmSndFDerivAt, is_const_of_deriv_eq_zero, Measure.addHaar_ball_of_pos, lintegral_eq_zero_iff, Measure.eqOn_open_of_ae_eq, norm_image_sub_le_of_norm_deriv_le_segment', Convex.norm_image_sub_le_of_norm_fderiv_le', ContDiff.continuous_fderiv_apply, ContinuousLinearMap.le_opENorm`
- `lake env lean Checks/Avail.lean (#check of those names under the frozen contract imports only)`
- `python3 gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch05.main_theorem')`
- `python3 scan of dag.json and issue-workers.json for dohr_eb_sch_liou* names and for mollifier, convolution, Liouville, difference-quotient and Caccioppoli nodes`
- `ast extraction of check_source_delta from /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py and replay on every insertion (leafsim.py)`
- `lake build GMT.Ch05.Submission (scratch with the six children, a Caccioppoli stand-in and the parent assembly); lake env lean Checks/Sol_<name>.lean for the six children and the parent; lake env lean Checks/AssemblyParent.lean and Checks/AssemblyAbstract.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Operator/NNNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/NumberTheory/ArithmeticFunction/Liouville.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`

PIN AND BASE. The snapshot pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The snapshot Contract.lean is byte-identical to the workspace Submission.lean and to the node's frozen proof base e821d886.

NO MATCH FOR THE THEOREM. Neither the project nor simongmt contains a Liouville or Caccioppoli theorem for elliptic systems or a mollification lemma for weak solutions. Mathlib's 'Liouville' hits are number theory and complex analysis only. simongmt's DistributionalConstancy.lean only handles scalar functions with zero weak derivative. So the Liouville theorem must be proved, as in the children.

TOOLS AVAILABLE AT THE FROZEN IMPORTS (checked with #check):
- ContDiffBump basics, HasCompactSupport.contDiff_convolution_left, convolution;
- hasFDerivAt_integral_of_dominated_of_fderiv_le and hasDerivAt_integral_of_dominated_loc_of_deriv_le;
- integral_integral_swap, ContinuousLinearMap.integral_comp_comm, integral_add_right_eq_self, fderiv_comp_add_right;
- Measure.addHaar_ball_of_pos, Measure.eqOn_open_of_ae_eq, lintegral_eq_zero_iff;
- norm_image_sub_le_of_norm_deriv_le_segment', ContDiff.continuous_fderiv_apply, is_const_of_deriv_eq_zero.

NOT IMPORTED: IsSymmSndFDerivAt, ContDiffAt.isSymmSndFDerivAt, ContDiffBump.normed and integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable.

LEAF RULE. leaf_verification.py's check_source_delta requires one contiguous single-theorem insertion and rejects import, set_option, and other declarations. Because of the missing imports and this rule, symmetry of D^2V is its own child, and the mollifier is normalized by hand.

INSTANCE-DEPTH PITFALLS (set_option maxSynthPendingDepth 3 is not allowed):
- ‖A‖ and A.hasFDerivAt on the bilinear-form type fail; (A P).le_opNorm Q and (A.flip q).hasFDerivAt work.
- ContinuousSub and sub_self fail on L(R^n, L).
- rw [← smul_sub] fails on L inside goals.
The stored proofs work around all of these.

RESULT. All six children are proved outright as single theorems at the frozen base, with only the standard axioms, and they pass the leaf rule. The frozen parent type follows from them plus the Caccioppoli type. No DAG node carries any proposed name, and no DAG node has an identical type, so nothing is reused.
