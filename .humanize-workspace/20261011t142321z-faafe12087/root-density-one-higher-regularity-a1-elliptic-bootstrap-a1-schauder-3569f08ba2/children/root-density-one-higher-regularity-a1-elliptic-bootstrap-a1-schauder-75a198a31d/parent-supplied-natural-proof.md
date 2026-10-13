# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.liouville-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.liouville-a1.mollify-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 of the parent proof (mollification), with every detail filled in. The parent's normalized bump (ContDiffBump.normed) is not imported at the frozen proof base, so step 1 normalizes it by hand.
Conventions. Integrals are over R^n with Lebesgue measure, which is invariant under translations. For a C^1 map f, Df(x) is in L. Integrals of L-valued or R^l-valued functions are Bochner integrals. A continuous function with compact support is integrable.

1. Mollifier. Let b be the smooth bump centred at 0 with inner radius eps/2 and outer radius eps (ContDiffBump (0 : Rn n) with rIn = eps/2, rOut = eps).
 b is C^infinity, 0 <= b <= 1, its support is the open ball B_eps(0), and it has compact support.
 Its integral is positive: b >= 0, b is integrable, and its support B_eps(0) has positive Lebesgue measure (integral_pos_iff_support_of_nonneg).
 Put c := (integral of b)^{-1} > 0 and phi := c b. Then phi is C^infinity, phi >= 0, phi(z) = 0 whenever |z| >= eps, phi has compact support, and the integral of phi is 1.
 For every continuous g from R^n to a real normed space, z -> phi(z) g(z) is continuous with compact support, hence integrable.

2. Definition. V(x) := integral of phi(z) W(x - z) dz. This is the convolution of phi and W for the bilinear map (a, w) -> a w: MeasureTheory.convolution phi W (ContinuousLinearMap.lsmul ℝ ℝ) volume, unfolded by convolution_def.

3. Smoothness. W is continuous, hence locally integrable, and phi is C^infinity with compact support. So V is C^infinity (HasCompactSupport.contDiff_convolution_left, with smoothness order ⊤ : ℕ∞).

4. Derivative formula: DV(x0) = integral of phi(z) DW(x0 - z) dz for every x0. Apply differentiation under the integral sign (hasFDerivAt_integral_of_dominated_of_fderiv_le) to F(x, z) := phi(z) W(x - z) and F'(x, z) := phi(z) DW(x - z), on the neighbourhood B_1(x0).
 (a) z -> F(x, z) is continuous for every x, z -> F(x0, z) is integrable (step 1), and z -> F'(x0, z) is continuous.
 (b) Bound. DW is continuous, so some M_W >= 0 bounds ||DW|| on the compact ball closedBall(x0, 1 + eps). Let x be in B_1(x0).
  If phi(z) = 0, then F'(x, z) = 0.
  Otherwise |z| < eps and |x - z - x0| <= |x - x0| + |z| <= 1 + eps, so ||F'(x, z)|| <= M_W |phi(z)|.
  The bound z -> M_W |phi(z)| is integrable.
 (c) For every z and x, x -> F(x, z) has derivative F'(x, z) at x: the translation x -> x - z has derivative the identity (hasFDerivAt_comp_sub), then multiply by the constant phi(z).
 Hence V has derivative (integral of F'(x0, z) dz) at x0, and DV(x0) equals that integral.

5. Hoelder bound (i). Let x, y be in R^n. By step 4 and linearity, DV(x) - DV(y) = integral of phi(z)(DW(x - z) - DW(y - z)) dz.
 For every z, ||phi(z)(DW(x - z) - DW(y - z))|| = phi(z) ||DW(x - z) - DW(y - z)|| <= phi(z) K |(x - z) - (y - z)|^alpha = phi(z) K |x - y|^alpha.
 By the norm bound for Bochner integrals (norm_integral_le_of_norm_le), ||DV(x) - DV(y)|| <= integral of phi(z) K |x - y|^alpha dz = K |x - y|^alpha.

6. Approximation (ii). Since the integral of phi is 1, DW(x) = integral of phi(z) DW(x) dz. Hence DV(x) - DW(x) = integral of phi(z)(DW(x - z) - DW(x)) dz.
 Fix z. If phi(z) = 0, the integrand is 0. Otherwise |z| < eps, and ||phi(z)(DW(x - z) - DW(x))|| <= phi(z) K |(x - z) - x|^alpha = phi(z) K |z|^alpha <= phi(z) K eps^alpha. This uses that t -> t^alpha is monotone on [0, infinity) for alpha > 0, and K >= 0.
 Therefore ||DV(x) - DW(x)|| <= integral of phi(z) K eps^alpha dz = K eps^alpha.

7. Weak equation (iii). Let zeta be C^1 with compact support. Dzeta is continuous and has compact support T := tsupport(Dzeta), and Dzeta = 0 off T.
 (a) For each x, P -> A[P][Dzeta(x)] is a continuous linear form on L. Continuous linear maps commute with Bochner integrals (ContinuousLinearMap.integral_comp_comm). With step 4 and A[s P][Q] = s A[P][Q], this gives A[DV(x)][Dzeta(x)] = integral of phi(z) A[DW(x - z)][Dzeta(x)] dz.
 (b) Put H(x, z) := phi(z) A[DW(x - z)][Dzeta(x)] on R^n x R^n. H is continuous. It vanishes outside the compact set T x tsupport(phi): if x is not in T then Dzeta(x) = 0, and if z is not in tsupport(phi) then phi(z) = 0. So H is integrable for the product measure, and Fubini (integral_integral_swap) lets us exchange the order: integral over x of (integral over z of H) = integral over z of (integral over x of H).
 (c) Fix z. Then integral over x of H(x, z) = phi(z) times integral of A[DW(x - z)][Dzeta(x)] dx.
  By translation invariance (substitute x -> x + z; integral_add_right_eq_self), the latter integral equals integral of A[DW(x)][Dzeta(x + z)] dx.
  The map zeta_z := (x -> zeta(x + z)) is C^1, has compact support (composition with the homeomorphism x -> x + z), and Dzeta_z(x) = Dzeta(x + z) (fderiv_comp_add_right).
  The hypothesis applied to zeta_z shows this integral is 0. So integral over x of H(x, z) = 0 for every z.
 (d) By (a), (b) and (c), integral of A[DV(x)][Dzeta(x)] dx = integral over x of (integral over z of H) = integral over z of 0 = 0.

8. Conclusion. V is C^infinity (step 3) and satisfies (i), (ii) and (iii) by steps 5, 6 and 7. QED

Lean implementation note: a kernel-checked single-declaration proof of exactly this frozen type is at /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/dohr_eb_sch_liou/dohr_eb_sch_liou_mollify.lean.txt (sha256 2180c0598597761b280f698df1c478f2a5a6732b7edecc23accdf8333c10a372). It compiles at the frozen proof base imports with no set_option and no extra import, uses only the axioms propext, Classical.choice and Quot.sound, and passes check_source_delta. Pitfalls it handles:
- Write MeasureTheory.convolution explicitly; the ⋆ notation is scoped.
- rw [← smul_sub] on L fails inside elaborated goals. State have hs : φ z • a - φ z • b = φ z • (a - b) := (smul_sub _ _ _).symm and rewrite with hs.
- Use (A.flip (fderiv ℝ ζ x)).integral_comp_comm for 7(a).
- Give the product measure explicitly: Continuous.integrable_of_hasCompactSupport (μ := (volume : Measure (Rn n)).prod volume).

## Key steps

1. phi := (integral of b)^{-1} b for the smooth bump b with radii eps/2 < eps: smooth, >= 0, supported in B_eps(0), integral 1
2. V := phi * W is C^infinity (contDiff_convolution_left)
3. DV(x) = integral of phi(z) DW(x - z) dz by dominated differentiation under the integral sign
4. Hoelder bound and the approximation |DV - DW| <= K eps^alpha from the norm bound for Bochner integrals
5. weak equation: pull the linear form inside, apply Fubini to the compactly supported continuous H(x, z), translate, and test with zeta(. + z)

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
