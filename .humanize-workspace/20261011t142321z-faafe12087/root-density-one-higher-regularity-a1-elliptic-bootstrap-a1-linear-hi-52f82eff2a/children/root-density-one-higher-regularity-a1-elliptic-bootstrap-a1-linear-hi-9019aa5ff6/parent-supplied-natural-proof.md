# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.dq_uniform_bounds-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.dq_uniform_bounds-a1.wd_props-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2, 3, 4, 6, 7 and 8 of the parent proof (the bound on w_d, its C^1 regularity, the derivative formula and the Hölder derivative). Notation: K0 := closedBall(xb, 4R), B := ball(xb, 2R), Dv = fderiv ℝ v, w_d(z) := d⁻¹ • (v(z + d e) − v(z)). The sibling lemmas are dohr_eb_lhr_dqub_fderiv_consts (A) and dohr_eb_lhr_dqub_dq_mean_value (B).
1. Unpacking the hypothesis. IsLocallyHolderCkα 1 α v U has two parts. The first is ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞) v U, which is ContDiffOn ℝ 1 v U by Nat.cast_one. The second gives, for every compact K ⊆ U, a constant C with ‖iteratedFDeriv ℝ 1 v x − iteratedFDeriv ℝ 1 v y‖ ≤ C ‖x − y‖^α on K. K0 is compact (isCompact_closedBall; ℝ^n is proper) and K0 ⊆ U.
2. Constants. Apply A with E = Rn n, F = Rn ℓ, K = K0, g = v and the hypotheses from step 1. This gives S_v ≥ 0 and H_v ≥ 0 with ‖Dv(z)‖ ≤ S_v and ‖Dv(z) − Dv(w)‖ ≤ H_v ‖z − w‖^α for all z, w ∈ K0. Take S := S_v; it does not depend on d. Now fix d ≠ 0 with |d| < R.
3. Geometry. Let z ∈ B and |s| ≤ |d|. Then ‖z + s e − xb‖ ≤ ‖z − xb‖ + |s| ‖e‖ < 2R + R = 3R ≤ 4R, using ‖z − xb‖ < 2R, |s| ‖e‖ ≤ |d| < R and R > 0. So z + s e ∈ K0 ⊆ U. In particular z ∈ K0 (s = 0) and z + d e ∈ K0 (s = d) for every z ∈ B.
4. Claim (i). v is differentiable on U (ContDiffOn.differentiableOn, 1 ≠ 0). Apply B with E = Rn n, F = Rn ℓ, g = v, S = S_v, H = H_v, the bounds of step 2 and the fixed d (d ≠ 0, |d| < R). Part (a) at x ∈ B gives ‖d⁻¹ • (v(x + d e) − v(x))‖ ≤ S_v = S.
5. Claim (ii). The translation τ(z) := z + d e is C^∞ (contDiff_id.add contDiff_const) and maps B into U (step 3). So z ↦ v(z + d e) = v ∘ τ is C^1 on B (ContDiffOn.comp applied to ContDiffOn ℝ 1 v U, τ and the MapsTo fact). Also v is C^1 on B, because B ⊆ K0 ⊆ U (ContDiffOn.mono). Therefore w_d = d⁻¹ • ((v ∘ τ) − v) is C^1 on B (ContDiffOn.sub, ContDiffOn.const_smul).
6. Claim (iii). Let x ∈ B. By step 3, x and x + d e lie in the open set U. So v is differentiable at both points (DifferentiableWithinAt.differentiableAt with IsOpen.mem_nhds), with derivatives Dv(x) and Dv(x + d e). The translation has derivative the identity at x ((hasFDerivAt_id x).add_const (d • e)). By the chain rule (HasFDerivAt.comp), z ↦ v(z + d e) has derivative Dv(x + d e) at x. By HasFDerivAt.sub and HasFDerivAt.const_smul, w_d has derivative d⁻¹ • (Dv(x + d e) − Dv(x)) at x. Hence fderiv ℝ w_d x = d⁻¹ • (Dv(x + d e) − Dv(x)) (HasFDerivAt.fderiv).
7. Claim (iv). Take K := 2 H_v |d|⁻¹. Let x, y ∈ B. By step 6, Dw_d(x) − Dw_d(y) = d⁻¹ • ((Dv(x + d e) − Dv(x)) − (Dv(y + d e) − Dv(y))), by smul_sub. Also (Dv(x + d e) − Dv(x)) − (Dv(y + d e) − Dv(y)) = (Dv(x + d e) − Dv(y + d e)) − (Dv(x) − Dv(y)). The four points x, y, x + d e and y + d e lie in K0 (step 3), and (x + d e) − (y + d e) = x − y. So by step 2 and the triangle inequality, ‖Dw_d(x) − Dw_d(y)‖ ≤ |d|⁻¹ (H_v ‖x − y‖^α + H_v ‖x − y‖^α) = K ‖x − y‖^α.
8. Steps 4–7 establish (i)–(iv) for every d ≠ 0 with |d| < R, with the d-independent constant S of step 2. QED
Lean notes: step 1 is `simpa using hv.1`. In step 6, the chain rule result is `simpa [Function.comp_def] using hA1.hasFDerivAt.comp x ((hasFDerivAt_id x).add_const (d • e))`; plain `simpa` leaves `v ∘ _`. In step 7, state the smul_sub equation as the term `(smul_sub _ _ _).symm`, because `rw [← smul_sub]` failed to match the CLM-valued expression at the pin.

## Key steps

1. unpack IsLocallyHolderCkα 1: v is C^1 on U and D^1 v is α-Hölder on the compact K0 = closedBall(xb, 4R)
2. sibling fderiv_consts on K0 gives S_v and H_v; set S := S_v
3. geometry: z ∈ K0 and z + d e ∈ K0 for z ∈ ball(xb, 2R)
4. (i) follows from part (a) of sibling dq_mean_value with g = v
5. (ii) ContDiffOn.comp with the translation, then sub and const_smul
6. (iii) HasFDerivAt chain rule with the translation, sub, const_smul and .fderiv
7. (iv) K := 2H_v|d|⁻¹ from (iii) and the Hölder bound of Dv on K0

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Contract.lean; cmp GMT/Ch05/Contract.lean GMT/Ch05/Submission.lean`
- `python3 scan of the run's dag.json: statuses and lean_statements of the sibling nodes under linear_higher_regularity-a1 and of the accepted dohr_eb_holder_* / dohr_eb_hsif_* declarations; check whether any of the five proposed child types is identical to an existing node type`
- `rg 'dqub|dohr_eb_lhr_dqub' over <snapshot>, the run directory and the other workspaces; git grep -l dqub over all 2452 refs/heads and refs/remotes; git grep -ho 'dohr_eb_lhr_[A-Za-z0-9_]*' over all refs`
- `rg -n in <snapshot>/mathlib/Mathlib for: iteratedFDeriv_one_apply, norm_iteratedFDeriv_one, continuousMultilinearCurryFin1_symm_apply, 'structure IsLinearMap', 'def mk'' (IsLinearMap.mk'), norm_image_sub_le_of_norm_fderiv_le, norm_image_sub_le_of_norm_hasDerivWithin_le, norm_image_sub_le_of_norm_deriv_le, ContDiffOn.continuousOn_fderiv_of_isOpen, ContDiffOn.differentiableOn, 'def finBasis', 'theorem Basis.sum_repr', 'def toContinuousLinearMap', coe_toContinuousLinearMap', fderiv_comp_add_right, hasFDerivAt_comp_add_right, fderiv_fun_const_smul, HasFDerivAt.comp_hasDerivAt, le_opNorm, rpow_nonneg, convex_closedBall, convex_uIcc, left_mem_uIcc, right_mem_uIcc, exists_bound_of_continuousOn, abs_sum_le_sum_abs, inv_mul_le_iff₀`
- `python3 using verifier/gmt-compare.py contract_scope + child_modules (contract mode) to generate NodeChallenge/NodeSolution files; lake build GMT.Ch05.Submission in scratch copy /tmp/dqub-decomp-dMSAWZ/proj; lake env lean Checks/v1/Challenge_*.lean (five child types)`
- `lake env lean Checks/Assembly2.lean (parent frozen type proved from the wd_props and forcing_holder types posed as axioms; #print axioms)`
- `lake env lean Checks/Base.lean, Checks/W.lean, Checks/V.lean, Checks/V2.lean (complete proofs of all five children, V2 with the non-deprecated add_apply/smul_apply/sub_apply)`
- `lake build GMT.Ch05.Submission with all child and parent proofs inserted into a scratch Submission.lean; lake env lean Checks/sol/Solution_*.lean (exact Submission.X for the five children and the parent; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Module/Multilinear/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Algebra/Module/LinearMap/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/Dimension/Free.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/Basis/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Module/Convex.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Convex/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Order/Interval/Finset/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`

The snapshot pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace Contract.lean is byte-identical to the snapshot Contract, and Submission.lean is still identical to it.

No 'dqub' or dohr_eb_lhr_dqub_* name occurs in the snapshot, the run directory, the other workspaces or any of the 2452 git refs, so the five names are fresh. None of the five child types is identical to an existing DAG node type, so no accepted declaration is reused. Children need no DAG node outside this decomposition.

Every Mathlib lemma cited in the child proofs exists at the pin:
- iteratedFDeriv_one_apply (ContDiff/FTaylorSeries.lean:938)
- continuousMultilinearCurryFin1_symm_apply (Normed/Module/Multilinear/Curry.lean:522)
- IsLinearMap (Algebra/Module/LinearMap/Defs.lean:69) and IsLinearMap.mk' (:648)
- Convex.norm_image_sub_le_of_norm_fderiv_le (Calculus/MeanValue.lean:499)
- Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (MeanValue.lean:694)
- ContDiffOn.differentiableOn (ContDiff/Defs.lean:578)
- ContDiffOn.continuousOn_fderiv_of_isOpen (Defs.lean:916)
- Module.finBasis (Dimension/Free.lean:334)
- Module.Basis.sum_repr (Basis/Defs.lean:258)
- LinearMap.toContinuousLinearMap (Topology/Algebra/Module/FiniteDimension.lean:307)
- hasFDerivAt_comp_add_right and fderiv_comp_add_right (FDeriv/Add.lean:847, :855)
- HasFDerivAt.comp_hasDerivAt (Deriv/Comp.lean:374)
- le_opNorm (Normed/Operator/Basic.lean:234)
- Real.rpow_nonneg (Pow/Real.lean:163)
- convex_closedBall (Normed/Module/Convex.lean:70)
- convex_uIcc (Convex/Basic.lean:307)
- IsCompact.exists_bound_of_continuousOn (to_additive, Normed/Group/Bounded.lean:91)
- Finset.abs_sum_le_sum_abs (BigOperators/Group/Finset.lean:371)
- inv_mul_le_iff₀ (GroupWithZero/Basic.lean:885)
ContinuousLinearMap.add_apply, sub_apply and smul_apply are deprecated aliases of the root add_apply, sub_apply and smul_apply.

Lean checks on the scratch build (Lean 4.35.0-rc3):
- All five child types elaborate in the comparator's replayed Contract scope.
- The frozen parent type follows from the wd_props and forcing_holder types alone. #print axioms shows propext, Classical.choice, Quot.sound and those two.
- Complete sorry-free proofs of all five children and of the parent compile.
- The comparator-style NodeSolution files (`exact Submission.X`) for each child and for the parent compile using only propext, Classical.choice and Quot.sound.
