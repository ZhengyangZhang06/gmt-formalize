# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.jacobian_continuity-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.jacobian_continuity-a1.mollify_fderiv-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 6(i): 'for each Lipschitz h, ... D(h∗ϕ_δ) = (Dh)∗ϕ_δ (the a.e. derivative of a Lipschitz function is its weak derivative, Mathlib LipschitzWith.integral_lineDeriv_mul_eq)', for one L-Lipschitz function f and an arbitrary C¹ compactly supported kernel ρ. (The frozen type is identical to that of node dor_lmb_fcd_jwc_mollify_fderiv_eq of another branch. That node was accepted (candidate ebbe3de7) only at 2026-10-14T01:41Z, after this decomposition attempt's DAG refresh, so a fresh name is used. The Lean realization below is that accepted proof with the declaration renamed.)

Notation: λ = Lebesgue measure (volume) on ℝᵏ = Euclid k; D = fderiv ℝ; ∂_w F(s) := lineDeriv ℝ F s w, the derivative of t ↦ F(s + t·w) at t = 0 (0 if it does not exist); f_ρ(y) := ∫ ρ(t)·f(y − t) dt.

1. (Convolution.) f_ρ is the convolution ρ ⋆ f with the multiplication pairing, i.e. f_ρ = convolution ρ f (lsmul ℝ ℝ) λ (convolution_def: (ρ ⋆ f)(y) = ∫ ρ(t)·f(y − t) dt).

2. (Differentiation under the integral.) ρ is C¹ with compact support and f is continuous (being Lipschitz), hence locally integrable. Therefore ρ ⋆ f has at every x the derivative (Dρ ⋆ f)(x) = ∫ f(x − t)·Dρ(t) dt, a Bochner integral of continuous linear maps (HasCompactSupport.hasFDerivAt_convolution_left). This integrand is integrable: Dρ is continuous (ρ is C¹) with compact support and f is locally integrable (HasCompactSupport.convolutionExists_left). Evaluation at v is continuous linear and commutes with the Bochner integral (ContinuousLinearMap.integral_apply), so Df_ρ(x)v = ∫ Dρ(t)v·f(x − t) dt.

3. (Change of variables.) λ is invariant under s ↦ x − s (integral_sub_left_eq_self), so ∫ Dρ(t)v·f(x − t) dt = ∫ Dρ(x − s)v·f(s) ds and ∫ ρ(t)·Df(x − t)v dt = ∫ ρ(x − s)·Df(s)v ds. It remains to show ∫ Dρ(x − s)v·f(s) ds = ∫ ρ(x − s)·Df(s)v ds.

4. (Reflected kernel.) Let h(s) := ρ(x − s). h is C¹ (ρ composed with an affine map) and has compact support (its support is the image of the support of ρ under the homeomorphism s ↦ x − s; HasCompactSupport.comp_homeomorph). A C¹ function with compact support is Lipschitz (ContDiff.lipschitzWith_of_hasCompactSupport). By the chain rule Dh(s) = −Dρ(x − s), so ∂_{−v}h(s) = Dh(s)(−v) = Dρ(x − s)v for every s (h is differentiable, DifferentiableAt.lineDeriv_eq_fderiv).

5. (Integration by parts for Lipschitz functions.) For the L-Lipschitz f and the Lipschitz, compactly supported h, LipschitzWith.integral_lineDeriv_mul_eq gives ∫ ∂_v f(s)·h(s) ds = ∫ ∂_{−v}h(s)·f(s) ds. By step 4 the right side equals ∫ Dρ(x − s)v·f(s) ds.

6. (Rademacher.) f is differentiable at λ-a.e. s (LipschitzWith.ae_differentiableAt), and at such s, ∂_v f(s) = Df(s)v (DifferentiableAt.lineDeriv_eq_fderiv). Hence ∫ ∂_v f(s)·h(s) ds = ∫ ρ(x − s)·Df(s)v ds (integral_congr_ae).

7. (Conclusion.) Steps 5 and 6 give ∫ Dρ(x − s)v·f(s) ds = ∫ ρ(x − s)·Df(s)v ds, which by steps 2 and 3 is the claim Df_ρ(x)v = ∫ ρ(t)·Df(x − t)v dt.

Lean realization (compiled during this decomposition with the pinned toolchain against GMT.Ch07.Submission at b4d606db, Mathlib 25730c7c, in the Submission layout: inside namespace GMT.Ch07 after the contract's open commands, together with the proofs of the sibling declarations it uses; no extra import, no sorry; #print axioms: propext, Classical.choice, Quot.sound):
```lean
/-- **Derivative of the mollification of a Lipschitz function**: for an `L`-Lipschitz `f` and a
`C¹` kernel `ρ` with compact support, `D(ρ ⋆ f)(x) v = ∫ ρ(t) Df(x − t) v dt`.  Differentiating
under the integral (`HasCompactSupport.hasFDerivAt_convolution_left`) gives
`D(ρ ⋆ f)(x) v = ∫ Dρ(t) v · f(x − t) dt`.  With `t = x − s` and the reflected kernel
`h(s) = ρ(x − s)` (`C¹` with compact support, hence Lipschitz, and `∂_{−v} h(s) = Dρ(x − s) v`)
the two sides become `∫ ∂_{−v} h · f` and `∫ h · Df(·) v`; they agree by integration by parts for
Lipschitz functions (`LipschitzWith.integral_lineDeriv_mul_eq`: `∫ ∂_v f · h = ∫ ∂_{−v} h · f`)
and Rademacher (`∂_v f = Df · v` a.e.). -/
theorem Submission.dimred_mbl_dt_lp_jc_mollify_fderiv_eq : ∀ (k : ℕ) (L : NNReal) (f ρ : Euclid k → ℝ), LipschitzWith L f → ContDiff ℝ 1 ρ → HasCompactSupport ρ → ∀ x v : Euclid k, fderiv ℝ (fun y => ∫ t, ρ t * f (y - t)) x v = ∫ t, ρ t * fderiv ℝ f (x - t) v := by
  intro k L f ρ hf hρ hρs x v
  have hconv : (fun y => ∫ t, ρ t * f (y - t)) =
      convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext y; simp [convolution_def]
  have hD := hρs.hasFDerivAt_convolution_left (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ) hρ
    hf.continuous.locallyIntegrable x
  have hint := (hρs.fderiv (𝕜 := ℝ)).convolutionExists_left (μ := (volume : Measure (Euclid k)))
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Euclid k)) (hρ.continuous_fderiv (by norm_num))
    (hf.continuous.locallyIntegrable (μ := (volume : Measure (Euclid k)))) x
  rw [hconv, hD.fderiv, convolution_def, ContinuousLinearMap.integral_apply hint]
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  -- change of variables `t ↦ x - t` on both sides
  rw [← integral_sub_left_eq_self (fun t => fderiv ℝ ρ t v * f (x - t)) (μ := volume) x,
    ← integral_sub_left_eq_self (fun t => ρ t * fderiv ℝ f (x - t) v) (μ := volume) x]
  simp only [sub_sub_cancel]
  -- integration by parts against `h(s) = ρ(x - s)`
  set h : Euclid k → ℝ := fun s => ρ (x - s) with hh
  have hhC1 : ContDiff ℝ 1 h := hρ.comp (contDiff_const.sub contDiff_id)
  have hhs : HasCompactSupport h := hρs.comp_homeomorph (Homeomorph.subLeft x)
  obtain ⟨D, hhL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hhs hhC1 (by norm_num)
  have hibp := hf.integral_lineDeriv_mul_eq (μ := volume) hhL hhs v
  have hlh : ∀ s, lineDeriv ℝ h s (-v) = fderiv ℝ ρ (x - s) v := by
    intro s
    rw [(hhC1.differentiable (by norm_num) s).lineDeriv_eq_fderiv]
    have h1 : HasFDerivAt h (-(fderiv ℝ ρ (x - s))) s := by
      have := (hρ.differentiable (by norm_num) (x - s)).hasFDerivAt.comp s
        ((hasFDerivAt_const x s).sub (hasFDerivAt_id s))
      simpa [hh, Function.comp_def] using this
    rw [h1.fderiv]
    simp
  -- Rademacher: `∂_v f = Df · v` almost everywhere
  have hlf : ∀ᵐ s ∂(volume : Measure (Euclid k)), lineDeriv ℝ f s v = fderiv ℝ f s v := by
    filter_upwards [hf.ae_differentiableAt] with s hs
    exact hs.lineDeriv_eq_fderiv
  simp only [hlh] at hibp
  rw [← hibp]
  refine integral_congr_ae ?_
  filter_upwards [hlf] with s hs
  rw [hs, hh]
  ring
```

## Key steps

1. f_ρ = ρ ⋆ f; differentiating under the integral (HasCompactSupport.hasFDerivAt_convolution_left) gives Df_ρ(x)v = ∫ Dρ(t)v·f(x − t) dt.
2. Change variables s = x − t on both sides.
3. The reflected kernel h(s) = ρ(x − s) is C¹, compactly supported, Lipschitz, with ∂_{−v}h(s) = Dρ(x − s)v.
4. Integration by parts for Lipschitz functions (LipschitzWith.integral_lineDeriv_mul_eq) and Rademacher (∂_v f = Df·v a.e.) identify the two sides.

## Reference use

### local-project

Queries:
- `cat SNAPSHOT/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git -C SNAPSHOT/mathlib rev-parse HEAD (25730c7c); cmp SNAPSHOT/project/GMT/Ch07/Contract.lean workspace GMT/Ch07/Submission.lean (identical); git log -1 of the workspace (b4d606db)`
- `rg -n -i 'piola|mollif|weak.?contin|null.?lagrang|minor' SNAPSHOT/project -g '*.lean' (no relevant match: only LpSeminorm imports and a Hölder-seminorm comment in Ch04/Ch05); rg -n -i jacobian SNAPSHOT/project/GMT/Ch02/Contract.lean SNAPSHOT/project/GMT/Ch03/Contract.lean SNAPSHOT/project/GMT/Ch07/Contract.lean (only the areaJacobian/coareaJacobian definitions of Ch02/Ch03 and the area/coarea formulas; nothing in Ch07)`
- `rg -l 'dimred_mbl_dt_lp_jc|dor_lmb_fcd_jwc|cmcs_ls_mollify|cmr_cc_det' SNAPSHOT/project (no match; these declarations exist only in DAG candidate commits)`
- `rg -n '^(theorem|lemma) [A-Za-z_.]*NAME' SNAPSHOT/mathlib/Mathlib for NAME in integral_lineDeriv_mul_eq, norm_fderiv_le_of_lipschitz, measurable_fderiv_apply_const, contDiff_convolution_left, hasFDerivAt_convolution_left, convolutionExists_left, ae_tendsto_average_norm_sub, tendsto_integral_smul_of_tendsto_average_norm_sub, dist_convolution_le, extDeriv_pullback, extDeriv_apply, det_succ_row_zero, tendsto_integral_filter_of_dominated_convergence, ae_differentiableAt, induction_dense, exists_contDiff_support_eq_eq_one_iff, lipschitzWith_of_hasCompactSupport, exists_isCompact_sdiff_lt, exists_isOpen_sdiff_lt, bdd_mul, addHaar_real_closedBall' (all found); ae_convolution_tendsto_right_of_locallyIntegrable and det_le (found in the snapshot, see next query)`
- `lake env lean /tmp/jc-decomp2/probe/Probe.lean importing only GMT.Ch07.Submission: #check ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable and Matrix.det_le (Unknown constant: outside the frozen import closure); #check IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub, tendsto_integral_smul_of_tendsto_average_norm_sub, LipschitzWith.integral_lineDeriv_mul_eq, MemLp.induction_dense, HasCompactSupport.hasFDerivAt_convolution_left, extDeriv_pullback (available)`
- `python3 scans of RUN/dag.json: nodes whose id/title/statement mention Jacobian weak continuity; status, candidate_commit, updated_at and lean_statement of the eleven child names under the runtime rule _accepted_checkpoint (six reused names accepted with byte-identical types; twin mollify_fderiv accepted at 01:41:31Z, the four other twins comparing/speculative-ready); collision scan for dimred_mbl_dt_lp_jc_* (unused); RUN/issue-workers.json (mode broker-owned-issue-polling; worker for issue 7020 started 2026-10-14T00:19:09Z)`
- `grep/sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_decompose depth guard and name checks, _existing_lean_name_problem, _accepted_checkpoint, _solve_children reuse by lean_name), store.py (refresh, update: accepted is permanent), parallel.py (enabled, RefreshLock), scripts/swarm-run-issue.py, and workspace .humanize/swarm-configs/c8e45649089f4d62adf9de1e95c664c3.json (github_shared_issue_runtime true, max_depth 6, max_children 12, max_nodes 5000, decomposition_attempts 5)`
- `git show <commit>:GMT/Ch07/Submission.lean for accepted candidates fee01ff86c, 2c87728a, 7ba02a03, c6153c4c, 52b9c39c, 13966862 (reused proofs byte-identical to the compiled chain) and ebbe3de7 (accepted twin of mollify_fderiv; proof body identical to the embedded realization)`
- `lake env lean /tmp/jc-decomp2/lean/FinalCheck.lean (eleven child proofs, assembly_from_children, Submission.dimred_mbl_dt_lp_jacobian_weak_continuity with its frozen type, exact-type checks; exit 0, no sorry, axioms propext/Classical.choice/Quot.sound); lake env lean /tmp/jc-decomp2/challenges/AllChallenges.lean (prefix from verifier contract_scope; exit 0, only sorry warnings); both validate_lean_statement implementations on all eleven types; dependency cross-check of Submission.* references against depends_on`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Average.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/SimpleFuncDenseLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/AbsoluteValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-b372f37aac/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-b372f37aac/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/c8e45649089f4d62adf9de1e95c664c3.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/parallel.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/scripts/swarm-run-issue.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/jc-decomp2/lean/FinalCheck.lean`
- `/tmp/jc-decomp2/challenges/AllChallenges.lean`
- `/tmp/jc-decomp2/probe/Probe.lean`

Pins match: project b4d606db and Mathlib 25730c7c, and the workspace Submission is byte-identical to the frozen Ch07 contract. The snapshot project contains no weak-continuity, Piola, mollification or minor-expansion lemma. Its only Jacobians are the Ch02/Ch03 area/coarea Jacobian definitions, so the needed obligations come from the DAG. Six comparator-accepted DAG declarations with exactly the needed types are reused verbatim: cmr_cc_det_covector_exists, dor_lmb_fcd_jwc_covector_det_expansion, dor_lmb_fcd_jwc_weak_star_l1_upgrade, dor_lmb_fcd_jwc_piola_identity, cmcs_ls_mollify_lipschitz and dor_lmb_fcd_jwc_minor_measurable_bound. All six were accepted before this attempt's shared-DAG refresh (01:30:20Z), so the earlier 'reserved by active DAG node' rejection no longer applies. The five remaining links get fresh, unused dimred_mbl_dt_lp_jc_* names, because their twins were unaccepted at that refresh. Every Mathlib lemma cited by the child proofs exists in the snapshot and is available after import GMT.Ch07.Submission. ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable and Matrix.det_le exist in the snapshot but are outside the import closure, so the child proofs use in-closure substitutes. All eleven child proofs plus the parent, stated with its exact frozen type, compile together with no sorry and only the standard axioms. Every type elaborates in the comparator's challenge scope.
