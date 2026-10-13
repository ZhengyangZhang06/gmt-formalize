# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.interpolation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step (1b) of the parent proof, with the details filled in.
1. Since x is in B_rho(x), S >= |w(x)| >= 0. Put B := 2S/t + t^alpha K; then B >= 0 because S >= 0, K >= 0 and t > 0.
2. Fix a unit vector e. For s in [0, t], the point x + s e lies in the closed ball of radius t around x, which is contained in B_rho(x) because t < rho. Since w is C^1 on the open set B_rho(x), w is differentiable at every point of this closed ball. Define h(y) := w(y) - Dw(x)(y - x). Then h has derivative Dw(y) - Dw(x) at every y in B_rho(x).
3. Derivative bound. For y in closedBall(x, t): ||Dw(y) - Dw(x)|| <= K |y - x|^alpha <= K t^alpha. Here we use alpha >= 0 (so r -> r^alpha is monotone on [0, infinity)) and K >= 0.
4. Mean value inequality on the convex set closedBall(x, t), between x and x + t e: |h(x + t e) - h(x)| <= K t^alpha |t e| = K t^{1+alpha}. Since h(x + t e) - h(x) = w(x + t e) - w(x) - t Dw(x)e, this is the parent's identity w(x + te) - w(x) = t Dw(x)e + integral_0^t (Dw(x + se) - Dw(x))e ds, written as an inequality.
5. Consequently t |Dw(x)e| <= |w(x + t e) - w(x)| + |w(x + t e) - w(x) - t Dw(x)e| <= 2S + K t^{1+alpha}. Dividing by t > 0 gives |Dw(x)e| <= 2S/t + t^alpha K = B.
6. Operator norm. Let v be in R^n. If v = 0, then |Dw(x)v| = 0 <= B|v|. Otherwise apply step 5 to e := v/|v| and multiply by |v| to get |Dw(x)v| <= B|v|. Since B >= 0, the operator norm satisfies ||Dw(x)|| <= B. If n = 0, then Dw(x) = 0 and the bound holds since B >= 0.
Lean proof checked at the pin (Lean 4.35.0-rc3, Mathlib 25730c7c; stated inside `namespace GMT.Ch05` with the contract's `open`s; #print axioms: propext, Classical.choice, Quot.sound):
set_option maxSynthPendingDepth 3 in
theorem Submission.dohr_eb_sch_fderiv_norm_interpolation : ∀ (n ℓ : ℕ) (w : Rn n → Rn ℓ) (x : Rn n) (ρ t α S K : ℝ), 0 ≤ α → 0 ≤ K → 0 < t → t < ρ → ContDiffOn ℝ 1 w (ball x ρ) → (∀ y ∈ ball x ρ, ‖w y‖ ≤ S) → (∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ, ‖fderiv ℝ w y - fderiv ℝ w z‖ ≤ K * ‖y - z‖ ^ α) → ‖fderiv ℝ w x‖ ≤ 2 * S / t + t ^ α * K := by
  intro n ℓ w x ρ t α S K hα hK ht htρ hw hS hH
  have hxB : x ∈ ball x ρ := mem_ball_self (ht.trans htρ)
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS x hxB)
  have hsub : closedBall x t ⊆ ball x ρ := closedBall_subset_ball htρ
  have hdiff : ∀ y ∈ ball x ρ, HasFDerivAt w (fderiv ℝ w y) y := fun y hy =>
    (((hw.differentiableOn one_ne_zero) y hy).differentiableAt (isOpen_ball.mem_nhds hy)).hasFDerivAt
  set h : Rn n → Rn ℓ := fun y => w y - fderiv ℝ w x (y - x) with hdef
  have hh : ∀ y ∈ closedBall x t,
      HasFDerivWithinAt h (fderiv ℝ w y - fderiv ℝ w x) (closedBall x t) y := by
    intro y hy
    have h2 : HasFDerivAt (fun y => fderiv ℝ w x (y - x)) (fderiv ℝ w x) y := by
      have := (fderiv ℝ w x).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const x)
      rw [ContinuousLinearMap.comp_id] at this
      exact this
    exact ((hdiff y (hsub hy)).sub h2).hasFDerivWithinAt
  have hbound : ∀ y ∈ closedBall x t, ‖fderiv ℝ w y - fderiv ℝ w x‖ ≤ K * t ^ α := by
    intro y hy
    calc ‖fderiv ℝ w y - fderiv ℝ w x‖ ≤ K * ‖y - x‖ ^ α := hH y (hsub hy) x hxB
      _ ≤ K * t ^ α := by
        gcongr
        exact mem_closedBall_iff_norm.mp hy
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro e
  rcases eq_or_ne e 0 with rfl | he
  · simp
  set u := ‖e‖⁻¹ • e with hudef
  have hu : ‖u‖ = 1 := norm_smul_inv_norm he
  have hxu : x + t • u ∈ closedBall x t := by
    rw [mem_closedBall_iff_norm, add_sub_cancel_left, norm_smul, hu, Real.norm_eq_abs,
      abs_of_pos ht, mul_one]
  have mvt := (convex_closedBall x t).norm_image_sub_le_of_norm_hasFDerivWithin_le hh hbound
    (mem_closedBall_self ht.le) hxu
  have hmv : ‖w (x + t • u) - t • fderiv ℝ w x u - w x‖ ≤ K * t ^ α * t := by
    have e1 : h (x + t • u) - h x = w (x + t • u) - t • fderiv ℝ w x u - w x := by
      simp only [hdef, add_sub_cancel_left, sub_self, map_zero, sub_zero, map_smul]
    have e2 : ‖x + t • u - x‖ = t := by
      rw [add_sub_cancel_left, norm_smul, hu, Real.norm_eq_abs, abs_of_pos ht, mul_one]
    rw [e1, e2] at mvt
    exact mvt
  have h1 : ‖w (x + t • u)‖ ≤ S := hS _ (hsub hxu)
  have h2 : ‖w x‖ ≤ S := hS x hxB
  have key : t * ‖fderiv ℝ w x u‖ ≤ 2 * S + K * t ^ α * t := by
    have hdec : ‖t • fderiv ℝ w x u‖
        ≤ ‖w (x + t • u) - w x‖ + ‖w (x + t • u) - t • fderiv ℝ w x u - w x‖ := by
      have := norm_sub_le (w (x + t • u) - w x) (w (x + t • u) - t • fderiv ℝ w x u - w x)
      have e : (w (x + t • u) - w x) - (w (x + t • u) - t • fderiv ℝ w x u - w x)
          = t • fderiv ℝ w x u := by abel
      rw [e] at this
      exact this
    calc t * ‖fderiv ℝ w x u‖ = ‖t • fderiv ℝ w x u‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      _ ≤ ‖w (x + t • u) - w x‖ + ‖w (x + t • u) - t • fderiv ℝ w x u - w x‖ := hdec
      _ ≤ (‖w (x + t • u)‖ + ‖w x‖) + K * t ^ α * t := by
          gcongr; exact norm_sub_le _ _
      _ ≤ 2 * S + K * t ^ α * t := by linarith
  have hfu : ‖fderiv ℝ w x u‖ ≤ 2 * S / t + t ^ α * K := by
    have : ‖fderiv ℝ w x u‖ ≤ (2 * S + K * t ^ α * t) / t := by
      rw [le_div_iff₀ ht]; linarith
    calc ‖fderiv ℝ w x u‖ ≤ (2 * S + K * t ^ α * t) / t := this
      _ = 2 * S / t + t ^ α * K := by field_simp
  have hu' : fderiv ℝ w x e = ‖e‖ • fderiv ℝ w x u := by
    rw [hudef, map_smul, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr he), one_smul]
  rw [hu', norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), mul_comm]
  exact mul_le_mul_of_nonneg_right hfu (norm_nonneg _)

## Key steps

1. S >= 0 and B := 2S/t + t^alpha K >= 0
2. h(y) := w(y) - Dw(x)(y - x) has derivative Dw(y) - Dw(x), bounded by K t^alpha on closedBall(x, t)
3. mean value inequality: |w(x+te) - w(x) - t Dw(x)e| <= K t^{1+alpha}
4. t|Dw(x)e| <= 2S + K t^{1+alpha} for unit e
5. homogeneity and the operator-norm bound give ||Dw(x)|| <= B

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Submission.lean`
- `rg -l -i 'caccioppoli|schauder|campanato|liouville' <snapshot>/mathlib/Mathlib <snapshot>/project`
- `grep -n 'theorem|lemma' <snapshot>/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `grep (pinned Mathlib) for integral_comp_smul, integral_mul_left_eq_self (to_additive integral_add_left_eq_self), setIntegral_eq_integral_of_forall_compl_eq_zero, ContinuousLinearMap.integral_comp_comm, Real.smoothTransition, HasCompactSupport.contDiff_convolution_left, hasFDerivAt_integral_of_dominated_of_fderiv_le, ContDiffAt.isSymmSndFDerivAt, ContDiffBump.integral_normed, BoundedContinuousFunction.arzela_ascoli, hasFDerivAt_of_tendstoUniformlyOn, Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`
- `python3 scan of dag.json: lean_name collisions for the 7 proposed dohr_eb_sch_* names; topic scan of node titles/statements for Caccioppoli, Liouville, mollifier, blow-up, interpolation, Schauder, Campanato`
- `python3 gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch05.main_theorem') to obtain the replayed child scope`
- `lake build GMT.Ch05.Submission in scratch /tmp/sch-decomp-vQxbTq/proj (Lean 4.35.0-rc3, shared lake-packages-25730c7c)`
- `lake env lean Checks/AllChallenges.lean (7 child types + frozen parent type, each as `theorem _root_.HumanizeNodeComparator.target_k : (T) := by sorry` in the replayed scope)`
- `lake env lean Checks/Sol_<key>.lean for all 7 keys (generated NodeSolution targets closed by `exact Submission.X`, children declared in a scratch Submission copy)`
- `lake env lean Checks/Assembly.lean (frozen parent type proved from the rescale and unit_ball_estimate types as hypotheses; #print axioms)`
- `lake env lean Checks/ZeroMean.lean, Checks/Interp.lean, Checks/TwoProofs.lean (zero_mean and interpolation proved outright)`
- `lake env lean Checks/InstVerify.lean, Checks/SmulTest.lean (inferred instances of inline constructions; smul_sub needs maxSynthPendingDepth 3 on L(R^n,R^l))`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/ContinuousMap/Bounded/ArzelaAscoli.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/UniformLimitsDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Complex/Harmonic/Liouville.lean`

Snapshot pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace Submission.lean is byte-identical to the snapshot Contract.lean. No elliptic regularity theory is available at the pin. The keyword search finds no Caccioppoli or Campanato matches. 'Schauder' matches only Schauder-basis files (Analysis/InnerProductSpace/l2Space.lean, Analysis/Normed/Module/Bases.lean) and the chapter README remark that 7.1(ii) cites Schauder theory. 'Liouville' matches number theory, differential fields, operator algebras and the complex-plane theorems (Analysis/Complex/Liouville.lean; Analysis/Complex/Harmonic/Liouville.lean, bounded harmonic functions on C are constant). None covers Legendre-elliptic systems on R^n with |x|^alpha gradient growth, so the Caccioppoli, Liouville, blow-up and absorption steps must be proved, as in the children. Usable pinned tools, one per child: zero_mean uses integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (IntegrationByParts.lean:212; needs an extra import). rescale uses MeasureTheory.Measure.integral_comp_smul (Haar/NormedSpace.lean:92, valid without integrability), integral_add_left_eq_self (to_additive of Group/Integral.lean:91) and setIntegral_eq_integral_of_forall_compl_eq_zero (Bochner/Set.lean:486). caccioppoli uses Real.smoothTransition (SmoothTransition.lean:146). liouville uses HasCompactSupport.contDiff_convolution_left (ContDiff/Convolution.lean:427), hasFDerivAt_integral_of_dominated_of_fderiv_le (ParametricIntegral.lean:208), ContDiffAt.isSymmSndFDerivAt (FDeriv/Symmetric.lean:533) and ContDiffBump.integral_normed (BumpFunction/Normed.lean:68). blowup_estimate uses BoundedContinuousFunction.arzela_ascoli (ArzelaAscoli.lean:109) and hasFDerivAt_of_tendstoUniformlyOn (UniformLimitsDeriv.lean:419). interpolation uses Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (MeanValue.lean:422). No proposed lean_name occurs in dag.json. No DAG node carries an identical frozen type for any child; the accepted mollifier and Campanato nodes have different types. Lean checks on a scratch build: (1) All 7 child types and the frozen parent type elaborate in the comparator's replayed scope, and every generated NodeSolution target closes by `exact Submission.X`. (2) With the rescale and unit_ball_estimate types as hypotheses, the frozen parent type is proved without sorry (#print axioms: propext, Classical.choice, Quot.sound). (3) zero_mean and interpolation were proved outright; their Lean proofs are included in those children. (4) Instance checks: ‖T‖ₑ = ofReal ‖T‖ on L(R^n,R^l) and R^l; (ρ • Φ z) P = ρ * Φ z P; (ρ • T) h = ρ • T h; volume on Rn n is an additive Haar measure. Rewrites such as smul_sub on L(R^n,R^l) need `set_option maxSynthPendingDepth 3`.
