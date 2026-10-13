# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.zero_mean-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step (1a) of the parent proof, with the details filled in. Lebesgue measure on R^n is the (additive Haar) volume measure of EuclideanSpace R (Fin n).
1. Integrability. Since zeta is C^1, Dzeta : R^n -> L is continuous. If x is not in tsupport zeta, then zeta vanishes on the open neighbourhood R^n \ tsupport zeta of x, so Dzeta(x) = 0. Hence Dzeta is continuous with support in the compact set tsupport zeta, so it is Bochner integrable. Consequently, for every v in R^n, the map x -> Dzeta(x)v (continuous, with support in tsupport zeta) is integrable, and so is x -> c(Dzeta(x)).
2. Pulling c out. A continuous linear map commutes with the Bochner integral of an integrable function. So the integral of c(Dzeta(x)) dx equals c(I), where I := (integral of Dzeta(x) dx) is in L. It suffices to show I = 0.
3. Directional reduction. For v in R^n, evaluation T -> Tv is a continuous linear map L -> R^l, so Iv = (integral of Dzeta(x)v dx). It suffices to show that the integral of Dzeta(x)v dx is 0 for every v, since then I is the zero linear map.
4. Each directional integral vanishes. Fix v. Apply integration by parts for Frechet derivatives on R^n with a Haar measure, scalar-action version (Mathlib: integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable, Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean). Take the constant scalar function f = 1, g = zeta and direction v. This gives: integral of 1 * Dzeta(x)v dx = - integral of (Df(x)v) zeta(x) dx = - integral of 0 = 0. The hypotheses hold. The map x -> (Df(x)v) zeta(x) = 0 is integrable. The map x -> f(x) Dzeta(x)v = Dzeta(x)v is integrable by step 1. The map x -> f(x) zeta(x) = zeta(x) is continuous with compact support, hence integrable. Finally, f and zeta are differentiable everywhere. (Equivalently, as in the parent proof: write Dzeta(x)v = sum_b v_b d_b zeta(x). Each partial derivative d_b zeta^i integrates to 0 by Fubini and the fundamental theorem of calculus on lines parallel to e_b, because t -> zeta^i(x' + t e_b) is C^1 with compact support.)
5. Conclusion. By step 4, Iv = 0 for all v, so I = 0 and the integral of c(Dzeta(x)) dx equals c(0) = 0. If n = 0, then L = {0} and the statement is trivial; the argument above covers this case too.
Lean proof checked at the pin (Lean 4.35.0-rc3, Mathlib 25730c7c, scratch build of GMT.Ch05.Submission). It needs the extra import `Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts` and is stated inside `namespace GMT.Ch05` with the contract's `open`s. #print axioms: propext, Classical.choice, Quot.sound. Because instance synthesis on L(R^n,R^l) needs a higher pending depth for some rewrites, the declaration is preceded by `set_option maxSynthPendingDepth 3 in`:
set_option maxSynthPendingDepth 3 in
theorem Submission.dohr_eb_sch_integral_clm_fderiv_eq_zero : ∀ (n ℓ : ℕ) (c : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (ζ : Rn n → Rn ℓ), ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ x, c (fderiv ℝ ζ x) = 0 := by
  intro n ℓ c ζ hζ hcs
  have hcont : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv one_ne_zero
  have hcsD : HasCompactSupport (fderiv ℝ ζ) := hcs.fderiv (𝕜 := ℝ)
  have hint : Integrable (fderiv ℝ ζ) := hcont.integrable_of_hasCompactSupport hcsD
  rw [ContinuousLinearMap.integral_comp_comm c hint]
  suffices h : ∫ x, fderiv ℝ ζ x = 0 by rw [h, map_zero]
  ext1 v
  rw [ContinuousLinearMap.zero_apply, ← ContinuousLinearMap.apply_apply (v := v),
    ← ContinuousLinearMap.integral_comp_comm _ hint]
  simp only [ContinuousLinearMap.apply_apply]
  have hcsv : HasCompactSupport (fun x => fderiv ℝ ζ x v) := by
    apply hcsD.mono
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h0
    exact hx (by rw [h0]; rfl)
  have key := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := (volume : Measure (Rn n)))
    (f := fun _ : Rn n => (1 : ℝ)) (g := ζ) (v := v)
    (by simp) (by simpa using (hcont.clm_apply continuous_const).integrable_of_hasCompactSupport hcsv)
    (by simpa using hζ.continuous.integrable_of_hasCompactSupport hcs)
    (fun x _ => differentiableAt_const _) (fun x _ => hζ.differentiable one_ne_zero x)
  simpa using key

## Key steps

1. Dzeta is continuous with support in tsupport zeta, hence Bochner integrable
2. c commutes with the integral: integral of c(Dzeta) = c(integral of Dzeta)
3. evaluate the L-valued integral in each direction v
4. integration by parts with f = 1 (equivalently Fubini + FTC on lines) gives integral of Dzeta(x)v dx = 0
5. hence the integral equals c(0) = 0

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
