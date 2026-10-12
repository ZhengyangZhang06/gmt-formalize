# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1.allard_lemma-a1.cylinder_monotonicity-a1`
- Child DAG node: `root.integral_compactness-a1.allard_lemma-a1.cylinder_monotonicity-a1.cylinder_mass_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent proof: "By step 2(c) and 0 ≤ h ≤ 1, μ(U^τ_σ(y)) ≤ I(σ) and I(ρ) ≤ μ(U^{2τ}_ρ(y)) … Applying ENNReal.ofReal … gives the asserted inequality in [0,∞]". Here the comparison is stated for any h with these properties.
Notation. B_r(y) := closedBall y r. S₁ := {z : ‖q(z − y)‖ < τ}, S₂ := {z : ‖q(z − y)‖ < 2τ}, U₁ := B_σ(y) ∩ S₁ and U₂ := B_ρ(y) ∩ S₂. For a set U of finite measure write μ_ℝ(U) := (μ U).toReal (= μ.real U).

1. Borel sets. p_P = projectionLinearMap P is a linear map on the finite-dimensional space ℝ^N, hence continuous (LinearMap.continuous_of_finiteDimensional). So z ↦ ‖q(z − y)‖ = ‖(z − y) − p_P(z − y)‖ is continuous, and S₁, S₂ are open, hence measurable. Closed balls are measurable.

2. Finiteness. Since σ ≤ ρ, B_σ(y) ⊆ B_ρ(y), so μ(B_σ(y)) ≤ μ(B_ρ(y)) < ∞. Also μ(U₁) ≤ μ(B_σ(y)) < ∞ and μ(U₂) ≤ μ(B_ρ(y)) < ∞.

3. Integrability. h is measurable with |h| ≤ 1, so h is integrable on every set of finite μ-measure (Measure.integrableOn_of_bounded), in particular on B_σ(y), B_ρ(y) and U₂. The constant 1 is integrable on U₂ (integrableOn_const).

4. Lower comparison. h = 1 on U₁ ⊆ S₁, so ∫_{U₁} h dμ = ∫_{U₁} 1 dμ = μ_ℝ(U₁) (setIntegral_congr_fun, setIntegral_const). Since h ≥ 0 and U₁ ⊆ B_σ(y), ∫_{U₁} h dμ ≤ ∫_{B_σ(y)} h dμ (setIntegral_mono_set). Hence μ_ℝ(U₁) ≤ ∫_{B_σ(y)} h dμ.

5. Upper comparison. Split B_ρ(y) along the measurable set S₂ (integral_inter_add_sdiff):
  ∫_{B_ρ(y)} h dμ = ∫_{U₂} h dμ + ∫_{B_ρ(y)∖S₂} h dμ.
 For z ∈ B_ρ(y) ∖ S₂ we have ‖q(z − y)‖ ≥ 2τ, so h(z) = 0, and the second integral is 0 (setIntegral_eq_zero_of_forall_eq_zero). On U₂ we have h ≤ 1, so ∫_{U₂} h dμ ≤ ∫_{U₂} 1 dμ = μ_ℝ(U₂) (setIntegral_mono_on, setIntegral_const). Hence ∫_{B_ρ(y)} h dμ ≤ μ_ℝ(U₂).

6. Real inequality. Since σ^n > 0 and ρ^n > 0, steps 4 and 5 and the hypothesis give
  μ_ℝ(U₁)/σ^n ≤ (∫_{B_σ(y)} h dμ)/σ^n ≤ (∫_{B_ρ(y)} h dμ)/ρ^n + E ≤ μ_ℝ(U₂)/ρ^n + E.

7. Conversion to [0,∞]. Let r > 0 and let U have μ(U) < ∞. Then μ(U) = ofReal(μ_ℝ(U)) (ENNReal.ofReal_toReal) and ofReal(r)^n = ofReal(r^n) (ENNReal.ofReal_pow). Since r^n > 0, ofReal(μ_ℝ(U))/ofReal(r^n) = ofReal(μ_ℝ(U)/r^n) (ENNReal.ofReal_div_of_pos). Therefore
  μ(U₁)/ofReal(σ)^n = ofReal(μ_ℝ(U₁)/σ^n)
   ≤ ofReal(μ_ℝ(U₂)/ρ^n + E)   (step 6 and monotonicity of ofReal)
   ≤ ofReal(μ_ℝ(U₂)/ρ^n) + ofReal(E)   (ENNReal.ofReal_add_le)
   = μ(U₂)/ofReal(ρ)^n + ofReal(E).
 Since U₁ and U₂ are exactly the sets in the conclusion, this is the asserted inequality. ∎

## Key steps

1. S₁ = {‖q(z − y)‖ < τ}, S₂ = {‖q(z − y)‖ < 2τ} are open (p_P continuous); all sets involved have finite μ-measure
2. h is integrable on finite-measure sets (|h| ≤ 1, measurable)
3. μ(B_σ ∩ S₁) = ∫_{B_σ ∩ S₁} h ≤ ∫_{B_σ} h since h = 1 on S₁ and h ≥ 0
4. ∫_{B_ρ} h = ∫_{B_ρ ∩ S₂} h ≤ μ(B_ρ ∩ S₂) since h = 0 off S₂ and h ≤ 1
5. Real inequality μ(U₁)/σ^n ≤ μ(U₂)/ρ^n + E
6. Convert with ofReal_toReal, ofReal_pow, ofReal_div_of_pos and ofReal_add_le

## Reference use

### local-project

Queries:
- `cat local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum snapshot project/GMT/Ch08/Contract.lean, workspace GMT/Ch08/Contract.lean and GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `rg -n 'theorem HasCompactSupport.exists_bound_of_continuous|theorem tendsto_integral_filter_of_dominated_convergence|theorem HasFDerivAt.norm_sq|theorem integral_inter_add_sdiff|theorem setIntegral_mono_set|theorem integrableOn_of_bounded|theorem ofReal_div_of_pos|theorem ofReal_add_le|theorem abs_real_inner_le_norm|theorem le_opNorm |theorem tendsto_one_div_add_atTop_nhds_zero_nat|theorem HasDerivAt.comp_hasFDerivAt|theorem HasFDerivAt.mul_const |theorem contDiff_norm_sq|theorem setIntegral_eq_zero_of_forall_eq_zero|theorem integral_indicator |theorem le_of_tendsto_of_tendsto.' mathlib/Mathlib`
- `rg -n 'exists_bound_of_continuous|theorem integrableOn_of_bounded|theorem Measure.integrableOn_of_bounded|theorem integrableOn_const' mathlib/Mathlib; rg -n 'exists_bound_of_continuous' mathlib/Mathlib/Topology mathlib/Mathlib/Analysis/Normed/Group`
- `rg -n 'theorem|lemma|def smoothTransition' and rg -n 'deriv' mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `rg -n 'cylinder|smoothTransition|intcpt_allard' project/GMT`
- `grep -n 'def project|def projectionLinearMap|projectionLinearMap_isSymmetric|theorem project_project|structure Varifold|def weight|weight_finite_on_compact' simongmt Poincare/SimonGMT/Chapter08/Varifold.lean`
- `grep -n 'integrating 3.5|simply integrating' book/chapter-08.txt`
- `lake env lean /tmp/cm-decomp-v1/Probe.lean and /tmp/cm-decomp-v1/proofs/Probe1.lean (#check from import GMT.Ch08.Submission)`
- `lake env lean /tmp/cm-decomp-v1/Assembly.lean (sibling + 4 sorried children + sorry-free parent assembly)`
- `lake env lean /tmp/cm-decomp-v1/Full.lean (4 children fully proved, #print axioms)`
- `python3 -I /tmp/cm-decomp-v1/gen/compform.py (verifier lean_contract.validate_lean_statement + gmt-compare.child_modules in contract mode) and lake env lean /tmp/cm-decomp-v1/CompForm0..3.lean`
- `python3 scan of dag.json lean_names; grep -rl 'intcpt_allard_cm_' run directory; git grep 'intcpt_allard_cm_' over every ref tip (221 distinct objects of 521 refs)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-08.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-cylinder-monotonicity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-weighted-radial-monotonicity-a1/parent-child-handoff.json`
- `/tmp/cm-decomp-v1/Assembly.lean`
- `/tmp/cm-decomp-v1/Full.lean`
- `/tmp/cm-decomp-v1/CompForm0.lean`
- `/tmp/cm-decomp-v1/CompForm1.lean`
- `/tmp/cm-decomp-v1/CompForm2.lean`
- `/tmp/cm-decomp-v1/CompForm3.lean`

The snapshot is project 63436ae6 + Mathlib 25730c7c. Its Contract is byte-identical to the workspace Contract and Submission.

No existing project or SimonGMT lemma gives a cylinder weight, a smoothTransition derivative bound or the cutoff limit. rg over project/GMT finds only an unrelated README line, and SmoothTransition.lean has no derivative lemma. So the children are proved from library facts in the snapshot:
- Real.smoothTransition contDiff, monotone, nonneg, le_one, zero_of_nonpos and one_of_one_le (SmoothTransition.lean:161–222)
- HasCompactSupport.exists_bound_of_continuous (to_additive of Analysis/Normed/Group/Bounded.lean:98)
- HasFDerivAt.norm_sq (InnerProductSpace/Calculus.lean:211) and contDiff_norm_sq (:140)
- HasFDerivAt.mul_const (FDeriv/Mul.lean:299) and HasDerivAt.comp_hasFDerivAt (Deriv/Comp.lean:171)
- abs_real_inner_le_norm (InnerProductSpace/Basic.lean:471) and le_opNorm (Normed/Operator/Basic.lean:234)
- tendsto_integral_filter_of_dominated_convergence (DominatedConvergence.lean:67)
- integral_indicator, integral_inter_add_sdiff, setIntegral_eq_zero_of_forall_eq_zero and setIntegral_mono_set (Bochner/Set.lean:185, 114, 357, 737)
- Measure.integrableOn_of_bounded and integrableOn_const (IntegrableOn.lean:716, 119)
- ENNReal.ofReal_div_of_pos and ofReal_add_le (Basic/ENNReal/Inv.lean:960, Basic/ENNReal/Real.lean:57)
- tendsto_one_div_add_atTop_nhds_zero_nat (SpecificLimits/Basic.lean:70) and le_of_tendsto_of_tendsto' (OrderClosed.lean:480)
- SimonGMT projectionLinearMap_isSymmetric, project_project and weight_finite_on_compact (Chapter08/Varifold.lean:98, 108, 576)
Each was #checked from import GMT.Ch08.Submission. HasFDerivAt.div_const does not exist and is not used.

The book (chapter-08.txt l.880) confirms that printed (7) is 'proved by simply integrating 3.5 from σ to ρ'.

Verification:
- The four lean_statements pass validate_lean_statement and elaborate in comparator form.
- Assembly.lean proves the parent's frozen type from the four children plus the sibling stub, with no sorry.
- Full.lean proves all four children with axioms propext, Classical.choice and Quot.sound only.
- The four intcpt_allard_cm_* names have 0 hits in dag.json (195 unique names), the run directory and all git ref tips.
