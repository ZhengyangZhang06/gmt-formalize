# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1.allard_lemma-a1.cylinder_monotonicity-a1`
- Child DAG node: `root.integral_compactness-a1.allard_lemma-a1.cylinder_monotonicity-a1.cylinder_weight-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 0 and 2 of the parent proof (Simon 8.5.10, printed (7), where h(z) = f(|q(z − y)|) with f ≡ 1 on [0,τ) and f ≡ 0 on (2τ,∞), and |∇^S f(|q(z − y)|)| ≤ |f′|·|p_S − p|). The parent's h(z) := st(4 − ‖q(z − y)‖²/τ²) is used, and M₀ := 4L, where L bounds |Real.smoothTransition′|; no numerical value of L is needed.
Notation. st := Real.smoothTransition: C^∞ (Real.smoothTransition.contDiff), monotone, 0 ≤ st ≤ 1 (nonneg, le_one), st(u) = 0 for u ≤ 0 (zero_of_nonpos), st(u) = 1 for u ≥ 1 (one_of_one_le). st′ := deriv st.

1. st′ vanishes off [0,1]. If u < 0, then st = 0 on the open neighbourhood (−∞,0) of u, so st′(u) = 0 (Filter.EventuallyEq.deriv_eq, deriv_const). If u > 1, then st = 1 on the open neighbourhood (1,∞) of u, so st′(u) = 0.

2. The constant. st is C¹, so st′ is continuous (ContDiff.continuous_deriv). By step 1 the support of st′ lies in the compact set [0,1], so st′ has compact support and is bounded (HasCompactSupport.exists_bound_of_continuous). Fix L with |st′(u)| ≤ L for all u ∈ ℝ. Then L ≥ |st′(0)| ≥ 0. Put M₀ := 4L ≥ 0. It does not depend on N, n, P, y or τ.

3. Set-up. Fix N, n, P, y and τ > 0. Let p := projectionLinearMap P, so p_P(v) = p(v). The map p is self-adjoint (projectionLinearMap_isSymmetric) and idempotent (project_project). Let Q := id − p, regarded as a continuous linear map on the finite-dimensional space ℝ^N, so Q(v) = v − p_P(v) = q(v). Define F(z) := ‖Q(z − y)‖²/τ² and h(z) := st(4 − F(z)). Note F(z) = ‖q(z − y)‖²/τ².

4. Property (i). z ↦ Q(z − y) is a continuous affine map, hence C^∞. The map v ↦ ‖v‖² is C^∞ (contDiff_norm_sq). Dividing by the constant τ² ≠ 0, subtracting from 4 and composing with the C^∞ function st keep the map C^∞. So h is C^∞, in particular C¹.

5. Property (ii) holds because st takes values in [0,1].

6. Property (iii). If ‖q(z − y)‖ < τ, then ‖q(z − y)‖² < τ² because both sides are non-negative. So F(z) < 1 and 4 − F(z) > 3 ≥ 1, hence h(z) = 1.

7. Property (iv). If ‖q(z − y)‖ ≥ 2τ > 0, then ‖q(z − y)‖² ≥ 4τ², so F(z) ≥ 4 and 4 − F(z) ≤ 0. Hence h(z) = 0.

8. Derivative formula. Fix z and put w := z − y and a := Q w = q(w). The map z′ ↦ Q(z′ − y) has derivative Q at z. By HasFDerivAt.norm_sq, z′ ↦ ‖Q(z′ − y)‖² has derivative v ↦ 2⟨a, Q v⟩, so DF(z)[v] = (2/τ²)⟨a, Q v⟩. The map s ↦ st(4 − s) has derivative −st′(4 − s) at s (chain rule with the derivative −1 of s ↦ 4 − s). By the chain rule (HasDerivAt.comp_hasFDerivAt), for all v ∈ ℝ^N:
  Dh(z)[v] = −st′(4 − F(z))·(2/τ²)·⟨a, Q v⟩.

9. Inner-product identity. Let S ∈ G(N,n) and T := LinearMap.toContinuousLinearMap(projectionLinearMap S − projectionLinearMap P), so ‖T‖ = t_P(S). Because p is idempotent, p a = p w − p(p w) = 0. For v := p_S w, self-adjointness of p gives
  ⟨a, Q v⟩ = ⟨a, v⟩ − ⟨a, p v⟩ = ⟨a, v⟩ − ⟨p a, v⟩ = ⟨a, v⟩.
 Self-adjointness of p_S gives ⟨a, p_S w⟩ = ⟨p_S a, w⟩, and p_S a = p_S a − p a = T a. Hence ⟨a, Q(p_S w)⟩ = ⟨T a, w⟩. By Cauchy–Schwarz (abs_real_inner_le_norm) and ContinuousLinearMap.le_opNorm,
  |⟨a, Q(p_S w)⟩| ≤ ‖T a‖·‖w‖ ≤ t_P(S)·‖a‖·‖w‖.

10. Property (v). By steps 8 and 9, |Dh(z)[p_S w]| = |st′(4 − F(z))|·(2/τ²)·|⟨T a, w⟩|.
 – If st′(4 − F(z)) = 0, the left side is 0. The right side (M₀/τ)·t_P(S)·‖w‖ is a product of non-negative numbers, so the bound holds.
 – Otherwise step 1 forces 4 − F(z) ≥ 0, i.e. ‖a‖² ≤ 4τ², so ‖a‖ ≤ 2τ. Using |st′| ≤ L and step 9,
  |Dh(z)[p_S w]| ≤ L·(2/τ²)·t_P(S)·(2τ)·‖w‖ = (4L/τ)·t_P(S)·‖w‖ = (M₀/τ)·t_P(S)·‖z − y‖.
Thus h satisfies (i)–(v). ∎

## Key steps

1. st′ = 0 off [0,1] (st locally constant there); st′ continuous with compact support, so |st′| ≤ L for some L ≥ 0; M₀ := 4L
2. h(z) := st(4 − ‖q(z − y)‖²/τ²) is C^∞ (contDiff_norm_sq, affine maps) with values in [0,1]
3. h = 1 where ‖q(z − y)‖ < τ and h = 0 where ‖q(z − y)‖ ≥ 2τ
4. Chain rule: Dh(z)[v] = −st′(4 − F(z))·(2/τ²)·⟨q w, Q v⟩ with Q = id − p_P, w = z − y
5. p_P(q w) = 0 and self-adjointness of p_P, p_S give ⟨q w, Q(p_S w)⟩ = ⟨(p_S − p_P)(q w), w⟩, of absolute value ≤ t_P(S)‖q w‖‖w‖
6. st′(4 − F(z)) ≠ 0 forces ‖q w‖ ≤ 2τ, so |Dh(z)[p_S w]| ≤ (4L/τ)·t_P(S)·‖w‖ = (M₀/τ)·t_P(S)·‖z − y‖

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
