# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1.allard_lemma-a1.cylinder_monotonicity-a1`
- Child DAG node: `root.integral_compactness-a1.allard_lemma-a1.cylinder_monotonicity-a1.cutoff_integral_tendsto-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent proof: "By dominated convergence (tendsto_integral_filter_of_dominated_convergence), Ĩ_{η_j}(t) → I(t) := ∫_{B_t(y)} h dμ". The dominating function there is the indicator of a closed ball of finite measure. Here the argument is stated for a general family of cutoffs.
Notation. B_r(y) := closedBall y r, a closed and hence measurable set. Put F_j(z) := φ_j(‖z − y‖²/t²)·h(z), f := 1_{B_t(y)}·h (the indicator of B_t(y) applied to h), and g := 1_{B_R(y)}, the indicator of B_R(y) of the constant 1.

1. Reduction. B_t(y) is measurable, so ∫_{B_t(y)} h dμ = ∫ f dμ (integral_indicator). It therefore suffices to show ∫ F_j dμ → ∫ f dμ. This follows from the dominated convergence theorem (tendsto_integral_filter_of_dominated_convergence, filter atTop on ℕ) with bound g. Its four hypotheses are verified in steps 2–5.

2. Measurability. z ↦ ‖z − y‖²/t² is continuous, hence measurable. φ_j and h are measurable, so every F_j is measurable and in particular AE strongly measurable.

3. Domination: ‖F_j(z)‖ ≤ g(z) for all j and all z.
 – If z ∈ B_R(y), then 0 ≤ F_j(z) = φ_j(‖z − y‖²/t²)·h(z) ≤ 1·1 = 1 = g(z).
 – If z ∉ B_R(y), then ‖z − y‖ > R ≥ t·A_j > 0, using t > 0 and A_j > 0. Hence ‖z − y‖² > (t·A_j)² = A_j²·t², i.e. ‖z − y‖²/t² ≥ A_j². So φ_j(‖z − y‖²/t²) = 0 and F_j(z) = 0 = g(z).

4. Integrability of g. μ(B_R(y)) < ∞, so the constant 1 is integrable on B_R(y) (integrableOn_const). Since B_R(y) is measurable, its indicator g is integrable (integrable_indicator_iff).

5. Pointwise convergence at every z.
 – If ‖z − y‖ ≤ t, then ‖z − y‖²/t² ≤ 1 (as t > 0). So φ_j(‖z − y‖²/t²) = 1 and F_j(z) = h(z) = f(z) for every j.
 – If ‖z − y‖ > t, then s := ‖z − y‖²/t² > 1. As A_j → 1 we have A_j² → 1 < s, so A_j² ≤ s for all sufficiently large j. For those j, φ_j(s) = 0 and F_j(z) = 0 = f(z).
 In both cases F_j(z) → f(z).

6. By steps 2–5 and dominated convergence, ∫ F_j dμ → ∫ f dμ = ∫_{B_t(y)} h dμ. ∎

## Key steps

1. Rewrite ∫_{B_t(y)} h dμ as ∫ 1_{B_t(y)} h dμ (integral_indicator) and apply dominated convergence with bound 1_{B_R(y)}
2. Measurability of F_j(z) = φ_j(‖z − y‖²/t²)h(z)
3. Domination: F_j ∈ [0,1], and F_j(z) = 0 off B_R(y) because ‖z − y‖ > R ≥ tA_j gives ‖z − y‖²/t² ≥ A_j²
4. 1_{B_R(y)} is integrable since μ(B_R(y)) < ∞
5. Pointwise limit: φ_j(…) = 1 for ‖z − y‖ ≤ t; for ‖z − y‖ > t, A_j² → 1 < ‖z − y‖²/t² makes φ_j(…) = 0 eventually

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
