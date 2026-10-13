# Parent-supplied natural-language proof

- Parent DAG node: `root.varifold_tangents-a1.density_lower_bound-a1`
- Child DAG node: `root.varifold_tangents-a1.density_lower_bound-a1.bad_set_weight-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 7 of the parent proof, for one fixed scale t. The parent applies it with t = t_j, c = (ofReal τ)⁻¹, and E the set where Θ^n(μ_V,·) ≥ τ fails. No hypothesis on c is needed: every step below is monotone in c.

1. (Measurable hull.) Put E' := {z : z ∈ closedBall x (tR) ∧ z ∈ E} and Ẽ := toMeasurable μ_V E'. Then Ẽ is Borel (measurableSet_toMeasurable), E' ⊆ Ẽ (subset_toMeasurable), and μ_V(Ẽ) = μ_V(E') (measure_toMeasurable). Let A := {y : x + t•y ∈ Ẽ}. A is Borel as the preimage of Ẽ under the continuous map y ↦ x + t•y.

2. (Inclusion.) We show {y : x + t•y ∈ E} ∩ O ⊆ A. Let x + t•y ∈ E and y ∈ O. Since O ⊆ ball 0 R, ‖y‖ < R. So dist(x + t•y, x) = ‖t•y‖ = t‖y‖ ≤ tR, using t > 0 (add_sub_cancel_left, norm_smul, abs_of_pos). Hence x + t•y ∈ E' ⊆ Ẽ, i.e. y ∈ A.

3. (Pass to the rescaled measure.) By step 2 and monotonicity of measures:
  μ_W({y : x + t•y ∈ E} ∩ O) ≤ μ_W(A) = W.measure(A × G)   (Varifold.weight_apply, A Borel)
    = c·(rescaledMeasure V x t).restrict(ball 0 R × G)(A × G)   (Measure.smul_apply)
    ≤ c·rescaledMeasure V x t (A × G).
  The last inequality holds because restriction does not increase a measure (Measure.restrict_le_self) and multiplication by c is monotone.

4. (Rescaled mass.) By part (i) of the sibling rescaled_mass_formula (Submission.varifold_tangents_dlb_rescaledMeasure_prod_univ, applied to the Borel set A), rescaledMeasure V x t (A × G) = ofReal((t⁻¹)^n)·μ_V({z : t⁻¹•(z − x) ∈ A}).
  - For every z, x + t•(t⁻¹•(z − x)) = x + (z − x) = z, since t ≠ 0 (smul_smul, mul_inv_cancel₀, one_smul, add_sub_cancel).
  - So {z : t⁻¹•(z − x) ∈ A} = {z : z ∈ Ẽ} = Ẽ, and μ_V(Ẽ) = μ_V(E') by step 1.
  Thus rescaledMeasure V x t (A × G) = ofReal((t⁻¹)^n)·μ_V(E').

5. (Arithmetic.) Let T := ofReal(t)^n and Q := ofReal(R)^n; both lie in (0,∞) because t, R > 0. Write M := μ_V(E').
  - ofReal((t⁻¹)^n) = T⁻¹ (ENNReal.ofReal_pow, ENNReal.ofReal_inv_of_pos, ENNReal.inv_pow).
  - ofReal(tR)^n = T·Q (ENNReal.ofReal_mul, mul_pow).
  - Q·(M/(T·Q)) = Q·((T·Q)⁻¹·M) = Q·(T⁻¹·Q⁻¹)·M (ENNReal.mul_inv, using T ∈ (0,∞)) = (Q·Q⁻¹)·(T⁻¹·M) = T⁻¹·M (ENNReal.mul_inv_cancel, Q ≠ 0, Q ≠ ∞).
  Hence ofReal((t⁻¹)^n)·μ_V(E') = ofReal(R)^n·(μ_V(E')/ofReal(tR)^n).

6. (Conclusion.) Steps 3–5 give μ_W({y : x + t•y ∈ E} ∩ O) ≤ c·(ofReal(R)^n·(μ_V(E')/ofReal(tR)^n)), where E' = {z : z ∈ closedBall x (tR) ∧ z ∈ E}. This is the claim. ∎

## Key steps

1. Replace E' = {z ∈ closedBall x (tR) : z ∈ E} by its measurable hull Ẽ = toMeasurable μ_V E', and set A = {y : x + t•y ∈ Ẽ} (Borel).
2. {y : x+t•y ∈ E} ∩ O ⊆ A, because ‖y‖ < R puts x + t•y in closedBall x (tR).
3. μ_W(A) = W.measure(A × G) ≤ c·rescaledMeasure V x t (A × G) (Measure.restrict_le_self).
4. Sibling rescaled_mass_formula (i) and {z : t⁻¹•(z−x) ∈ A} = Ẽ give c·ofReal(t⁻¹^n)·μ_V(E').
5. ENNReal arithmetic: ofReal(t⁻¹^n)·M = ofReal(R)^n·(M/ofReal(tR)^n).

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum <snapshot>/project/GMT/Ch08/Contract.lean GMT/Ch08/Contract.lean GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `rg -n 'rescaledMeasure|densityRatio|HasDensity' <snapshot>/project/GMT/Ch08/Contract.lean`
- `rg -c 'varifold_tangents|rescaledMeasure_prod|hasDensity_of_closedBall' <snapshot>/project (exit 1: no match)`
- `rg -n 'lemma absolutelyContinuous_smul|theorem integral_smul_measure|theorem setIntegral_eq_integral_of_forall_compl_eq_zero|theorem measure_toMeasurable|theorem subset_toMeasurable|theorem measurableSet_toMeasurable|protected theorem Tendsto.const_mul|theorem measure_ball_pos|theorem measure_ball_lt_top|theorem ae_restrict_iff\'|theorem restrict_apply_le|theorem restrict_le_self|theorem tendsto_add_atTop_iff_nat|theorem ofReal_inv_of_pos|protected theorem mul_inv|protected theorem inv_mul_cancel|protected theorem mul_inv_cancel|protected theorem inv_pow|theorem ofReal_pow|theorem ae_all_iff|theorem tendsto_nhdsWithin_iff|Ioo_mem_nhdsGT' <snapshot>/mathlib/Mathlib`
- `grep -n '^theorem|^def|^structure|^abbrev' .lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean, VarifoldConvergence.lean, FirstVariationRiesz.lean, TangentRescaling.lean`
- `sed -n 540,630p book/sources/chapter-08-source.txt (printed 5.5–5.7)`
- `python dag.json scan of all node ids/lean_names/lean_statements; grep -o 'varifold_tangents_dlb[A-Za-z0-9_]*' dag.json, node dirs, cluster-state/verification/results; git grep over all 138 refs (no match)`
- `lake env lean /tmp/dlb-decomp/T1.lean (statement elaboration), T2.lean (parent glue from sorry'd children + sibling stubs), T3.lean/T4.lean (child proofs), T5.lean (#print axioms), T6.lean (comparator-scope replay 'exact Submission.X')`
- `python lean_contract.validate_lean_statement and gmt-compare.contract_scope on the 7 statements`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/AbsolutelyContinuous.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/NhdsWithin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Order/LeftRightNhds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/VarifoldConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/FirstVariationRiesz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/TangentRescaling.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-08-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-varifold-tangents-a1-density-lower-bound-a1/parent-child-handoff.json`

Snapshot = project 63436ae6 + Mathlib 25730c7c. Its project/GMT/Ch08/Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

No match: the snapshot project has no declaration for any proposed child (varifold_tangents*, rescaledMeasure_prod*, hasDensity_of_closedBall* all absent), so each child is a new obligation.

What the children rely on:
- Mathlib (snapshot): Measure.absolutelyContinuous_smul (AbsolutelyContinuous.lean:169); integral_smul_measure (Bochner/Basic.lean:1052); setIntegral_eq_integral_of_forall_compl_eq_zero (Bochner/Set.lean:486); toMeasurable lemmas (MeasureSpaceDef.lean:333–348); ENNReal.Tendsto.const_mul (Instances/ENNReal/Lemmas.lean:354); measure_ball_pos (OpenPos.lean:212) and measure_ball_lt_top (Typeclasses/Finite.lean:373); ae_restrict_iff', restrict_apply_le and restrict_le_self (Restrict.lean); tendsto_add_atTop_iff_nat (AtTopBot/Basic.lean:337); ENNReal.mul_inv, inv_mul_cancel, mul_inv_cancel and inv_pow (Basic/ENNReal/Inv.lean); ofReal_pow (Basic/ENNReal/Real.lean:306); ae_all_iff (AE.lean:151); tendsto_nhdsWithin_iff (NhdsWithin.lean:474); Ioo_mem_nhdsGT (used at LeftRightNhds.lean:58).
- SimonGMT (pinned): Varifold.weight_apply, weight_finite_on_compact, finite_on_compact, isOpen_domain and support_tangentialDivergence_subset (Varifold.lean), and firstVariationRieszMeasure_eq_norm (FirstVariationRiesz.lean:218). TangentRescaling.blowUpMeasure has the same form as the contract's rescaledMeasure but is not needed.
- Printed source: Simon Ch. 8, 5.5 steps (3)–(7) and 5.7, at chapter-08-source.txt:540–630. It invokes 3.7 only in one line, so the child proofs are extracted from the parent-supplied steps 2, 3, 5, 6, 7 and 9.

Lean checks:
- All 7 statements elaborate in the comparator scope, pass validate_lean_statement, and replay with 'exact Submission.X'.
- All 7 are fully proved, using only propext, Classical.choice and Quot.sound.
- The parent glue proves the selected frozen type verbatim from the children plus the two sibling contracts.

Names: varifold_tangents_dlb_* is free in the whole run.
