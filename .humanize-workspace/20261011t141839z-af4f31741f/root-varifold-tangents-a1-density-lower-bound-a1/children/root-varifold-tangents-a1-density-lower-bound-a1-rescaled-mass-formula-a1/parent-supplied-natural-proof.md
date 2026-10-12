# Parent-supplied natural-language proof

- Parent DAG node: `root.varifold_tangents-a1.density_lower_bound-a1`
- Child DAG node: `root.varifold_tangents-a1.density_lower_bound-a1.rescaled_mass_formula-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof.

1. (Measurability.) The map φ(z,S) := (t⁻¹•(z − x), S) on ℝ^N × G(N,n) is continuous, hence Borel measurable. By definition, rescaledMeasure V x t = ofReal((t⁻¹)^n) • V.measure.map φ.

2. (Part (i).) Let A ⊆ ℝ^N be Borel. Then A × G is Borel. The set A' := {z : t⁻¹•(z − x) ∈ A} is Borel, being the preimage of A under the continuous map z ↦ t⁻¹•(z − x).
  - Measure.smul_apply and Measure.map_apply (φ measurable, A × G measurable) give rescaledMeasure V x t (A × G) = ofReal((t⁻¹)^n)·V.measure(φ⁻¹(A × G)).
  - (z,S) ∈ φ⁻¹(A × G) iff t⁻¹•(z − x) ∈ A iff (z,S) ∈ A' × G, so φ⁻¹(A × G) = A' × G.
  - Varifold.weight_apply (A' Borel) gives V.measure(A' × G) = μ_V(A').
  Combining these proves (i).

3. (Part (ii).) Assume t > 0 and fix y ∈ ℝ^N, ρ ∈ ℝ. Apply (i) with A := closedBall y ρ, which is closed and hence Borel. It remains to show {w : t⁻¹•(w − x) ∈ closedBall y ρ} = closedBall (x + t•y) (tρ).
  - For w ∈ ℝ^N, t⁻¹•(w − (x + t•y)) = t⁻¹•w − t⁻¹•x − (t⁻¹t)•y = t⁻¹•(w − x) − y, because t⁻¹t = 1 (smul_sub, smul_add, smul_smul, inv_mul_cancel₀, one_smul).
  - Hence dist(t⁻¹•(w − x), y) = ‖t⁻¹•(w − (x + t•y))‖ = t⁻¹·‖w − (x + t•y)‖, since t⁻¹ > 0 (norm_smul, abs_of_pos).
  - As t > 0, t⁻¹·d ≤ ρ iff d ≤ tρ (div_le_iff₀).
  So w lies in the left-hand set iff dist(w, x + t•y) ≤ tρ, i.e. iff w ∈ closedBall (x + t•y) (tρ). Substituting this set identity into (i) gives (ii). ∎

## Key steps

1. rescaledMeasure V x t = ofReal(t⁻¹^n) • V.measure.map φ with φ(z,S) = (t⁻¹•(z−x),S) continuous.
2. φ⁻¹(A × G) = {z : t⁻¹•(z−x) ∈ A} × G; Measure.smul_apply, Measure.map_apply and Varifold.weight_apply give (i).
3. For t > 0: t⁻¹•(w−x) − y = t⁻¹•(w − (x+t•y)), so {w : t⁻¹•(w−x) ∈ B_ρ(y)} = B_{tρ}(x+t•y), and (ii) follows from (i).

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
