# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_mass_bound-a1.cutoff_defect_bound-a1`
- Child DAG node: `root.slicing-a1.slice_mass_bound-a1.cutoff_defect_bound-a1.band_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Provenance (orientation only; the hypotheses are exactly those of the statement): parent proof, Step 6 (the sets E_j and continuity from above), with K = tsupport ω, a = t − h, b = t and δ_j = 1/(j+1); only closedness of K, continuity of f on K and μ(K) < ∞ are used.

Notation. δ_j := 1/((j : ℝ) + 1), so δ_j > 0 (positivity); I_j := (a − δ_j, b + δ_j); E_j := K ∩ f⁻¹(I_j). The statement asserts μ(E_j) → μ(K ∩ f⁻¹([a, b])).

1. (Measurability.) The complement I_jᶜ of the open interval is closed (isOpen_Ioo.isClosed_compl). Since f is continuous on the closed set K, the set K ∩ f⁻¹(I_jᶜ) is closed (ContinuousOn.preimage_isClosed_of_isClosed). Elementwise, x ∈ E_j ⇔ (x ∈ K ∧ f(x) ∈ I_j) ⇔ (x ∈ K ∧ ¬(x ∈ K ∧ f(x) ∉ I_j)), so E_j = K \ (K ∩ f⁻¹(I_jᶜ)) (ext; simp only [mem_inter_iff, mem_preimage, mem_sdiff, mem_compl_iff]; tauto). Closed sets are Borel (IsClosed.measurableSet), so E_j is measurable (MeasurableSet.diff), in particular null-measurable (MeasurableSet.nullMeasurableSet).

2. (Antitone.) Let i ≤ j. Then 0 < (i : ℝ) + 1 ≤ (j : ℝ) + 1, so δ_j ≤ δ_i (one_div_le_one_div_of_le, or gcongr). Hence a − δ_i ≤ a − δ_j and b + δ_j ≤ b + δ_i, so I_j ⊆ I_i and E_j ⊆ E_i (linarith on both endpoint inequalities). Thus j ↦ E_j is antitone.

3. (Intersection.) ⋂_j E_j = K ∩ f⁻¹([a, b]).
 (⊇) If x ∈ K and a ≤ f(x) ≤ b, then for every j, a − δ_j < a ≤ f(x) ≤ b < b + δ_j because δ_j > 0; so x ∈ E_j for every j.
 (⊆) Let x ∈ E_j for every j. Then x ∈ K (take j = 0). Suppose f(x) < a. Then a − f(x) > 0, so there is j with δ_j = 1/((j : ℝ) + 1) < a − f(x) (exists_nat_one_div_lt). Then f(x) < a − δ_j, contradicting a − δ_j < f(x) (x ∈ E_j). Hence a ≤ f(x). Symmetrically, if f(x) > b, choose j with δ_j < f(x) − b (exists_nat_one_div_lt); then f(x) > b + δ_j, contradicting f(x) < b + δ_j. Hence f(x) ≤ b, and x ∈ K ∩ f⁻¹([a, b]).

4. (Finite start.) μ(E_0) ≤ μ(K) < ∞ (measure_mono with inter_subset_left), so μ(E_0) ≠ ∞.

5. (Continuity from above.) The sequence (E_j) is null-measurable (step 1), antitone (step 2) and μ(E_0) ≠ ∞ (step 4), so tendsto_measure_iInter_atTop gives μ(E_j) → μ(⋂_j E_j) as j → ∞. Rewriting ⋂_j E_j with step 3 yields μ(E_j) → μ(K ∩ f⁻¹([a, b])), which is the claim. ∎

Remark. No relation between a and b is required: if a > b, step 3 still holds (both sides are empty), and steps 1–5 apply verbatim.

## Key steps

1. E_j := K ∩ f⁻¹((a − δ_j, b + δ_j)), δ_j = 1/(j+1), equals K \ (K ∩ f⁻¹((a − δ_j, b + δ_j)ᶜ)) and is measurable (ContinuousOn.preimage_isClosed_of_isClosed, K closed).
2. E_j is antitone because δ_j decreases.
3. ⋂_j E_j = K ∩ f⁻¹([a, b]) (exists_nat_one_div_lt for ⊆; δ_j > 0 for ⊇).
4. μ(E_0) ≤ μ(K) < ∞, then tendsto_measure_iInter_atTop and rewrite the intersection.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `python3 read of nodes/root-slicing-a1-slice-mass-bound-a1-cutoff-defect-bound-a1/{parent-child-handoff.json, parent-supplied-plan.md, parent-supplied-natural-proof.json}`
- `python3 scan of dag.json: sibling lean_statements of smooth_approx-a1, leibniz_bound-a1, wedge_norm-a1; non-sibling dependency census; 235 nodes with unique lean_names, no child of this node yet; patterns 'Tendsto (fun j => ∫', '∫⁻ x, (‖fderiv ℝ', 'Integrable F', 'IsClosed K → ContinuousOn f K' (no identical child type)`
- `python3 read of nodes/root-slicing-a1-slice-mass-bound-a1/decomposition-audit-v1..v5.json and nodes/root-flat-iff-weak-a1-im-series-a1-series-current-a1/decomposition-v2.json (format of depth-4 child contracts)`
- `grep -n 'abbrev NVector|abbrev Covector|abbrev DifferentialForm|def IsTestForm|def testFormOnSubmodule|abbrev TestFormOn|def covectorEuclideanNorm|covectorEuclideanNorm_zero|def exteriorDerivativeTestOn|GeometricCurrentOn.boundary_apply|tsupport_exteriorDerivative_subset|abbrev exteriorDerivative' simongmt/Poincare/SimonGMT/Chapter06/{Forms,FormsDuality,Mass,Currents}.lean`
- `rg -n 'theorem lintegral_indicator_const_le|theorem tendsto_measure_iInter_atTop|theorem tendsto_integral_of_dominated_convergence|theorem ContinuousOn.preimage_isClosed_of_isClosed|theorem ContDiff.differentiable |theorem Tendsto.const_mul|theorem norm_deriv_eq_norm_fderiv|theorem fderiv_comp |theorem ContinuousOn.isOpen_inter_preimage' local-references/197bdd4b88278494/mathlib/Mathlib`
- `rg -n 'exists_nat_one_div_lt|image_eq_zero_of_notMem_tsupport|theorem tendsto_one_div_add_atTop_nhds_zero_nat|theorem le_of_tendsto_of_tendsto|lemma ofReal_norm|lemma enorm_eq_nnnorm|theorem opNorm_comp_le' local-references/197bdd4b88278494/mathlib/Mathlib`
- `rg -n 'slicing_mb_cdb|grad_lintegral_le|band_measure_tendsto|multiplier_integral_tendsto' local-references/197bdd4b88278494/project (no match); rg -l slicing_mb_cdb over the run directory and workspace GMT/ (no match)`
- `python3 contract_scope(GMT/Ch06/Contract.lean, 'GMT.Ch06.main_theorem') and child_modules from verifier/gmt-compare.py; lean_contract.validate_lean_statement on the three child types and the parent`
- `git show <tangent-locality branch>:GMT/Ch06/Submission.lean (accepted declarations are `theorem Submission.X` inside namespace GMT.Ch06)`
- `lean -o /tmp/cdb_split_HHvFLJ/out/GMT/Ch06/Submission.olean GMT/Ch06/Submission.lean (LEAN_PATH from lake env)`
- `lean /tmp/cdb_split_HHvFLJ/check/Stmts.lean (parent, two siblings, three children elaborate in the comparator scope)`
- `lean /tmp/cdb_split_HHvFLJ/check/Children.lean (#print axioms of the three child proofs: [propext, Classical.choice, Quot.sound])`
- `lean /tmp/cdb_split_HHvFLJ/check/Assembly.lean (#print axioms HumanizeCheck.assembly: [propext, Classical.choice, Quot.sound])`
- `lean /tmp/cdb_split_HHvFLJ/check/Named.lean (Submission.* declarations, parent from children + stubbed siblings, comparator-style exact targets)`
- `lean /tmp/cdb_split_HHvFLJ/check/Quoted.lean and /tmp/cdb_split_HHvFLJ/check/NamedQuoted.lean (the assembly text quoted in the rationale, verbatim, in hypothesis form and under the real Submission.* names)`
- `independent reviewer subagent re-check of payload, statements, proofs, lemma names and compiles (verdict: accept with minor fixes, applied)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-cutoff-defect-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1/decomposition-audit-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1/decomposition-audit-v5.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-series-current-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/ContinuousOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/cdb_split_HHvFLJ/check/Stmts.lean`
- `/tmp/cdb_split_HHvFLJ/check/Children.lean`
- `/tmp/cdb_split_HHvFLJ/check/Assembly.lean`
- `/tmp/cdb_split_HHvFLJ/check/Named.lean`
- `/tmp/cdb_split_HHvFLJ/check/Quoted.lean`
- `/tmp/cdb_split_HHvFLJ/check/NamedQuoted.lean`

The pinned snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 contract, and the workspace Submission is the frozen file, so the child types may use only contract, SimonGMT and Mathlib names. SimonGMT supplies DifferentialForm, TestFormOn (membership IsTestForm ∧ tsupport ⊆ U, so ω.property.1.2 : HasCompactSupport), covectorEuclideanNorm with covectorEuclideanNorm_zero, exteriorDerivativeTestOn (its coercion is exteriorDerivative ω by rfl) and tsupport_exteriorDerivative_subset. Mathlib supplies every lemma the child proofs cite: fderiv_fun_comp, norm_deriv_eq_norm_fderiv, ContinuousLinearMap.opNorm_comp_le, lintegral_indicator_const_le (no measurability), ofReal_norm, ContinuousOn.preimage_isClosed_of_isClosed, exists_nat_one_div_lt, tendsto_measure_iInter_atTop, tendsto_integral_of_dominated_convergence, ENNReal.Tendsto.const_mul, le_of_tendsto_of_tendsto' and tendsto_one_div_add_atTop_nhds_zero_nat. Neither library nor the DAG contains the three child statements, so they are new obligations. In a scratch compile of the frozen Submission, all child types elaborate in the comparator scope and pass validate_lean_statement. Their complete Lean proofs compile with axioms [propext, Classical.choice, Quot.sound]. The exact parent type follows from the three children plus the resolved siblings slicing_mb_smooth_approx and slicing_mb_leibniz_bound, also with only those axioms. The proposed names occur nowhere in the snapshot, the workspace or the run directory.
