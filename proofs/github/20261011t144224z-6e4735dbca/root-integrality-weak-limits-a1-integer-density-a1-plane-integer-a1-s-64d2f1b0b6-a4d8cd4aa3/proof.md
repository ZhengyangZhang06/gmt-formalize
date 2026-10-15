# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.slice_selection-a1`
- Child DAG node: `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.slice_selection-a1.cycle_slice_boundary-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 3 of the parent proof (Simon Ch. 6, (4.6) with ∂T = 0).

Conventions. (R1) is the second conjunct of the comparator-accepted declaration Submission.iwl_restriction_theory: if U is open, then any two restrictions (IsRestriction) of the same current X ∈ D_k(U) to the same set are equal. Write A_t := {x ∈ U : f(x) < t}.

1. Unfold IsSlice T f t S. There are A ∈ D_{m+1}(U) and B ∈ D_m(U) such that:
 (a) IsRestriction T A_t A;
 (b) IsRestriction ∂T A_t B;
 (c) S(ω) = ∂A(ω) − B(ω) for every ω ∈ D^m(U).
2. The zero current 0 ∈ D_m(U) is a restriction of ∂T to A_t:
 (i) A_t is measurable, by the first component of (b).
 (ii) Take the zero measure μ := 0 and v := 0 : ℝ^P → Λ_m(ℝ^P). Then IsMeasureRepresentation ∂T 0 0 holds. For each test form ω, the function x ↦ 0(ω(x)) is integrable with respect to the zero measure, since every function is (integrable_zero_measure). Moreover ∂T(ω) = 0, because ∂T = 0 and the zero current vanishes on every form (GeometricCurrentOn.zero_apply), and ∫ 0(ω(x)) d0(x) = 0, an integral against the zero measure.
 (iii) For each ω, 0(ω) = 0 = ∫_{A_t} 0(ω(x)) d0(x).
3. Apply (R1) to U (open), the current ∂T ∈ D_m(U), the set A_t and its two restrictions B (from (b)) and 0 (from step 2). This gives B = 0.
4. For every ω ∈ D^m(U), (c) and step 3 give S(ω) = ∂A(ω) − 0(ω) = ∂A(ω) − 0 = ∂A(ω). By extensionality of currents (GeometricCurrentOn.ext), ∂A = S.
5. By (a), A is a restriction of T to A_t = {x ∈ U : f(x) < t}, and ∂A = S by step 4. Hence A is the required current. ∎

## Key steps

1. Unfold IsSlice: there are restrictions A of T and B of ∂T to A_t = {x ∈ U : f(x) < t} with S = ∂A − B.
2. 0 is a restriction of ∂T = 0 to A_t: A_t is measurable (from B's restriction); use μ := 0, v := 0.
3. Uniqueness (R1) of Submission.iwl_restriction_theory gives B = 0.
4. Hence S(ω) = ∂A(ω) for all ω, and ∂A = S by GeometricCurrentOn.ext.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (local-project; project d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `diff GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (identical)`
- `python3 scan of dag.json (572 nodes): frozen types/status of ind_pi_good_slice_selection, iwl_restriction_theory, iwl_restriction_weak_limit; all lean_statements containing IsSlice, IsRestriction+massOn, ∫⁻+StrictMono/Countable; lean_names matching slice|fatou|liminf|restrict.*mass|cycle; collision check for ind_pi_ss_*`
- `git show <accepted restriction-limit branch>:GMT/Ch06/Submission.lean | grep Submission.iwl_restriction_theory (how accepted declarations are reused)`
- `grep -n 'structure GeometricCurrentOn|instance.*Zero|GeometricCurrentOn.ext|zero_apply|def massOn|NVector' simongmt Chapter06/{Currents,Mass,FormsDuality}.lean`
- `rg in snapshot mathlib: lintegral_liminf_le, Measurable.liminf, liminf_le_of_frequently_le', ae_lt_top, Set.Countable.measure_zero, measure_eq_zero_iff_ae_notMem, ae_restrict_of_ae, ae_restrict_mem, Measure.restrict_eq_zero, Real.volume_Ioo, ae_neBot, Filter.Eventually.exists, extraction_of_frequently_atTop, frequently_lt_of_liminf_lt, norm_fderiv_le_of_lipschitz, integrable_zero_measure, mul_le_mul_right, ENNReal.lt_add_right, LipschitzWith.lipschitzOnWith, isOpen_lt, StrictMono.tendsto_atTop`
- `grep -n '8.2|selection argument|4.5(1)|6.7(2)' book/chapter-06.txt; sed -n 1225,1260p and 2405,2450p book/chapter-06.txt; sed -n 1505,1575p book/chapter-02.txt`
- `verifier gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') and lean_contract.validate_lean_statement on the 4 child statements`
- `lake env lean /tmp/ssel-decomp/Stmts.lean; lake env lean /tmp/ssel-decomp/Asm.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1-s-253346ea31/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1-s-253346ea31/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/NullSingletonClass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Filter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Filter/AtTopBot/Tendsto.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Filter/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/ssel-decomp/Stmts.lean`
- `/tmp/ssel-decomp/Asm.lean`

Snapshot pins project d8d46c95 and Mathlib 25730c7c. Contract.lean and Submission.lean are byte-identical.

Accepted declarations that children may use:
- Submission.iwl_restriction_theory (accepted): (R0) a measure representation gives finite mass; (R1) restrictions are unique; (R2) existence of a mass measure, restrictions to measurable sets, and the formula M_W(S) = μ(W ∩ A). Accepted branches embed it as `theorem Submission.iwl_restriction_theory` in Submission.lean.
- Its frozen type and RWL's frozen type (iwl_restriction_weak_limit, accepted) are byte-identical to the strings used in the checks.

SimonGMT supplies:
- GeometricCurrentOn.ext and the Zero instance with zero_apply (Currents.lean:305–319);
- massOn as the sSup of ofReal (T ω) over admissible forms, so M_V(0) = 0 (Mass.lean).

All Mathlib lemmas cited in the child proofs exist in the snapshot, for example:
- lintegral_liminf_le (Lebesgue/Add.lean:233), Measurable.liminf (BorelSpace/Order.lean:1058), ae_lt_top (Markov.lean:159);
- Set.Countable.measure_zero (NullSingletonClass.lean:58), Real.volume_Ioo (Lebesgue/Basic.lean:96), ae_neBot (Measure/Filter.lean:44);
- extraction_of_frequently_atTop (AtTopBot/Basic.lean:114), frequently_lt_of_liminf_lt (generated by to_dual at LiminfLimsup.lean:645);
- norm_fderiv_le_of_lipschitz (FDeriv/Basic.lean:947), integrable_zero_measure (Integrable.lean:283), mul_le_mul_right (Monoid/Unbundled/Basic.lean:58; the old mul_le_mul_left' is not present).

DAG: no node is named ind_pi_ss_*, and no node has a type equivalent to any child. The closest are slicing_mass_bound, smr_restriction_massOn_eq and iwl_rl_monotone_helly_selection, none of them equivalent.

Book: the printed Proof of 8.2 (chapter-06.txt ~2424–2435) obtains display (8) 'by 4.5(1) and a selection argument as in 6.7(2) of Ch. 2' (chapter-02.txt ~1540–1565). The supplied Steps 6–8 are its Fatou form.

Lean checks in the exact comparator scope:
- all four child statements and the parent elaborate;
- assembly_parent (the parent from the three direct children), assembly_B, leaf_C, leaf_B1 and leaf_A all compile with axioms [propext, Classical.choice, Quot.sound] only.
