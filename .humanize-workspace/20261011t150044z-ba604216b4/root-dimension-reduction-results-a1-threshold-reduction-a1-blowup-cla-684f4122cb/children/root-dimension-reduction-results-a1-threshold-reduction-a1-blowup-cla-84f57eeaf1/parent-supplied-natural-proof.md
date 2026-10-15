# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.threshold_reduction-a1.blowup_class-a1.class_tangent-a1`
- Child DAG node: `root.dimension_reduction_results-a1.threshold_reduction-a1.blowup_class-a1.class_tangent-a1.zero_imrep-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: preliminary P4 ('the zero member') of the parent's supplied proof, used there in cases (PS-ii) and (ZS-ii) to show 0 ∈ 𝓜. Simon treats the zero current as the integer multiplicity current τ(∅, θ, ξ) (Ch. 6, 3.1).
Notation: Hⁿ := μHE[n] on ℝ^P = Euclid P.
1. (The triple.) Let R_∅ have carrier ∅, multiplicity θ :≡ 0 and orientation ξ :≡ 0 (the zero n-vector). We check the fields of IMRep univ n.
 (a) ∅ is a Borel set (MeasurableSet.empty) and ∅ ⊆ univ.
 (b) ∅ is countably n-rectifiable: Hⁿ(∅) = 0 (measure_empty), and every Hⁿ-null set is countably n-rectifiable (Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero: the null set itself is the exceptional set M₀ of Definition 1.1).
 (c) θ is constant, hence measurable. The positivity condition 'θ(x) > 0 for x ∈ ∅' is vacuous.
 (d) For every compact K ⊆ univ, ∅ ∩ K = ∅ and Hⁿ⌞∅ = 0 (Measure.restrict_empty), so ∫⁻_{∅∩K} θ dHⁿ = ∫⁻ θ d0 = 0 ≠ ∞ (lintegral_zero_measure).
 (e) ξ is constant, hence a.e.-strongly measurable for Hⁿ⌞∅ (aestronglyMeasurable_const).
 (f) The orientation condition is required only Hⁿ⌞∅-almost everywhere. Since Hⁿ⌞∅ = 0, its almost-everywhere filter is ⊥ (ae_zero), so every property, in particular this one, holds a.e.
 Hence R_∅ is an IMRep in univ.
2. (R_∅ represents 0.) Let ω ∈ 𝒟ⁿ(ℝ^P) be a test form. By definition R_∅.action ω = ∫_{x∈∅} θ(x)·ξ(x)(ω(x)) dHⁿ = ∫ … d(Hⁿ⌞∅) = ∫ … d0 = 0 (Measure.restrict_empty, integral_zero_measure). The zero current satisfies 0(ω) = 0 (GeometricCurrentOn.zero_apply). Hence 0(ω) = R_∅.action ω for every ω, i.e. R_∅.Represents 0.
3. (Zero weight.) R_∅.measure = (Hⁿ⌞∅).withDensity θ = (0 : Measure).withDensity θ. For every Borel set s, withDensity_apply gives (0).withDensity θ (s) = ∫⁻_s θ d0 = 0 = 0(s). Two measures that agree on all Borel sets are equal (Measure.ext), so R_∅.measure = 0.
Steps 1–3 show that R := R_∅ has the required properties. ∎

## Key steps

1. Take carrier ∅, multiplicity 0 and orientation 0; every IMRep field holds because Hⁿ⌞∅ = 0 (rectifiability by countablyRectifiable_of_measure_zero, a.e. conditions by ae_zero).
2. Its action is an integral against the zero measure, so it equals 0 = 0(ω); hence it represents the zero current of ℝ^P.
3. Its weight is a density against the zero measure, so R.measure = 0 (Measure.ext with withDensity_apply).

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; sha256sum GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean <snapshot>/project/GMT/Ch07/Contract.lean <snapshot>/project/GMT/Ch07/Submission.lean`
- `python3 -I scans of dag.json: selected node record; siblings' statuses and decomposition-v1.json decisions; ancestors' depends_on Lean names and statuses; lean_statement patterns 'Represents (0', 'measure = 0', 'exp (Λ', 'Γ * ρ ^ n' (hits included idtp_fons_cc_tm_zero_cycle, idod_local_uniform_ball_mass_bound, dimred_mbl_bh_moving_blowUp_mass_bound); the cone_class-a1.tangent_measures-a1 subtree (blowup_integrals, zero_cycle, density_homogeneous, support_blowup)`
- `grep -n '^def\|^structure\|^abbrev' GMT/Ch07/Contract.lean; sed -n 1,200p GMT/Ch07/Contract.lean (IMRep, IMRep.measure, Represents, ConvergesWeakly, MassMeasuresConverge, dilation, blowUp)`
- `grep -n 'massOn_mono\|GeometricCurrentOn.ext\|instance.*Zero\|def massOn' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/*.lean; sed -n 1,120p Chapter06/Mass.lean; sed -n 140,165p and 300,330p Chapter06/Currents.lean; sed -n 1,80p Chapter03/Rectifiable.lean`
- `rg -n -e 'theorem restrict_apply_le |theorem withDensity_apply |theorem restrict_restrict |theorem integral_zero_measure|theorem tendsto_add_atTop_nat|theorem ne_top_of_le_ne_top|theorem ae_zero|theorem aestronglyMeasurable_const|theorem restrict_empty|theorem lintegral_zero_measure|theorem map_apply |theorem smul_apply |theorem StrictMono.id_le' <snapshot>/mathlib/Mathlib; rg -n for one_le_exp, le_of_tendsto', Filter.Tendsto.mul, Filter.Tendsto.const_mul, isCompact_closedBall, Filter.Tendsto.smul_const in the relevant snapshot directories`
- `rg -n dimred_tr_bc_ct_ GMT <snapshot>/project (no match); git log --all --oneline -S dimred_tr_bc_ct_ (exit 0, no commit); dag.json lean_name scan for the four new names (no collision)`
- `git show 926c111dd53ee0c9413099cd843d15fd58a6cc4d:GMT/Ch07/Submission.lean | grep -n '^theorem'; python3 comparison of the blowup_integrals node's parent-child-handoff.json and parent-supplied-natural-proof.md with dag.json (statement, lean_statement identical)`
- `gh api repos/humanfia/math-lean-flow/contents/_recursive_lean/inherited.py?ref=feature/humanize-api-update-claude; sed -n 1850,1990p and 6810,6900p /runtime/flows/gmt-claude-b8891bf47f75/_recursive_lean/runtime.py (_solve_children reuse by accepted lean_name, _existing_lean_name_problem, _dependency_problem)`
- `lake env lean /tmp/ct-a1/lean/Types.lean; /tmp/ct-a1/scripts/runlean2.sh /tmp/ct-a1/lean/Types.lean, /tmp/ct-a1/lean/Assembly.lean, /tmp/ct-a1/lean/Children.lean (#print axioms)`
- `python3 -I /tmp/ct-a1/scripts/check_inherit.py /tmp/ct-a1/subproblems-draft.json`
- `sed -n 440,490p book/chapter-07.txt (class 𝒯 in the proof of 7.3.3)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-blowup-cla-684f4122cb/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-blowup-cla-684f4122cb/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-blowup-class-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-blowup-cla-8c251cd34c/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-blowup-cla-b6ccbff2fc/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-8dcb296910/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-8dcb296910/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Module.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Filter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/WellFounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/BoundedOrder/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Complex/Exponential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Monoid/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/MulAction.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/EuclideanDist.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/runtime/flows/gmt-claude-b8891bf47f75/_recursive_lean/runtime.py`
- `/tmp/ct-a1/mlf/inherited.py`
- `/tmp/ct-a1/lean/Types.lean`
- `/tmp/ct-a1/lean/Assembly.lean`
- `/tmp/ct-a1/lean/Children.lean`
- `/tmp/ct-a1/scripts/check_inherit.py`
- `/tmp/ct-a1/subproblems-draft.json`
- `/tmp/ct-a1-review/Assembly.lean`
- `/tmp/ct-a1-review/Children.lean`
- `/tmp/ct-a1-review/Elab.lean`

Pins and contract:
- The manifest pins project b4d606db1 and Mathlib 25730c7c, matching the workspace HEAD and .lake/packages/mathlib. SimonGMT is at 2b366308.
- The snapshot and workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).

Reuse:
- The accepted idtp_fons_cc_tm_blowup_integrals (candidate 926c111d, comparator passed) has exactly the localization and null-ball statements that the PS and ZS integral steps need. Its dag.json lean_statement, statement, natural proof and key steps are copied unchanged.
- idtp_fons_cc_tm_zero_cycle is not usable directly: its current is existential, not 0.
- The idod_* mass bounds need density hypotheses, so P8 stays a new child.

Names: no dimred_tr_bc_ct_* identifier occurs in dag.json, GMT/, the snapshot or git history.

Library facts the children cite:
- SimonGMT:
  - GeometricCurrentOn.massOn_mono and the massOn definition (Chapter06/Mass.lean:68, 81)
  - the Zero instance, zero_apply and GeometricCurrentOn.ext (Chapter06/Currents.lean:305–317)
  - countablyRectifiable_of_measure_zero (Chapter03/Rectifiable.lean:45)
- Snapshot Mathlib:
  - Measure.restrict_apply_le, restrict_restrict, restrict_empty (Measure/Restrict.lean:176, 205, 248)
  - withDensity_apply (WithDensity.lean:44); Measure.map_apply (Map.lean:170); Measure.smul_apply (Module.lean:120); ae_zero (Filter.lean:50)
  - integral_zero_measure (Bochner/Basic.lean:1020); lintegral_zero_measure (Lebesgue/Basic.lean:428); aestronglyMeasurable_const (AEStronglyMeasurable.lean:113)
  - tendsto_add_atTop_nat (AtTopBot/Basic.lean:331); StrictMono.id_le (WellFounded.lean:267); ne_top_of_le_ne_top (BoundedOrder/Basic.lean:206)
  - Real.one_le_exp (Complex/Exponential.lean:280); le_of_tendsto' (OrderClosed.lean:138)
  - Filter.Tendsto.mul and const_mul (Monoid/Defs.lean:78, 132); Filter.Tendsto.smul_const (MulAction.lean:111); isCompact_closedBall (EuclideanDist.lean:79)

Framework:
- inherited.py makes a child wait for any ancestor dependency whose exact Lean name its proof cites. No new child cites any of the 15 such names.
- runtime.py reuses an accepted node when the lean_name and frozen type match.

Lean checks (all with only propext, Classical.choice, Quot.sound):
- All 5 child types elaborate.
- The selected frozen type compiles from the 5 children and the 3 registered dependencies, with every hypothesis used.
- The 4 new children are fully proved.
- The independent reviewer reproduced all of this in /tmp/ct-a1-review.

Book: chapter-07.txt lines 443–486 define the class 𝒯 used in the proof of 7.3.3, which the zero-scale iteration child cites.
