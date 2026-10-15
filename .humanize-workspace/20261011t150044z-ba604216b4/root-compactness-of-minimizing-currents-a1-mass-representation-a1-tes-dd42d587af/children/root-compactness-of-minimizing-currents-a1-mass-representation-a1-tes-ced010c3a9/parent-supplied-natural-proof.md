# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.testform_extension-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.testform_extension-a1.uniform_approx-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 3, first bullet (approximating sequences): the rescaling argument around the sibling mollify_unit_field, stated for an arbitrary open set V and a single error ε > 0.
Notation: Λ := Covector (Euclid P) n; |α| := covectorEuclideanNorm α = ‖c α‖ (hypothesis). For a map F : ℝ^P → Λ and t ∈ ℝ, t•F is the pointwise multiple x ↦ t•F(x).
1. (Homogeneity.) For t ∈ ℝ and α ∈ Λ, |t•α| = ‖c(t•α)‖ = ‖t•c(α)‖ = |t|·‖c(α)‖ = |t|·|α|, because c is linear.
2. (Bound for G.) The map c∘G : ℝ^P → ℝ^d is continuous. Since c(0) = 0, support(c∘G) ⊆ support G, so c∘G has compact support (HasCompactSupport.comp_left). A continuous compactly supported map into a normed space is bounded (HasCompactSupport.exists_bound_of_continuous): there is C ∈ ℝ with ‖c(G(x))‖ ≤ C for all x. Put s := max(C, 0) + 1. Then s ≥ 1 > 0 and |G(x)| = ‖c(G(x))‖ ≤ C ≤ max(C, 0) ≤ s for every x.
3. (Normalized field.) Let g := s⁻¹•G, i.e. g(x) = s⁻¹•G(x). Then g is continuous. Since support g ⊆ support G, g has compact support and tsupport g ⊆ tsupport G ⊆ V. By steps 1–2, |g(x)| = s⁻¹·|G(x)| ≤ s⁻¹·s = 1 for every x.
4. (Mollification.) Apply the sibling mollify_unit_field (dor_ims_sua_mollify_unit_field) to V, g and the positive number ε/s; its hypotheses are verified in step 3. It gives an n-form ω₀ with IsTestForm ω₀, tsupport ω₀ ⊆ V, |ω₀(x)| ≤ 1 and |ω₀(x) − g(x)| ≤ ε/s for every x.
5. (Rescaling.) Put ω := s•ω₀. Test forms form a real vector subspace of the n-forms (testFormSubmodule), so IsTestForm ω. Since support ω ⊆ support ω₀, tsupport ω ⊆ tsupport ω₀ ⊆ V.
6. (Error.) For every x, ω(x) − G(x) = s•ω₀(x) − s•(s⁻¹•G(x)) = s•(ω₀(x) − g(x)), using s·s⁻¹ = 1 and linearity. By steps 1 and 4, |ω(x) − G(x)| = s·|ω₀(x) − g(x)| ≤ s·(ε/s) = ε.
7. By steps 5 and 6, ω satisfies IsTestForm ω, tsupport ω ⊆ V and covectorEuclideanNorm (ω(x) − G(x)) ≤ ε for all x ∈ ℝ^P.

## Key steps

1. |t•α| = |t|·|α| because |·| = ‖c ·‖; c∘G is continuous with compact support, hence |G| ≤ s := max(C, 0) + 1.
2. g := s⁻¹•G is continuous, compactly supported, tsupport g ⊆ V and |g| ≤ 1.
3. mollify_unit_field applied to g with error ε/s gives a test form ω₀ with tsupport ω₀ ⊆ V and |ω₀ − g| ≤ ε/s.
4. ω := s•ω₀ is a test form with tsupport ω ⊆ V and |ω − G| = s·|ω₀ − g| ≤ ε.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean GMT/Ch07/Submission.lean (both identical); cat local-references/123e8435b4a2469b/manifest.json`
- `rg -n 'cmr_tfe|uniform_testForm_approx|exists_limit_functional|ambient_extension' local-references/123e8435b4a2469b/project -g '*.lean' (no match)`
- `rg -n 'massAdmissibleOn|le_massOn|cmr_abs_apply_le_massOn|dor_ims_sua_mollify_unit_field' local-references/123e8435b4a2469b/project -g '*.lean' (no match; SimonGMT sources are read from .lake/packages/simongmt)`
- `rg -n 'theorem exists_open_between_and_isCompact_closure|theorem continuous_extend_one|theorem mulTSupport_extend_one_subset|theorem extend_one|theorem tendsto_nhds_limUnder|theorem cauchySeq_iff_tendsto_dist_atTop_0|theorem cauchySeq_tendsto_of_complete|theorem tendsto_one_div_add_atTop_nhds_zero_nat|theorem tsupport_smul_subset_right|theorem prod_atTop_atTop_eq' local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean'`
- `rg -n 'theorem mulTSupport_div|theorem mulTSupport_mul|exists_bound_of_continuous|le_of_tendsto_of_tendsto' local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean .../Analysis/Normed/Group/Bounded.lean .../Topology/Order/OrderClosed.lean`
- `python3 -I scan of dag.json nodes (lean_name, lean_statement, status, candidate_commit) for cmr_*, *approx*, *extension*; read nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1/decomposition-v1.json (mollify_unit_field reuse text)`
- `grep/sed of /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py (_solve_children, _existing_lean_name_problem, _overlay_accepted_children, _node_worktree) and leaf_verification.py (check_source_delta); python3 -I contract_scope from verifier/gmt-compare.py on GMT/Ch07/Contract.lean`
- `lake env lean /tmp/tfe-split/{Avail,Names,LinTest,Stmts,Parent,ChildA,ChildB,ChildC,E2E,E2E2}.lean; git show 8abce3204fc05f00ae9a4047981f27a9f9a6ba3b:GMT/Ch07/Submission.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Separation/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UniformSpace/Cauchy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-tes-dd42d587af/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-tes-dd42d587af/parent-supplied-natural-proof.md`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/tfe-split/Stmts.lean`
- `/tmp/tfe-split/Parent.lean`
- `/tmp/tfe-split/ChildA.lean`
- `/tmp/tfe-split/ChildB.lean`
- `/tmp/tfe-split/ChildC.lean`
- `/tmp/tfe-split/E2E2.lean`

The snapshot (project b4d606db, Mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean.

The project snapshot has no cmr_tfe declaration (rg: no match). It also contains no SimonGMT or DAG candidate sources; those are read from .lake/packages/simongmt and from candidate commits.

Every Mathlib fact the split needs exists in the pinned snapshot and is in scope after import GMT.Ch07.Submission (#check):
- exists_open_between_and_isCompact_closure (Topology/Separation/Regular.lean:364);
- HasCompactSupport.continuous_extend_zero, extend_zero and tsupport_extend_zero_subset, as to_additive forms of Topology/Algebra/Support.lean:321-341;
- tsupport_add and tsupport_sub (Support.lean:139-164), and tsupport_smul_subset_right (:172);
- HasCompactSupport.exists_bound_of_continuous (Analysis/Normed/Group/Bounded.lean:98);
- tendsto_nhds_limUnder (Topology/Basic.lean:245) and cauchySeq_tendsto_of_complete (Topology/UniformSpace/Cauchy.lean:425);
- cauchySeq_iff_tendsto_dist_atTop_0 (Topology/MetricSpace/Pseudo/Basic.lean:201) and prod_atTop_atTop_eq (Order/Filter/AtTopBot/Prod.lean:25);
- tendsto_one_div_add_atTop_nhds_zero_nat (Analysis/SpecificLimits/Basic.lean:70) and le_of_tendsto_of_tendsto' (Topology/Order/OrderClosed.lean:480).

From SimonGMT: testFormOnSubmodule and GeometricCurrentOn (Chapter06/Currents.lean); massAdmissibleOn, le_massOn and covectorEuclideanNorm_zero/neg (Chapter06/Mass.lean).

Reuse: dor_ims_sua_mollify_unit_field is accepted with an identical frozen type, and its proof from 8abce32 compiles in the end-to-end check. cmr_abs_apply_le_massOn cannot be reused as a child (it is unaccepted and owned by another parent), so it stays a dependency of the selected node only.

Lean: every child type elaborates in the comparator scope. Full proofs exist for all three new children, using standard axioms only, and the parent assembly compiles from the frozen child types plus eval_mass_bound.
