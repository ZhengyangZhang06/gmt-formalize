# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.testform_extension-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.testform_extension-a1.ambient_extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, steps 2 (admissible open sets), 3 (approximating sequences), 5–6 (definition and linearity), 7 (agreement with T) and 8 (local bound), carried out on ℝ^P for compactly supported continuous covector fields G (in the parent, G = g̃). The bound M_W(T).toReal is replaced by m. The parent discharges the hypothesis on m with its own prerequisite eval_mass_bound, which this child does not use.
Notation: Λ := Covector (Euclid P) n; |α| := covectorEuclideanNorm α = ‖c α‖ (hypothesis), so |α + β| ≤ |α| + |β| and |t•α| = |t|·|α| because c is linear; 'W ⊂⊂ U' means CompactlyContained W U. A map G : ℝ^P → Λ is admissible if it is continuous, has compact support and tsupport G ⊆ U. Sums and real multiples of maps ℝ^P → Λ are pointwise.
1. (Choice of Φ.) The hypotheses on c and m are exactly those of the sibling limit_functional (cmr_tfe_exists_limit_functional) for (P, n, d, c, U, T, m). It gives Φ : (ℝ^P → Λ) → ℝ with the following property (L). Let W be open with W ⊂⊂ U, let ω_k ∈ TestFormOn U n with tsupport ω_k ⊆ W, and let |ω_k(x) − G(x)| ≤ ε_k for all k and x, where ε_k → 0. Then T(ω_k) → Φ(G). Steps 4–7 prove (a)–(d) for this Φ.
2. (Topological facts.) (i) If S ⊆ U is compact, there is an open W with S ⊆ W, closure W ⊆ U and closure W compact, because ℝ^P is locally compact and regular and U is open (exists_open_between_and_isCompact_closure). Thus W ⊂⊂ U. (ii) If W₁ and W₂ are open with W₁ ⊂⊂ U and W₂ ⊂⊂ U, then W₁ ∪ W₂ is open and W₁ ∪ W₂ ⊂⊂ U: closure(W₁ ∪ W₂) = closure W₁ ∪ closure W₂ is compact and contained in U. (iii) If W ⊂⊂ U, then W ⊆ closure W ⊆ U.
3. (Approximating sequences.) Let W be open with W ⊂⊂ U, and let G be continuous with compact support and tsupport G ⊆ W. For each k, the sibling uniform_approx (cmr_tfe_uniform_testForm_approx) with V := W and ε := 1/(k+1) > 0 gives a form ω_k with IsTestForm ω_k, tsupport ω_k ⊆ W and |ω_k(x) − G(x)| ≤ 1/(k+1) for all x. By 2(iii), tsupport ω_k ⊆ U, so ω_k ∈ TestFormOn U n. Since 1/(k+1) → 0, property (L) gives T(ω_k) → Φ(G). If G is admissible, then tsupport G is compact and contained in U, so 2(i) gives an open W ⊂⊂ U with tsupport G ⊆ W, and the above applies.
4. (Additivity (a).) Let G₁ and G₂ be admissible. By step 3, for i = 1, 2 choose an open W_i ⊂⊂ U and ω^i_k ∈ TestFormOn U n with tsupport ω^i_k ⊆ W_i, |ω^i_k(x) − G_i(x)| ≤ 1/(k+1) and T(ω^i_k) → Φ(G_i). Put σ_k := ω¹_k + ω²_k ∈ TestFormOn U n. Then tsupport σ_k ⊆ tsupport ω¹_k ∪ tsupport ω²_k ⊆ W₁ ∪ W₂, and W₁ ∪ W₂ is open and ⊂⊂ U by 2(ii). For every x, σ_k(x) − (G₁ + G₂)(x) = (ω¹_k(x) − G₁(x)) + (ω²_k(x) − G₂(x)). Hence |σ_k(x) − (G₁ + G₂)(x)| ≤ 1/(k+1) + 1/(k+1), which tends to 0. By (L), T(σ_k) → Φ(G₁ + G₂). Since T is linear, T(σ_k) = T(ω¹_k) + T(ω²_k) → Φ(G₁) + Φ(G₂). Limits in ℝ are unique, so Φ(G₁ + G₂) = Φ(G₁) + Φ(G₂).
5. (Homogeneity (b).) Let G be admissible and t ∈ ℝ. Take W and ω_k as in step 3, so T(ω_k) → Φ(G). Then t•ω_k ∈ TestFormOn U n and tsupport(t•ω_k) ⊆ tsupport ω_k ⊆ W. For every x, (t•ω_k)(x) − (t•G)(x) = t•(ω_k(x) − G(x)). So |(t•ω_k)(x) − (t•G)(x)| = |t|·|ω_k(x) − G(x)| ≤ |t|·(1/(k+1)), which tends to 0. By (L), T(t•ω_k) → Φ(t•G). By linearity, T(t•ω_k) = t·T(ω_k) → t·Φ(G). By uniqueness of limits, Φ(t•G) = t·Φ(G).
6. (Agreement (c).) Let ω ∈ TestFormOn U n. Then IsTestForm ω, so ω has compact support and tsupport ω is compact; also tsupport ω ⊆ U. By 2(i), choose an open W ⊂⊂ U with tsupport ω ⊆ W. For G := ω, the constant sequence ω_k := ω with errors ε_k := 0 satisfies the hypotheses of (L), since |ω(x) − ω(x)| = |0| = 0 ≤ 0. So the constant sequence T(ω) tends to Φ(ω). It also tends to T(ω), so Φ(ω) = T(ω) by uniqueness of limits.
7. (Bound (d).) Let W be open with W ⊂⊂ U, let G be continuous with compact support and tsupport G ⊆ W, let r ∈ ℝ, and let |G(x)| ≤ r for all x. Step 3, applied to W and G, gives ω_k ∈ TestFormOn U n with tsupport ω_k ⊆ W, |ω_k(x) − G(x)| ≤ 1/(k+1) and T(ω_k) → Φ(G). For every x, ω_k(x) = (ω_k(x) − G(x)) + G(x), so |ω_k(x)| ≤ 1/(k+1) + r. The hypothesis on m, applied to W, ω_k and r + 1/(k+1), gives |T(ω_k)| ≤ (r + 1/(k+1))·m(W) for every k. As k → ∞, |T(ω_k)| → |Φ(G)| (continuity of the absolute value) and (r + 1/(k+1))·m(W) → r·m(W). Non-strict inequalities are preserved under limits, so |Φ(G)| ≤ r·m(W).
8. Steps 4–7 prove (a)–(d) for Φ.

## Key steps

1. Take Φ from limit_functional: T(ω_k) → Φ(G) along every sequence approximating G uniformly with supports in a fixed open W ⊂⊂ U.
2. Every compact S ⊆ U lies in an open W ⊂⊂ U, and unions of two such sets stay ⊂⊂ U.
3. uniform_approx with errors 1/(k+1) gives an approximating sequence for every continuous compactly supported G with tsupport G ⊆ W.
4. Sums and real multiples of approximating sequences approximate G₁ + G₂ (on W₁ ∪ W₂) and t•G, so (a) and (b) hold by linearity of T and uniqueness of limits.
5. The constant sequence ω gives Φ(ω) = T(ω).
6. |ω_k| ≤ r + 1/(k+1) and the m-bound give |T(ω_k)| ≤ (r + 1/(k+1))·m(W), hence |Φ(G)| ≤ r·m(W) in the limit.

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
