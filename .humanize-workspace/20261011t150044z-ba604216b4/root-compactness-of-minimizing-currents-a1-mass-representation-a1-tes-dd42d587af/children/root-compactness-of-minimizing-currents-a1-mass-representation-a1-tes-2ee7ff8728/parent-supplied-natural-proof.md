# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.testform_extension-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.testform_extension-a1.limit_functional-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, steps 4 (Cauchy estimate) and 5 (definition of L(g) as a limit). In the parent, G = g̃, m(W) = (M_W(T)).toReal, and the parent discharges the hypothesis on m with its own prerequisite eval_mass_bound, which this child does not use. Here G is an arbitrary map and m an arbitrary function with the stated bound.
Notation: Λ := Covector (Euclid P) n; |α| := covectorEuclideanNorm α = ‖c α‖ (hypothesis); 'W ⊂⊂ U' means CompactlyContained W U, i.e. closure W is compact and closure W ⊆ U. For G : ℝ^P → Λ, a triple (W, (ω_k), (ε_k)) is approximating data for G if W is open, W ⊂⊂ U, every ω_k ∈ TestFormOn U n has tsupport ω_k ⊆ W, |ω_k(x) − G(x)| ≤ ε_k for all k and x, and ε_k → 0.
1. (Triangle inequality.) For α, β ∈ Λ, |α − β| = ‖c(α) − c(β)‖ ≤ ‖c(α)‖ + ‖c(β)‖ = |α| + |β|, because c is linear.
2. (Unions.) If W and W' are open with W ⊂⊂ U and W' ⊂⊂ U, then W ∪ W' is open. Also closure(W ∪ W') = closure W ∪ closure W' is compact (a union of two compact sets) and contained in U. So W ∪ W' ⊂⊂ U.
3. (Key estimate.) Let (W, (ω_k), (ε_k)) and (W', (ω'_l), (ε'_l)) be approximating data for the same G. Then for all k, l: |T(ω_k) − T(ω'_l)| ≤ (ε_k + ε'_l)·m(W ∪ W').
 Proof. Fix k, l and put δ := ω_k − ω'_l. TestFormOn U n is a real vector subspace, so δ ∈ TestFormOn U n, and its underlying form is x ↦ ω_k(x) − ω'_l(x). Since support δ ⊆ support ω_k ∪ support ω'_l, tsupport δ ⊆ tsupport ω_k ∪ tsupport ω'_l ⊆ W ∪ W'. For every x, δ(x) = (ω_k(x) − G(x)) − (ω'_l(x) − G(x)), so by step 1, |δ(x)| ≤ ε_k + ε'_l. By step 2, W ∪ W' is open and W ∪ W' ⊂⊂ U. The hypothesis on m, applied to W ∪ W', δ and r := ε_k + ε'_l, gives |T(δ)| ≤ (ε_k + ε'_l)·m(W ∪ W'). Finally, T(δ) = T(ω_k) − T(ω'_l) because T is linear.
4. (Convergence.) Let (W, (ω_k), (ε_k)) be approximating data for G and a_k := T(ω_k). Then (a_k) converges.
 Proof. Step 3, applied with both data equal to (W, (ω_k), (ε_k)), gives |a_k − a_l| ≤ (ε_k + ε_l)·m(W ∪ W) ≤ (|ε_k| + |ε_l|)·μ for all k, l, where μ := |m(W ∪ W)|. Let η > 0. Since ε_k → 0, there is N with |ε_k| < η/(2(μ + 1)) for all k ≥ N. Then for all k, l ≥ N, |a_k − a_l| ≤ (|ε_k| + |ε_l|)·μ ≤ μη/(μ + 1) < η, since μ ≥ 0 and μ/(μ + 1) < 1. So (a_k) is a Cauchy sequence of real numbers. Since ℝ is complete, (a_k) converges.
5. (Definition of Φ.) Let G : ℝ^P → Λ. If G admits approximating data, choose one such triple (W_G, (ω^G_k), (ε^G_k)) (axiom of choice) and set Φ(G) := lim_k T(ω^G_k). This limit exists by step 4. Otherwise set Φ(G) := 0.
6. (Every approximating sequence has limit Φ(G).) Let G, W, (ω_k) and (ε_k) satisfy the hypotheses of the conclusion. These say exactly that (W, (ω_k), (ε_k)) is approximating data for G. So the chosen triple (W_G, (ω^G_k), (ε^G_k)) exists, and T(ω^G_k) → Φ(G) by step 5. Step 3 with l = k gives 0 ≤ |T(ω_k) − T(ω^G_k)| ≤ (ε_k + ε^G_k)·m(W ∪ W_G), and the right-hand side tends to (0 + 0)·m(W ∪ W_G) = 0. Hence T(ω_k) − T(ω^G_k) → 0, and T(ω_k) = T(ω^G_k) + (T(ω_k) − T(ω^G_k)) → Φ(G) + 0 = Φ(G).
7. Hence Φ has the required property.

## Key steps

1. |·| = ‖c ·‖ satisfies the triangle inequality, and W ∪ W' ⊂⊂ U is open when W, W' are open and ⊂⊂ U.
2. For two approximating data of the same G, the hypothesis on m applied to ω_k − ω'_l on W ∪ W' gives |T(ω_k) − T(ω'_l)| ≤ (ε_k + ε'_l)·m(W ∪ W').
3. With equal data this makes (T(ω_k)) Cauchy, hence convergent in ℝ.
4. Define Φ(G) as the limit along chosen approximating data (0 if none exist).
5. The estimate with l = k shows that every approximating sequence of G has the same limit Φ(G).

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
