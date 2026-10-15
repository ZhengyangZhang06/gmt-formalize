# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.foundations-a1.testform_extension-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.foundations-a1.testform_extension-a1.limit_functional-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: selected proof, steps 4 (Cauchy estimate) and 5 (definition of L(g) as a limit). In the selected proof G = g̃ and m(W) = (M_W(T)).toReal. The selected node itself discharges the hypothesis on m with its prerequisite eval_mass_bound (cmr_abs_apply_le_massOn), which this child does not use. Here G is an arbitrary map ℝ^P → Λ and m an arbitrary function with the stated bound.
Notation: Λ := Covector (Euclid P) n; |α| := covectorEuclideanNorm α = ‖c α‖ (hypothesis); 'W ⊂⊂ U' means CompactlyContained W U, i.e. closure W is compact and closure W ⊆ U. Elements of TestFormOn U n are identified with their underlying forms; TestFormOn U n is a real vector subspace of the n-forms, and T (through T.toCurrent) is linear on it. For G : ℝ^P → Λ, a triple D = (W, (ω_k), (ε_k)), with W ⊆ ℝ^P, ω_k ∈ TestFormOn U n and ε_k ∈ ℝ, is approximating data for G if: W is open; W ⊂⊂ U; tsupport ω_k ⊆ W for every k; |ω_k(x) − G(x)| ≤ ε_k for all k and x; and ε_k → 0.
1. (Triangle inequality.) For α, β ∈ Λ, |α − β| = ‖c(α) − c(β)‖ ≤ ‖c(α)‖ + ‖c(β)‖ = |α| + |β|, because c is linear.
2. (Unions.) Let W and W' be open with W ⊂⊂ U and W' ⊂⊂ U. Then W ∪ W' is open. Also closure(W ∪ W') = closure W ∪ closure W' is compact (a union of two compact sets) and contained in U. So W ∪ W' ⊂⊂ U.
3. (Key estimate.) Let D = (W, (ω_k), (ε_k)) and D' = (W', (ω'_l), (ε'_l)) be approximating data for the same G. Then for all k, l: |T(ω_k) − T(ω'_l)| ≤ (ε_k + ε'_l)·m(W ∪ W').
 Proof. Fix k, l and put δ := ω_k − ω'_l ∈ TestFormOn U n; as a form, δ(x) = ω_k(x) − ω'_l(x).
 - Support. If x ∉ support ω_k ∪ support ω'_l, then δ(x) = 0 − 0 = 0. So support δ ⊆ support ω_k ∪ support ω'_l. Taking closures, tsupport δ ⊆ closure(support ω_k ∪ support ω'_l) = tsupport ω_k ∪ tsupport ω'_l ⊆ W ∪ W'.
 - Size. For every x, δ(x) = (ω_k(x) − G(x)) − (ω'_l(x) − G(x)). By step 1, |δ(x)| ≤ |ω_k(x) − G(x)| + |ω'_l(x) − G(x)| ≤ ε_k + ε'_l.
 - Bound. By step 2, W ∪ W' is open and W ∪ W' ⊂⊂ U. The hypothesis on m, applied to W ∪ W', δ and r := ε_k + ε'_l, gives |T(δ)| ≤ (ε_k + ε'_l)·m(W ∪ W').
 Finally, T(δ) = T(ω_k) − T(ω'_l) because T is linear.
4. (Convergence.) Let D = (W, (ω_k), (ε_k)) be approximating data for G and put a_k := T(ω_k). Then (a_k) converges in ℝ.
 Proof. Put μ := |m(W ∪ W)| ≥ 0. Let η > 0 and θ := η/(2(μ + 1)) > 0. Since ε_k → 0, also |ε_k| → 0, so there is N with |ε_k| < θ for all k ≥ N. Let k ≥ N. Step 3, with D' := D and l := N, gives
 |a_k − a_N| ≤ (ε_k + ε_N)·m(W ∪ W) ≤ |(ε_k + ε_N)·m(W ∪ W)| = |ε_k + ε_N|·μ ≤ (|ε_k| + |ε_N|)·μ ≤ 2θ·μ = η·μ/(μ + 1) < η.
 Here |ε_k| + |ε_N| < 2θ, μ ≥ 0, and the last inequality holds because η > 0 and μ < μ + 1. So for every η > 0 there is N with dist(a_k, a_N) < η for all k ≥ N; that is, (a_k) is a Cauchy sequence (Metric.cauchySeq_iff'). Since ℝ is complete, (a_k) converges (cauchySeq_tendsto_of_complete).
5. (Definition of Φ.) Let G : ℝ^P → Λ. If G admits approximating data, choose one such triple D_G = (W_G, (ω^G_k), (ε^G_k)) (axiom of choice). By step 4 the sequence (T(ω^G_k))_k converges; let Φ(G) be (a chosen) limit of it. Otherwise set Φ(G) := 0. Then T(ω^G_k) → Φ(G) whenever D_G is defined.
6. (Every approximating sequence tends to Φ(G).) Let G, W, (ω_k) and (ε_k) satisfy the hypotheses of the conclusion: W is open, W ⊂⊂ U, tsupport ω_k ⊆ W for every k, |ω_k(x) − G(x)| ≤ ε_k for all k and x, and ε_k → 0. These say exactly that D := (W, (ω_k), (ε_k)) is approximating data for G. So D_G exists, and T(ω^G_k) → Φ(G) by step 5. Step 3, applied to D and D_G with l = k, gives 0 ≤ |T(ω_k) − T(ω^G_k)| ≤ (ε_k + ε^G_k)·m(W ∪ W_G) for every k. The right-hand side tends to (0 + 0)·m(W ∪ W_G) = 0. By the squeeze principle, T(ω_k) − T(ω^G_k) → 0. Hence T(ω_k) = (T(ω_k) − T(ω^G_k)) + T(ω^G_k) → 0 + Φ(G) = Φ(G).
7. So Φ has the required property.

## Key steps

1. |·| = ‖c ·‖ satisfies the triangle inequality, and W ∪ W' is open and ⊂⊂ U when W, W' are open and ⊂⊂ U.
2. For two approximating data of the same G, the m-hypothesis applied to ω_k − ω'_l on W ∪ W' with r = ε_k + ε'_l gives |T(ω_k) − T(ω'_l)| ≤ (ε_k + ε'_l)·m(W ∪ W').
3. With equal data this makes (T(ω_k)) Cauchy, hence convergent in ℝ.
4. Define Φ(G) as the limit along chosen approximating data (0 if none exists).
5. The estimate with l = k squeezes T(ω_k) − T(ω^G_k) to 0, so every approximating sequence of G has limit Φ(G).

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json (project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git log -1 --format=%H in <snapshot>/project and <snapshot>/mathlib (same commits)`
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean and <snapshot>/project/GMT/Ch07/Submission.lean against workspace GMT/Ch07/Contract.lean and GMT/Ch07/Submission.lean (identical)`
- `rg -n 'dimred_mbl_fnd_tfe|cmr_tfe|dor_ims_sua_mollify_unit_field|cmr_abs_apply_le_massOn|testForm_extension' <snapshot>/project -g '*.lean' (no match, rc=1)`
- `rg -n 'theorem continuous_extend_one|theorem mulTSupport_extend_one_subset|theorem extend_one : HasCompactMulSupport' <snapshot>/mathlib/Mathlib/Topology/Algebra/Support.lean (lines 341, 321, 327)`
- `rg -n 'theorem exists_open_between_and_isCompact_closure' <snapshot>/mathlib/Mathlib/Topology/Separation/Regular.lean (line 364)`
- `rg -n 'theorem cauchySeq_tendsto_of_complete' <snapshot>/mathlib/Mathlib/Topology/UniformSpace/Cauchy.lean (line 425)`
- `grep -n 'exists_bound_of_continuous' <snapshot>/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean (line 98, HasCompactMulSupport.exists_bound_of_continuous and its additive form)`
- `grep -n 'tendsto_one_div_add_atTop_nhds_zero_nat' <snapshot>/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean (line 70); grep -n 'tsupport_smul_subset_right|image_eq_one_of_notMem_mulTSupport' <snapshot>/mathlib/Mathlib/Topology/Algebra/Support.lean (lines 172, 111); grep -rn 'squeeze_zero_norm' <snapshot>/mathlib/Mathlib/Analysis/Normed/Group/Continuity.lean`
- `git show 8abce3204fc05f00ae9a4047981f27a9f9a6ba3b:GMT/Ch07/Submission.lean and git show 7a706164baaf42fc7f55751247396a8836928310:GMT/Ch07/Submission.lean (accepted proofs of dor_ims_sua_coeff_norm_rep, dor_ims_sua_mollify_unit_field, cmr_abs_apply_le_massOn)`
- `python3 scans of dag.json: selected node; identical-type node cmr_testForm_extension_functional with its decomposition-v1/audit-v1; statuses, candidate commits and closures of dor_ims_sua_mollify_unit_field and cmr_abs_apply_le_massOn; lean_name collisions for dimred_mbl_fnd_tfe_* (none)`
- `lean_contract.validate_lean_statement on all child and parent types (pass); read runtime.py _existing_lean_name_problem/_solve_children/_overlay_accepted_children and leaf_verification.check_source_delta`
- `lake env lean /tmp/dmf-tfe-split/Types.lean, Parent.lean, ChildUA.lean, ChildLF.lean, ChildAE.lean, E2E.lean, Thick.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Separation/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UniformSpace/Cauchy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-foundations-a1-ff007b1424/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-tes-dd42d587af/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-tes-dd42d587af/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-smooth-b62f226305/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/dmf-tfe-split/E2E.lean`

The snapshot pins match: project b4d606db and mathlib 25730c7c. The snapshot Contract.lean and Submission.lean are byte-identical to the workspace's. The snapshot project contains no dimred_mbl_fnd_tfe_*, cmr_tfe_*, testForm_extension or reused declaration. So no snapshot declaration is reused, and the fresh names collide with nothing. Snapshot Mathlib supplies every library fact the children and the parent assembly use, and all of them resolve after import GMT.Ch07.Submission (Lean compile): HasCompactSupport.continuous_extend_zero, extend_zero and tsupport_extend_zero_subset (to_additive of Support.lean:341/327/321); exists_open_between_and_isCompact_closure (Regular.lean:364); cauchySeq_tendsto_of_complete (Cauchy.lean:425); HasCompactSupport.exists_bound_of_continuous (Bounded.lean:98); tendsto_one_div_add_atTop_nhds_zero_nat; tsupport_smul_subset_right; squeeze_zero_norm. SimonGMT supplies TestFormOn as a Submodule, the linear GeometricCurrentOn, covectorEuclideanNorm and le_massOn. The reused dor_ims_sua_mollify_unit_field is accepted (candidate 8abce32, closure accepted) with an identical type. The parent's own prerequisite cmr_abs_apply_le_massOn is accepted (7a70616). All child types elaborate in the replayed comparator scope. The complete chain, with the real accepted proofs, compiles sorry-free with axioms propext, Classical.choice and Quot.sound.
