# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_dense-a1.integer_combination-a1.tangent_locality-a1`
- Child DAG node: `root.regular_set_dense-a1.integer_combination-a1.tangent_locality-a1.excess_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent proof. Notation: μ := μHE[n]; B̄_r(z) is the closed ball; all quantities lie in [0, ∞] with u/v := u·v⁻¹. For ρ ∈ ℝ put a(ρ) := μ(B ∩ B̄_ρ(x)), b(ρ) := μ(A ∩ B̄_ρ(x)), e(ρ) := μ((B ∖ A) ∩ B̄_ρ(x)). Let c := ENNReal.ofReal(C) ∈ [0, ∞) and K := 2c ∈ [0, ∞).

1. Small radii. Since min(r₀, r₁) > 0, the interval (0, min(r₀, r₁)) belongs to 𝓝[>]0; so eventually 0 < ρ < r₁ and ρ ≤ r₀. For such ρ, monotonicity gives a(ρ) ≤ μ(B ∩ B̄_{r₀}(x)) < ∞.

2. Subadditivity. For every ρ, B ∩ B̄_ρ(x) ⊆ (A ∩ B̄_ρ(x)) ∪ ((B ∖ A) ∩ B̄_ρ(x)) (a point of B lies in A or in B ∖ A), so by monotonicity and subadditivity of the outer measure μ, a(ρ) ≤ b(ρ) + e(ρ). No measurability is needed.

3. Growth of a. Apply the relative-excess hypothesis with ε := 1/2 (> 0): eventually e(ρ) ≤ a(ρ)/2. Let ρ satisfy this and step 1. Then a(ρ) ≤ b(ρ) + e(ρ) ≤ b(ρ) + a(ρ)/2. Writing a(ρ) = a(ρ)/2 + a(ρ)/2 and cancelling the finite summand a(ρ)/2 (a(ρ) < ∞) gives a(ρ)/2 ≤ b(ρ). Hence, using the growth hypothesis (0 < ρ < r₁),
   a(ρ) = a(ρ)/2 + a(ρ)/2 ≤ 2·b(ρ) ≤ 2·ENNReal.ofReal(C·ρⁿ) = 2c·ENNReal.ofReal(ρ)ⁿ = K·ENNReal.ofReal(ρ)ⁿ,
where ENNReal.ofReal(C·ρⁿ) = ENNReal.ofReal(C)·ENNReal.ofReal(ρⁿ) because ρⁿ ≥ 0, and ENNReal.ofReal(ρⁿ) = ENNReal.ofReal(ρ)ⁿ because ρ ≥ 0. Thus eventually a(ρ) ≤ K·ENNReal.ofReal(ρ)ⁿ. (If C ≤ 0, then c = K = 0 and this says a(ρ) = 0 eventually; nothing below changes.)

4. Conclusion. A function u with values in [0, ∞] tends to 0 along 𝓝[>]0 if and only if for every δ > 0, eventually u(ρ) ≤ δ (Mathlib ENNReal.tendsto_nhds_zero). Let δ > 0. If δ = ∞ there is nothing to prove. Let δ < ∞ and put ε := δ/(K + 1). As δ ≠ 0 and K + 1 < ∞, ε > 0. As K + 1 ∈ (0, ∞), ε·(K + 1) = δ, hence ε·K ≤ ε·(K + 1) = δ. By the relative-excess hypothesis for this ε and by step 3, eventually
   e(ρ) ≤ ε·a(ρ) ≤ ε·K·ENNReal.ofReal(ρ)ⁿ ≤ δ·ENNReal.ofReal(ρ)ⁿ,
and therefore e(ρ)/ENNReal.ofReal(ρ)ⁿ ≤ δ (in [0, ∞], u ≤ δ·v implies u/v ≤ δ). Hence e(ρ)/ENNReal.ofReal(ρ)ⁿ → 0 as ρ → 0 in 𝓝[>]0. For n = 0, ENNReal.ofReal(ρ)⁰ = 1 and the argument is unchanged; P = 0 needs no change either. ∎

## Key steps

1. Eventually 0 < ρ < r₁ and ρ ≤ r₀, so μ(B ∩ B̄_ρ(x)) < ∞.
2. Subadditivity: μ(B ∩ B̄_ρ) ≤ μ(A ∩ B̄_ρ) + μ((B ∖ A) ∩ B̄_ρ).
3. With ε = 1/2 and cancellation of the finite half: μ(B ∩ B̄_ρ) ≤ 2μ(A ∩ B̄_ρ) ≤ 2·ofReal(C)·ofReal(ρ)ⁿ.
4. For δ ∈ (0, ∞), ε := δ/(2·ofReal(C) + 1) gives μ((B ∖ A) ∩ B̄_ρ) ≤ δ·ofReal(ρ)ⁿ eventually, so the quotient tends to 0.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `grep -n -E 'blowUpMap|HasApproximateTangentSpaceAt|^theorem|^def' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n 'theorem ae_tendsto_measure_inter_div ' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean; grep -n 'instHasBesicovitchCovering' mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `grep -n 'theorem Isometry.euclideanHausdorffMeasure_image|theorem MeasureTheory.euclideanHausdorffMeasure_homothety_image' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `grep -n 'theorem setIntegral_union |theorem norm_setIntegral_le_of_norm_le_const |theorem setIntegral_eq_of_subset_of_forall_sdiff_eq_zero' mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `grep -rn "theorem ae_ball_iff|theorem ae_restrict_iff' |theorem restrict_restrict |theorem restrict_apply' |theorem measure_sdiff " mathlib/Mathlib/MeasureTheory/Measure mathlib/Mathlib/MeasureTheory/OuterMeasure`
- `grep -n 'protected theorem tendsto_nhds_zero|protected theorem Tendsto.const_mul' mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `grep -c rsdic_tl_ dag.json issue-workers.json; grep -rl rsdic_tl_ nodes GMT local-references/123e8435b4a2469b; git log --all --oneline -S rsdic_tl_; git ls-remote origin | grep integer-combination-a1-tangent-locality`
- `python3 listing of dag.json nodes tangent_locality-a1, tangent_growth-a1 and regular_components_are_minimizing-a1.approx_tangent_locality-a1 subtree (status, lean_name, lean_statement, children)`
- `diff Contract.lean Submission.lean in .swarm-worktrees/0dab999dcad4a9dc99a8 (rsdic_measure_closedBall_le_of_tangent) and .swarm-worktrees/b405db921480df316392 (regcomp_atl_blowUp_measure_scaling)`
- `grep -n '_existing_lean_name_problem|node bound|An accepted theorem may be reused' /runtime/flows/gmt-claude-8a1588a65b86/_recursive_lean/runtime.py`
- `sed -n 80,96p chapter-03.txt; sed -n 296,306p chapter-03.txt; sed -n 903,926p chapter-01.txt`
- `python3 -I /tmp/rsdic-tl-v3-scripts/gen_challenges.py children.json /tmp/rsdic-tl-v3/cmp (gmt-compare.py child_modules/contract_scope + lean_contract.validate_lean_statement)`
- `lake env lean /tmp/rsdic-tl-v3/Assembly.lean`
- `lake env lean /tmp/rsdic-tl-v3/All.lean`
- `lake env lean /tmp/rsdic-tl-v3/CmpAll.lean; lake env lean /tmp/rsdic-tl-v3/cmp/{ae_excess,excess_density,blowup_scaling,pointwise_comparison}_Challenge.lean`
- `lake env lean /tmp/rsdic-tl-v3/Inst.lean (set_option pp.explicit true instance check)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-integer-combination-a1-tangent-locality-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-integer-combination-a1-tangent-locality-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-integer-combination-a1-tangent-locality-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-integer-combination-a1-tangent-locality-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/.swarm-worktrees/0dab999dcad4a9dc99a8/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/.swarm-worktrees/b405db921480df316392/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-8a1588a65b86/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-8a1588a65b86/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/rsdic-tl-v3/Assembly.lean`
- `/tmp/rsdic-tl-v3/All.lean`
- `/tmp/rsdic-tl-v3/CmpAll.lean`
- `/tmp/rsdic-tl-v3/cmp/ae_excess_Challenge.lean`
- `/tmp/rsdic-tl-v3/cmp/excess_density_Challenge.lean`
- `/tmp/rsdic-tl-v3/cmp/blowup_scaling_Challenge.lean`
- `/tmp/rsdic-tl-v3/cmp/pointwise_comparison_Challenge.lean`
- `/tmp/rsdic-tl-v3/Inst.lean`
- `/tmp/rsdic-tl-review-jOkZ/MyAssembly.lean`
- `/tmp/rsdic-tl-review-jOkZ/CmpMine.lean`

**Snapshot.** The snapshot (project b4d606d, Mathlib 25730c7c) Ch07 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

**No reusable locality theorem.** None exists in the snapshot, GMT or SimonGMT. The only declarations with the same type are DAG nodes of the regcomp branch:
- accepted: `regcomp_atl_blowUp_measure_scaling`;
- still decomposing: `regcomp_atl_tangent_iff_of_density_zero` and `regcomp_approx_tangent_locality`.

**Reusable library facts found.**
- SimonGMT: `HasApproximateTangentSpaceAt` and `blowUpMap` (Def. 1.4 with Bochner set integrals along 𝓝[>]0).
- Mathlib:
  - `Besicovitch.ae_tendsto_measure_inter_div`, with `instHasBesicovitchCovering` for finite-dimensional spaces;
  - `Isometry.euclideanHausdorffMeasure_image`, `euclideanHausdorffMeasure_homothety_image`;
  - `setIntegral_union`, `setIntegral_eq_of_subset_of_forall_sdiff_eq_zero`, `norm_setIntegral_le_of_norm_le_const`;
  - `ae_ball_iff`, `ae_restrict_iff'`, `Measure.restrict_restrict`, `Measure.restrict_apply'`, `measure_sdiff`;
  - `ENNReal.tendsto_nhds_zero`, `ENNReal.Tendsto.const_mul`.

**Runtime rules (runtime.py).** Reusing an accepted cross-branch name with an identical type is allowed. A node still active under another parent requires a fresh name. Decompositions that exceed `max_nodes` are refused; the bound is now 1000 and the DAG has 230 nodes.

**Names.** `rsdic_tl_*` is unused everywhere except this node's own unpublished drafts.

**Lean checks.**
- The four child types elaborate in the comparator's replayed scope, with the intended instances.
- All four have sorry-free proofs using only propext, Classical.choice and Quot.sound.
- The exact frozen parent type follows from them plus tangent_growth: only sorryAx from stubs; axiom-clean with the accepted tangent_growth proof.
- An independent reviewer reproduced the assembly and accepted.
