# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_estimates-a1`
- Child DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_estimates-a1.cutoff_radial_form-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 0 of the parent proof (ζ_{r,s}ψ_ω is a test form satisfying the radial formula on B_r(0)) and the pointwise part of Step 6 (|ζψ_ω(x)| ≤ c·s), with the smooth radial form ψ_ω supplied as the input ψ₀.
Notation: |α| := covectorEuclideanNorm α; B_ρ(0), B̄_ρ(0) are the open and closed balls; D^m(ℝ^P) := TestFormOn univ m, whose elements are the m-forms f : ℝ^P → Λ_m(ℝ^P) that are C^∞ (ContDiff ℝ ∞), have compact support, and satisfy tsupport f ⊆ univ.
1. (Bump function.) Since 0 < r < s and Eucl P is a finite-dimensional inner product space (so it carries smooth bump functions), there is a ContDiffBump ζ centred at 0 with rIn = r and rOut = s. Its coercion ζ : ℝ^P → ℝ is C^∞ (ContDiffBump.contDiff), satisfies 0 ≤ ζ ≤ 1 (nonneg, le_one), ζ(x) = 1 for x ∈ B̄_r(0) (one_of_mem_closedBall), support ζ = B_s(0) (support_eq), and has compact support (hasCompactSupport).
2. (The test form.) Define f(x) := ζ(x)·ψ₀(x) ∈ Λ_m(ℝ^P). f is C^∞ as the product of the C^∞ scalar function ζ and the C^∞ form ψ₀ (ContDiff.smul), it has compact support because ζ has (HasCompactSupport.smul_right), and tsupport f ⊆ univ trivially. Hence f ∈ D^m(ℝ^P); let ψ be f regarded as an element of TestFormOn univ m.
3. (Property (i).) Let x ∈ B_r(0) and v ∈ (ℝ^P)^m. Then x ∈ B̄_r(0), so ζ(x) = 1 and ψ(x)(v) = ψ₀(x)(v) = ∫_0^1 t^m ω(tx)(x, v) dt by the hypothesis on ψ₀.
4. (Homogeneity.) For a ∈ ℝ and α ∈ Λ_m(ℝ^P): (aα)(e_I) = a·α(e_I) for every coordinate tuple e_I, so the sum of squares S' defining |aα|² equals a² times the sum S defining |α|², and |aα| = sqrt(a²·S) = |a|·sqrt(S) = |a|·|α| (Real.sqrt_mul, Real.sqrt_sq_eq_abs).
5. (Property (ii).) Assume |ω(y)| ≤ 1 for all y and let x ∈ ℝ^P. By Step 4, |ψ(x)| = |ζ(x)|·|ψ₀(x)|.
 (a) If ‖x‖ < s: |ζ(x)| = ζ(x) ≤ 1. The covector β := ψ₀(x) satisfies β(v) = ∫_0^1 t^m ω(tx)(x, v) dt for all v, so the sibling lemma iwl_cr_cest_radial_coeff_bound gives |ψ₀(x)| ≤ P^{2m+1}‖x‖. Hence |ψ(x)| ≤ 1·P^{2m+1}‖x‖ ≤ P^{2m+1}·s.
 (b) If ‖x‖ ≥ s: x ∉ B_s(0) = support ζ, so ζ(x) = 0 and |ψ(x)| = 0 ≤ P^{2m+1}·s, as s > r > 0. ∎

## Key steps

1. Take the ContDiffBump ζ centred at 0 with rIn = r, rOut = s; ψ := ζψ₀ is C^∞ with compact support, i.e. an element of TestFormOn univ m.
2. ζ = 1 on B̄_r(0) ⊇ B_r(0), so ψ = ψ₀ there and the radial formula holds on B_r(0).
3. |ψ(x)| = ζ(x)|ψ₀(x)|: for ‖x‖ < s use iwl_cr_cest_radial_coeff_bound and ‖x‖ < s, for ‖x‖ ≥ s ζ(x) = 0; hence |ψ(x)| ≤ P^{2m+1}s.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean`
- `python3 -I: dag.json status/lean_statement of cmb_abs_apply_le_of_massOn_le, isoperimetric_abs_covector_apply_le, iwl_cr_radial_operator, iwl_cr_cone_estimates and all cycle_reduction siblings; reuse records in nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-v2.json; nodes/*cone-exists-a1/decomposition-v1.json`
- `python3 -I name scan: 458 dag.json lean_names, subproblem lean_names of all nodes/*/decomposition-v*.json, substring 'iwl_cr_cest' over 4916 nodes/*/*.json`
- `git show 8c000d1fa9feee2acb018915bef93ab6fe6393ef:GMT/Ch06/Submission.lean; git show ba202ac0407b6e93210594416fcd0729874b2eff:GMT/Ch06/Submission.lean`
- `rg -n 'theorem norm_integral_le_of_norm_le_const|theorem integral_congr|theorem integral_zero' mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `rg -n 'structure ContDiffBump|theorem one_of_mem_closedBall|theorem support_eq|theorem tsupport_eq|protected theorem hasCompactSupport|protected theorem contDiff|theorem nonneg|theorem le_one' mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `rg -n 'theorem closure_ball |theorem isCompact_closedBall|exists_thickening_subset_open|theorem ofReal_mul|theorem le_of_forall_pos_lt_add|theorem HasCompactSupport.smul_right|theorem ContDiff.smul|theorem map_update_smul|theorem map_coord_zero|theorem Fintype.card_fun|image_eq_zero_of_notMem_tsupport' mathlib/Mathlib`
- `cat simongmt Poincare/SimonGMT/Chapter06/{Currents,Mass,CurrentLocalEquality,Forms}.lean`
- `grep -n -i 'cone|homotopy formula' book/chapter-06.txt; sed -n 436,560p book/chapter-06.txt`
- `python3 -I /tmp/ce-decomp-q7/scripts/gen.py (verifier gmt-compare.py contract_scope/child_modules + lean_contract.validate_lean_statement); lake env lean /tmp/ce-decomp-q7/gen/<key>__NodeChallenge.lean for the 6 children`
- `lake env lean /tmp/ce-decomp-q7/Scratch/{Assembly,ChildA,ChildB,ChildC,ChildD,Full}.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-estimates-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-estimates-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-exists-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-boundary-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-mass-bound-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-isoperimetric-a1-covector-eval-bound-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/RCLike/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Fintype/BigOperators.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ce-decomp-q7/scripts/gen.py`
- `/tmp/ce-decomp-q7/scripts/full.py`
- `/tmp/ce-decomp-q7/Scratch/Full.lean`
- `/tmp/ce-decomp-q7/Scratch/Assembly.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c. Its Ch06 Contract.lean is byte-identical (sha256 ea3ee0dd…853d) to the workspace Contract.lean and Submission.lean.

DAG findings:
- cmb_abs_apply_le_of_massOn_le and isoperimetric_abs_covector_apply_le are `accepted`, with frozen types byte-identical to the reuse children. Their accepted proofs (commits ba202ac0 and 8c000d1f) compile here with standard axioms.
- iwl_cr_radial_operator is `decomposing`, i.e. not accepted. It cannot be reused as a child, so it remains a parent-level dependency, and the new child cutoff_radial_form takes ψ₀ as an input.
- The prefix iwl_cr_ce_* is used by the cone_exists decomposition, so the new names use iwl_cr_cest_*. No match for iwl_cr_cest in dag.json or the 4,916 node JSON files.
- No accepted DAG lemma makes any new child redundant. cone_exists's iwl_cr_ce_cutoff_radial_operator is a different, unaccepted statement (a continuous linear cutoff operator).

Library inputs, all present in the snapshot Mathlib:
- intervalIntegral.norm_integral_le_of_norm_le_const (no integrability hypothesis), integral_congr, integral_zero;
- ContDiffBump: contDiff, nonneg, le_one, one_of_mem_closedBall, support_eq, hasCompactSupport;
- ContDiff.smul and HasCompactSupport.smul_right;
- closure_ball and isCompact_closedBall;
- ContinuousAlternatingMap.map_coord_zero and map_update_smul;
- ENNReal.ofReal_mul;
- le_of_forall_pos_lt_add, Nat.le_self_pow and Fintype.card_fun.

SimonGMT supplies the definitions used: support = univ ∖ zeroRegion, massOn as an sSup of ofReal(T ω) over massAdmissibleOn, covectorEuclideanNorm as a sum over StrictMono I, and IsSmoothForm = ContDiff ℝ ∞.

Public/book citation: Simon, Introduction to GMT (2014), Ch. 6, 2.25–2.31, printed pp. 140–142 (local book/chapter-06.txt). These give the homotopy formula, the mass estimate 2.27 (for the cone, M(0⨯T) ≤ R·M(T)) and the cone 0⨯T := h#([[(0,1)]]×T). The node's cruder constant P^{2m+1} suffices.

Lean checks: the 6 challenge modules compile. Full.lean (sha256 734b207f…) proves all 6 children with only propext, Classical.choice and Quot.sound, and proves the exact frozen parent type from them, with sorryAx only from the radial_operator stub. An independent reviewer agent re-verified this and accepted the split.
