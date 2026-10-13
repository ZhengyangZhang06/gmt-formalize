# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.eilenberg-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.eilenberg-a1.cover_majorant-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. X is an extended metric space; no measurable structure on X is used. ediam S ∈ [0, ∞] is the extended diameter `Metric.ediam S` (written `ediam` under `open Metric`); ediam ∅ = 0. Arithmetic is in [0, ∞] with 0·∞ = 0; x^a for x ∈ [0, ∞] and real a is `ENNReal.rpow`. For S ⊆ X and a real exponent a put w_a(S) := ⨆_{S ≠ ∅} (ediam S)^a, the supremum over the proposition S ≠ ∅, so w_a(S) = (ediam S)^a if S ≠ ∅ and w_a(∅) = 0 (in particular w_0(∅) = 0 although (ediam ∅)^0 = 1). For f : X → ℝ, edist on ℝ is edist(a, b) = |a − b| (as an element of [0, ∞]); `LipschitzOnWith L f A` means edist(f x, f y) ≤ L·edist(x, y) for all x, y ∈ A (unfolding the definition, `hf hx hy` gives this inequality). closedEBall(a, ρ) := {s ∈ ℝ : edist(s, a) ≤ ρ} for a ∈ ℝ and ρ ∈ [0, ∞] (`Metric.closedEBall`). λ¹ = volume on ℝ. The exponents m and m+1 are the real casts of natural numbers.

1. (Intervals.) Work classically. For each i with S_i ≠ ∅ choose x_i ∈ S_i (e.g. the chosen element of the nonempty set) and put I_i := closedEBall(f(x_i), L·ediam S_i); if S_i = ∅ put I_i := ∅. Each I_i is closed (`Metric.isClosed_closedEBall`), hence Borel. By `Real.volume_closedEBall`, λ¹(closedEBall(a, ρ)) = 2ρ for every a ∈ ℝ and every ρ ∈ [0, ∞] (including ρ = ∞ and ρ = 0). Hence λ¹(I_i) = 2·(L·ediam S_i) if S_i ≠ ∅, and λ¹(I_i) = λ¹(∅) = 0 if S_i = ∅.

2. (The function.) Put c_i := w_m(S_i) = ⨆_{S_i ≠ ∅} (ediam S_i)^m and ψ(s) := Σ_{i ∈ ℕ} 1_{I_i}(s)·c_i, i.e. ψ = Σ_i (indicator of I_i with constant value c_i). Each summand is the indicator of a Borel set with a constant value, hence measurable (`measurable_const.indicator`); a countable sum of measurable [0, ∞]-valued functions is measurable (`Measurable.ennreal_tsum`, or its replacement `Measurable.tsum`). So ψ is Borel.

3. (Pointwise bound.) Fix t ∈ ℝ, write B := A ∩ f⁻¹{t}, and fix i. We show w_m(S_i ∩ B) ≤ 1_{I_i}(t)·c_i. If S_i ∩ B = ∅, the left side is 0. Otherwise choose y ∈ S_i ∩ B, so y ∈ S_i, y ∈ A and f(y) = t. Then S_i ≠ ∅, so x_i ∈ S_i ⊆ A is defined, and by the Lipschitz condition on A and the definition of the diameter,
 edist(t, f(x_i)) = edist(f(y), f(x_i)) ≤ L·edist(y, x_i) ≤ L·ediam S_i
 (`Metric.edist_le_ediam_of_mem`, and monotonicity of multiplication by L, `mul_le_mul_right` in the pinned Mathlib naming). So t ∈ I_i and 1_{I_i}(t)·c_i = c_i = (ediam S_i)^m. Since S_i ∩ B ⊆ S_i, ediam(S_i ∩ B) ≤ ediam S_i (`Metric.ediam_mono`), and x ↦ x^m is monotone on [0, ∞] because m ≥ 0 (`ENNReal.rpow_le_rpow` with `Nat.cast_nonneg`), so w_m(S_i ∩ B) = (ediam(S_i ∩ B))^m ≤ (ediam S_i)^m. Summing over i (`ENNReal.tsum_le_tsum`) gives Σ_i w_m(S_i ∩ (A ∩ f⁻¹{t})) ≤ ψ(t).

4. (Integral.) By monotone convergence for series (`lintegral_tsum`; each summand is measurable, hence a.e.-measurable) and `lintegral_indicator_const`, ∫ ψ dλ¹ = Σ_i c_i·λ¹(I_i). Fix i. If S_i = ∅, the i-th term is c_i·0 = 0 ≤ 2L·w_{m+1}(S_i). If S_i ≠ ∅, put D := ediam S_i ∈ [0, ∞]; then c_i = D^m and by step 1 the i-th term is D^m·(2·(L·D)) = 2L·(D^m·D) = 2L·D^{m+1} = 2L·w_{m+1}(S_i). Here real powers with natural-number exponents agree with monoid powers (`ENNReal.rpow_natCast`: x^((n : ℕ) : ℝ) = x^n), and D^m·D = D^{m+1} (`pow_succ`) holds for every D ∈ [0, ∞], including D = 0 and D = ∞; the rest is commutative-semiring rearrangement in [0, ∞]. Summing (`ENNReal.tsum_le_tsum`) and pulling out the constant (`ENNReal.tsum_mul_left`): ∫ ψ dλ¹ ≤ Σ_i 2L·w_{m+1}(S_i) = 2L·Σ_i ⨆_{S_i ≠ ∅} (ediam S_i)^{m+1}. ∎

Remarks. L = 0 is allowed (then I_i = closedEBall(f(x_i), 0) = {f(x_i)} has measure 0 and both bounds still hold); ediam S_i = ∞ is allowed (λ¹(I_i) = 2·(L·∞) is ∞ if L > 0 and 0 if L = 0, matching `Real.volume_closedEBall`). Only the inclusions S_i ⊆ A (to apply the Lipschitz bound at x_i) and m ≥ 0 are used; no measurability of A, f or S_i is needed.

## Key steps

1. For nonempty S_i pick x_i ∈ S_i and let I_i := closedEBall(f(x_i), L·ediam S_i) (I_i := ∅ otherwise); λ¹(I_i) = 2·L·ediam S_i by Real.volume_closedEBall.
2. ψ := Σ_i 1_{I_i}·⨆_{S_i≠∅}(ediam S_i)^m is Borel (indicators of closed sets, countable sum).
3. If S_i ∩ A ∩ f⁻¹{t} ∋ y then t = f(y) ∈ I_i by the Lipschitz bound, and (ediam(S_i ∩ A ∩ f⁻¹{t}))^m ≤ (ediam S_i)^m; sum termwise.
4. lintegral_tsum + lintegral_indicator_const: ∫ψ = Σ_i c_i λ¹(I_i) = Σ_i 2L·w_{m+1}(S_i) (rpow_natCast, pow_succ).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp project/GMT/Ch06/Contract.lean project/GMT/Ch06/Submission.lean (identical); cmp snapshot Submission.lean with workspace GMT/Ch06/Submission.lean (identical)`
- `grep -rn 'slicing_im_coarea_eil\|near_optimal_cover\|liminf_cover_bound\|cover_majorant' local-references/197bdd4b88278494/project (no match)`
- `python3 scan of dag.json: lean_name containing eil/near_optimal/liminf/majorant/unnormalized (only slicing_im_coarea_eilenberg, slicing_mb_density_majorant, slicing_mb_pointwise_liminf_bound, the last two unrelated); lean_statement containing μH/μHE with ∑/diam/liminf (no reusable cover or liminf lemma); collision check of the four proposed names against all 507 lean_name values (none)`
- `grep -n 'hausdorffMeasure_apply\|hausdorffMeasure_le_liminf_tsum\|mkMetric_le_liminf_tsum\|mkMetric_apply' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `grep -rn 'addHaarScalarFactor_volume_hausdorffMeasure_ne_zero\|euclideanHausdorffMeasure_def\|μHE\[' mathlib/Mathlib (Geometry/Euclidean/Volume/Measure.lean; the def lemma is rfl)`
- `grep 'def ediam\|ediam_mono\|edist_le_ediam_of_mem\|ediam_le' mathlib/Mathlib/Topology/EMetricSpace/Diam.lean (namespace Metric)`
- `grep 'volume_closedEBall\|volume_closedBall\|volume_eball' mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `grep -rn 'theorem lintegral_liminf_le\|theorem lintegral_tsum\|theorem Measurable.liminf\|theorem Measurable.ennreal_tsum\|theorem lintegral_indicator_const' mathlib/Mathlib`
- `grep -rn 'def closedEBall\|mem_closedEBall\|isClosed_closedEBall\|tendsto_inv_nat_nhds_zero' mathlib/Mathlib/Topology`
- `grep "theorem mul_le_mul_left\b\|mul_le_mul_left'\|theorem mul_le_mul_right" mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean (no mul_le_mul_left'; mul_le_mul_right (bc : b ≤ c) (a) : a * b ≤ a * c)`
- `grep -rn 'theorem rpow_natCast\|theorem rpow_le_rpow' mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean; grep 'Subsingleton.countable\|Set.Countable.measure_zero' mathlib/Mathlib`
- `grep -rn 'hausdorffMeasure_apply\|hausdorffMeasure_le_liminf\|mkMetric_le_liminf\|Eilenberg\|eilenberg\|coarea_inequality' lake-packages-25730c7c/simongmt (no match); grep -n '^theorem\|^def' SimonGMT Chapter02/UpperIntegral.lean Chapter02/AreaNormalization.lean Chapter01/Hausdorff.lean`
- `sed verifier/gmt-compare.py contract_scope/child_modules (child scope: Contract opens, namespace GMT.Ch06, noncomputable section/end; target proved by exact Submission.<lean_name>)`
- `lake env lean /tmp/eilenberg-decomp-scratch/Stmts.lean (four child types elaborate in the comparator scope)`
- `lake env lean /tmp/eilenberg-decomp-scratch/{Parent,Dproof,Leaves,FullCheck}.lean (parent from unnormalized; unnormalized from the three leaves; leaves proved outright; comparator-style exact Submission.X checks; #print axioms: propext, Classical.choice, Quot.sound)`
- `independent reviewer: lake env lean /tmp/eil-review-k7q2x9/{Indep,Syn,Parens,Consts}.lean (independent derivation, instance constants, syntactic μH match after euclideanHausdorffMeasure_def)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/EMetricSpace/Diam.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/EMetricSpace/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Set/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/NullSingletonClass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/UpperIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaNormalization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-eilenberg-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-eilenberg-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-eilenberg-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1/decomposition-scope-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/eilenberg-decomp-scratch/Stmts.lean`
- `/tmp/eilenberg-decomp-scratch/Parent.lean`
- `/tmp/eilenberg-decomp-scratch/Dproof.lean`
- `/tmp/eilenberg-decomp-scratch/Leaves.lean`
- `/tmp/eilenberg-decomp-scratch/FullCheck.lean`
- `/tmp/eilenberg-decomp-scratch/draft_subproblems.json`
- `/tmp/eil-review-k7q2x9/Indep.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 contract; Submission is byte-identical to it.

No existing lemma to reuse:
- The snapshot has no Eilenberg inequality and no near-optimal-cover or empty-piece-free liminf lemma for Mathlib's μH.
- SimonGMT has none either; its content API concerns its own simonHausdorff measures.
- No accepted DAG node provides any of these.
- The four proposed names collide with nothing in the project or among the 507 DAG names.

Pinned Mathlib supplies:
- hausdorffMeasure_apply.
- hausdorffMeasure_le_liminf_tsum. It sums ediam^d without the nonemptiness supremum, which is why the reindexing child exists.
- euclideanHausdorffMeasure_def (rfl) and addHaarScalarFactor_volume_hausdorffMeasure_ne_zero.
- Metric.ediam, and Metric.closedEBall with Real.volume_closedEBall (= 2r for every r ∈ [0, ∞]).
- lintegral_tsum, lintegral_indicator_const, lintegral_liminf_le, Measurable.liminf, and the deprecated Measurable.ennreal_tsum.
- ENNReal.rpow_natCast and ENNReal.rpow_le_rpow.
- No mul_le_mul_left'; mul_le_mul_right replaces it.

Lean checks in the exact comparator scope:
- The four child types elaborate.
- The parent's frozen type follows from unnormalized.
- unnormalized follows from the three leaves.
- The three leaves are proved outright.
- All five pass comparator-style `exact Submission.X` checks, using only propext, Classical.choice and Quot.sound.

These scratch proofs certify the statements, not the downstream child workers.
