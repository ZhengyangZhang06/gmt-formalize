# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.eilenberg-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.eilenberg-a1.liminf_cover_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. X is an extended metric space whose measurable structure is its Borel σ-algebra. ediam S ∈ [0, ∞] is the extended diameter `Metric.ediam S` (written `ediam` under `open Metric`); ediam ∅ = 0. μH[d] is Mathlib's unnormalized d-dimensional Hausdorff measure `MeasureTheory.Measure.hausdorffMeasure d`, evaluated as an outer measure on arbitrary (possibly non-measurable) sets. Arithmetic is in [0, ∞] with 0·∞ = 0; x^a for x ∈ [0, ∞] and real a is `ENNReal.rpow`. For S ⊆ X and a real exponent a put w_a(S) := ⨆_{S ≠ ∅} (ediam S)^a, the supremum over the proposition S ≠ ∅, so w_a(S) = (ediam S)^a if S ≠ ∅ and w_a(∅) = 0 (in particular w_0(∅) = 0 although (ediam ∅)^0 = 1).

1. (Discard empty pieces.) For k ∈ ℕ let J_k := {i ∈ ℕ : T_{k,i} ≠ ∅}, regarded as the subtype {i : ℕ // (T k i).Nonempty}; it is countable (a subtype of ℕ), so `Countable (J_k)` holds for every k. Consider for each k the family (T_{k,i})_{i ∈ J_k}.

2. (Diameters.) For every k and every i ∈ J_k, ediam T_{k,i} ≤ r_k by hypothesis; in particular this holds eventually along atTop.

3. (Covering.) Let k ∈ ℕ and x ∈ s. By hypothesis x ∈ T_{k,i} for some i ∈ ℕ. Then T_{k,i} contains x, so it is nonempty, i ∈ J_k, and x ∈ ⋃_{j ∈ J_k} T_{k,j}. Hence s ⊆ ⋃_{j ∈ J_k} T_{k,j} for every k.

4. (Mathlib's covering bound.) Since r_k → 0 and each index type J_k is countable, `MeasureTheory.Measure.hausdorffMeasure_le_liminf_tsum` (with β = ℕ, the filter atTop, ι k = J_k and the family (k, j) ↦ T_{k,j}) applies to steps 2 and 3 and gives
 μH[d](s) ≤ liminf_{k→∞} Σ_{j ∈ J_k} (ediam T_{k,j})^d.
 (That lemma sums (ediam T)^d without the nonemptiness supremum; this is why empty pieces were discarded in step 1: for d = 0 an empty piece would contribute (ediam ∅)^0 = 1.)

5. (Compare the sums.) Fix k. By `tsum_subtype`, Σ_{j ∈ J_k} (ediam T_{k,j})^d = Σ_{i ∈ ℕ} 1_{J_k}(i)·(ediam T_{k,i})^d, the sum over ℕ of the indicator of the set J_k applied to i ↦ (ediam T_{k,i})^d. Compare termwise (`ENNReal.tsum_le_tsum`): if i ∈ J_k, the i-th term is (ediam T_{k,i})^d = w_d(T_{k,i}) (`le_iSup_of_le` with the proof of T_{k,i} ≠ ∅); if i ∉ J_k, the i-th term is 0 ≤ w_d(T_{k,i}). Therefore Σ_{j ∈ J_k} (ediam T_{k,j})^d ≤ Σ_i w_d(T_{k,i}). (In fact equality holds; only ≤ is needed.)

6. (Pass to liminf.) The bound of step 5 holds for every k, so by monotonicity of liminf (`Filter.liminf_le_liminf` with an eventually-everywhere bound; [0, ∞] is a complete lattice, so no boundedness side conditions are needed), liminf_k Σ_{j ∈ J_k} (ediam T_{k,j})^d ≤ liminf_k Σ_i w_d(T_{k,i}). Combined with step 4 this is the claim. No sign condition on d is needed. ∎

## Key steps

1. Reindex each cover by J_k := {i : T_{k,i} ≠ ∅}, a countable type; the reindexed families still cover s and have diameters ≤ r_k.
2. hausdorffMeasure_le_liminf_tsum gives μH[d](s) ≤ liminf_k Σ_{j ∈ J_k} (ediam T_{k,j})^d.
3. tsum_subtype and a termwise comparison give Σ_{j∈J_k}(ediam T_{k,j})^d ≤ Σ_i ⨆_{T_{k,i}≠∅}(ediam T_{k,i})^d; conclude by liminf_le_liminf.

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
