# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.caratheodory_criterion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

PROOF OF `CaratheodoryCriterion` (Simon, Ch. 1, Lemma 1.6 and Theorem 1.13; printed proof, transcribed and completed).

Statement. Let (X, d) be a metric space and μ an outer measure on X with the property
  (H) μ(A ∪ B) = μ(A) + μ(B) whenever A, B ⊆ X and there is a real r > 0 with r ≤ d(a, b) for all a ∈ A, b ∈ B.
Then every Borel set E ⊆ X is μ-measurable in Carathéodory's sense (Def. 1.2): μ(S) = μ(S ∩ E) + μ(S ∖ E) for every S ⊆ X. (In Lean: `μ.IsCaratheodory E` for every `E` with `MeasurableSet[borel X] E`.)

Notation. M denotes the family of μ-measurable sets. An outer measure is monotone, countably subadditive and μ(∅) = 0 (Simon 1.1).

Step 0 (Remark 1.3). A ⊆ X is μ-measurable iff μ(S) ≥ μ(S ∖ A) + μ(S ∩ A) for every S with μ(S) < ∞. Indeed this inequality is trivial when μ(S) = ∞, and the reverse inequality μ(S) ≤ μ(S ∖ A) + μ(S ∩ A) always holds by subadditivity.

Step 1 (Lemma 1.6: M is a σ-algebra; printed Steps 1–5).
 1a. ∅, X ∈ M, and A ∈ M ⇔ X ∖ A ∈ M, because the defining identity is symmetric in A and X ∖ A.
 1b. (Printed Step 1.) A₁, A₂ ∈ M ⇒ A₂ ∖ A₁ ∈ M. Let μ(S) < ∞. Measurability of A₁ with test set S ∩ A₂ gives μ(S ∩ A₂) = μ(S ∩ A₂ ∩ A₁) + μ(S ∩ (A₂ ∖ A₁)); measurability of A₂ with test set S gives μ(S) = μ(S ∩ A₂) + μ(S ∖ A₂). All terms are finite, so
   μ(S ∩ (A₂ ∖ A₁)) = μ(S) − μ(S ∖ A₂) − μ(S ∩ A₂ ∩ A₁) ≤ μ(S) − μ((S ∖ A₂) ∪ (S ∩ A₂ ∩ A₁)) = μ(S) − μ(S ∖ (A₂ ∖ A₁)),
   using subadditivity and the identity (S ∖ A₂) ∪ (S ∩ A₂ ∩ A₁) = (S ∖ A₂) ∪ (S ∩ A₁) = S ∖ (A₂ ∖ A₁). By Step 0, A₂ ∖ A₁ ∈ M.
 1c. (Printed Step 2.) A₁, A₂ ∈ M ⇒ A₁ ∪ A₂ ∈ M: by 1a and 1b, (X ∖ A₁) ∩ (X ∖ A₂) = (X ∖ A₂) ∖ A₁ ∈ M, hence A₁ ∪ A₂ = X ∖ ((X ∖ A₁) ∩ (X ∖ A₂)) ∈ M. If A₁, A₂ ∈ M are disjoint, then using A₁ with test set S ∩ (A₁ ∪ A₂): μ(S ∩ (A₁ ∪ A₂)) = μ(S ∩ A₁) + μ(S ∩ A₂).
 1d. (Printed Step 3.) By induction, finite unions of members of M lie in M, and μ(S ∩ ⋃_{j≤N} A_j) = Σ_{j≤N} μ(S ∩ A_j) for pairwise disjoint A₁, …, A_N ∈ M and every S.
 1e. (Printed Step 4.) If A₁, A₂, … ∈ M are pairwise disjoint and S ⊆ X, then by 1d and monotonicity
   μ(S) = μ(S ∩ ⋃_{j≤N} A_j) + μ(S ∖ ⋃_{j≤N} A_j) ≥ Σ_{j≤N} μ(S ∩ A_j) + μ(S ∖ ⋃_{j≥1} A_j).
   Letting N → ∞ and using subadditivity, μ(S) ≥ Σ_j μ(S ∩ A_j) + μ(S ∖ ⋃_j A_j) ≥ μ(S ∩ ⋃_j A_j) + μ(S ∖ ⋃_j A_j); by Step 0, ⋃_j A_j ∈ M. (Replacing S by S ∩ ⋃_j A_j also gives μ(S ∩ ⋃_j A_j) = Σ_j μ(S ∩ A_j), Remark 1.7.)
 1f. (Printed Step 5.) For arbitrary A₁, A₂, … ∈ M put Ã_j := A_j ∖ (A₁ ∪ ⋯ ∪ A_{j−1}) ∈ M (1b, 1d). The Ã_j are pairwise disjoint with ⋃_j Ã_j = ⋃_j A_j, so ⋃_j A_j ∈ M by 1e.
 Hence M is a σ-algebra.

Step 2 (reduction to closed sets). The Borel σ-algebra is the smallest σ-algebra containing the open sets, equivalently (by closure under complements) the closed sets. Since M is a σ-algebra (Step 1), it suffices to show that every closed set C ⊆ X lies in M. If C = ∅ this is clear, so let C ≠ ∅. Then dist(x, C) := inf_{c∈C} d(x, c) is a finite, 1-Lipschitz function of x, and, C being closed, dist(x, C) = 0 ⇔ x ∈ C. By Step 0 we must show
  (*) μ(S) ≥ μ(S ∖ C) + μ(S ∩ C) for every S ⊆ X with μ(S) < ∞.

Step 3. For j ≥ 1 let C_j := {x ∈ X : dist(x, C) ≤ 1/j}. If a ∈ S ∖ C_j and b ∈ S ∩ C, then d(a, b) ≥ dist(a, C) > 1/j, so (H) applies with r = 1/j and, by monotonicity,
  μ(S) ≥ μ((S ∖ C_j) ∪ (S ∩ C)) = μ(S ∖ C_j) + μ(S ∩ C).
Thus (*) follows once we show lim_{j→∞} μ(S ∖ C_j) = μ(S ∖ C).

Step 4. For k ≥ 1 let R_k := {x ∈ S : 1/(k+1) < dist(x, C) ≤ 1/k}. Since C is closed, S ∖ C = {x ∈ S : dist(x, C) > 0} = (S ∖ C_j) ∪ ⋃_{k≥j} R_k for every j. By monotonicity and subadditivity,
  μ(S ∖ C_j) ≤ μ(S ∖ C) ≤ μ(S ∖ C_j) + Σ_{k≥j} μ(R_k).
Hence it suffices to show Σ_{k≥1} μ(R_k) < ∞ (then the tails tend to 0).

Step 5. If i ≥ 1, l ≥ i + 2, x ∈ R_i and y ∈ R_l, then, dist(·, C) being 1-Lipschitz,
  d(x, y) ≥ dist(x, C) − dist(y, C) > 1/(i+1) − 1/l ≥ 1/(i+1) − 1/(i+2) > 0.
Consequently, for N ≥ 2 the sets ⋃_{k=1}^{N−1} R_{2k} and R_{2N} satisfy the hypothesis of (H) with r := 1/(2N−1) − 1/(2N) > 0 (for k ≤ N − 1: 1/(2k+1) − 1/(2N) ≥ r), and likewise ⋃_{k=1}^{N−1} R_{2k−1} and R_{2N−1} with r := 1/(2N−2) − 1/(2N−1) > 0. By (H) and induction on N,
  Σ_{k=1}^N μ(R_{2k}) = μ(⋃_{k=1}^N R_{2k}) ≤ μ(S),   Σ_{k=1}^N μ(R_{2k−1}) = μ(⋃_{k=1}^N R_{2k−1}) ≤ μ(S).
Letting N → ∞, Σ_{k≥1} μ(R_k) ≤ 2μ(S) < ∞.

Step 6 (conclusion). By Steps 4–5, μ(S ∖ C_j) → μ(S ∖ C); letting j → ∞ in Step 3 gives (*). So every closed set is μ-measurable, and by Step 2 every Borel set is μ-measurable. ∎

Formalization note (non-binding; not part of the argument): Mathlib's `MeasureTheory.OuterMeasure.IsMetric.borel_le_caratheodory` (Mathlib/MeasureTheory/Measure/Hausdorff.lean) is this theorem for the hypothesis `μ.IsMetric` (additivity on `Metric.AreSeparated` pairs); SimonGMT wraps it as `Poincare.SimonGMT.Chapter01.caratheodory_metric_criterion`. The only bridge needed is: `Metric.AreSeparated A B` (some r ∈ ℝ≥0∞, r ≠ 0, with r ≤ edist a b) yields the real r' := (min r 1).toReal > 0 with r' ≤ dist a b, so (H) implies `μ.IsMetric`.

## Key steps

1. Lemma 1.6: the Carathéodory-measurable sets form a σ-algebra (printed Steps 1–5).
2. Reduce to nonempty closed C and, by Remark 1.3, to μ(S) ≥ μ(S ∖ C) + μ(S ∩ C) for μ(S) < ∞.
3. With C_j = {dist(·, C) ≤ 1/j}, the sets S ∖ C_j and S ∩ C are 1/j-separated, so μ(S) ≥ μ(S ∖ C_j) + μ(S ∩ C).
4. S ∖ C = (S ∖ C_j) ∪ ⋃_{k≥j} R_k with annuli R_k, so μ(S ∖ C_j) ≤ μ(S ∖ C) ≤ μ(S ∖ C_j) + Σ_{k≥j} μ(R_k).
5. R_i and R_l are positively separated for l ≥ i + 2; the hypothesis on even and odd unions gives Σ_k μ(R_k) ≤ 2μ(S) < ∞.
6. Hence μ(S ∖ C_j) → μ(S ∖ C): closed sets, and therefore all Borel sets, are μ-measurable.

## Reference use

### local-project

Queries:
- `cat manifest.json (snapshot root e8e26216f05cbb4e)`
- `rg -n '^def (CaratheodoryCriterion|BorelRegularApproximation|LusinTheorem|LebesgueEqHausdorff|IsodiametricInequality|UpperDensityComparison|UpperDensityTheorem|BesicovitchCovering|GeneralDensityTheorem|LebesgueDifferentiation|RadonNikodymTheorem|HausdorffDensityBounds|RieszPositive|RieszVector|RadonCompactness)|^theorem main_theorem|^universe|^open|^namespace' project/GMT/Ch01/Contract.lean`
- `cmp project/GMT/Ch01/Contract.lean project/GMT/Ch01/Submission.lean`
- `rg -n -c Poincare.SimonGMT project mathlib/Mathlib`
- `rg -n 'theorem simon_theorem' . (no match: SimonGMT is not in the snapshot)`
- `rg -n 'theorem borel_le_caratheodory|def IsMetric' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n '^theorem exist_disjoint_covering_families|^theorem isEmpty_satelliteConfig_multiplicity|def multiplicity' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `rg -n 'theorem integral_rieszMeasure|instance rieszMeasure_regular|instance regular_rieszMeasure' mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/NNReal.lean mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `rg -n 'theorem volume_ball|theorem volume_closedBall' mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `rg -n 'def IsCaratheodory|def caratheodory |theorem isCaratheodory_iff' mathlib/Mathlib/MeasureTheory/OuterMeasure/Caratheodory.lean`
- `rg -n 'theorem toMeasure_apply|theorem le_toMeasure_apply' mathlib/Mathlib/MeasureTheory/Measure/OuterMeasure.lean; rg -n 'theorem ae_iff' mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `rg -n 'theorem setLIntegral_trim_ae|theorem lintegral_trim_ae' mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean; rg -n 'theorem integral_trim_ae|theorem integral_trim ' mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean; rg -n 'theorem restrict_trim' mathlib/Mathlib/MeasureTheory/Measure/Trim.lean`
- `rg -n 'sigmaCompactSpace_of_locallyCompact_secondCountable|noncomputable def choice|theorem exists_superset_of_isCompact' mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `rg -n '^instance|^theorem' mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean; rg -n 'metrizableSpace_of_t3_secondCountable' mathlib/Mathlib/Topology/Metrizable/Urysohn.lean; rg -n 'theorem exists_compact_superset' mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean`
- `rg -n 'theorem exists_continuous_one_zero_of_isCompact' mathlib/Mathlib/Topology/UrysohnsLemma.lean; rg -n 'theorem IsCompact.tendsto_subseq' mathlib/Mathlib/Topology/Sequences.lean`
- `rg -n 'theorem tendsto_iff_forall_integral_tendsto' mathlib/Mathlib/MeasureTheory/Measure/FiniteMeasure.lean; rg -n -F 'CompactSpace (ProbabilityMeasure' mathlib/Mathlib/MeasureTheory/Measure/Prokhorov.lean; rg -n 'theorem measure_iUnion_le|theorem measure_mono_null' mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `test -f on every cited snapshot file (all present); cmp of cited Mathlib files against lake-packages-25730c7c/mathlib (identical)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/GMT/Ch01/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/GMT/Ch01/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/GMT/Ch01/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/PROBLEM.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/lakefile.toml`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/NNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/OuterMeasure/Caratheodory.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Measure/OuterMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Measure/Trim.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/UrysohnsLemma.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/Metrizable/Urysohn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Measure/FiniteMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Measure/Prokhorov.lean`

The manifest pins project ec1c322 and Mathlib 25730c7c. In the snapshot, project/GMT/Ch01/Contract.lean is byte-identical to Submission.lean. It defines exactly the fifteen Props CaratheodoryCriterion … RadonCompactness (lines 88–303), with main_theorem at line 313, inside namespace GMT.Ch01 with `universe u v` (line 69) and the opens at lines 63–65. Each child lean_statement is one of these Props or a conjunction of two of them; the two merged children with universe parameters share the declared universe u, which the comparator replays from that scope. README.md maps the conjuncts to SimonGMT theorems and documents the 4.16 erratum (second countability). That erratum is applied in radon_compactness. The snapshot contains no SimonGMT declarations: rg finds 'Poincare.SimonGMT' only as imports and opens in the project files, and 'theorem simon_theorem' has no match. The package is pinned in project/lake-manifest.json and lives outside the snapshot, so the children cite it only in non-binding formalization notes. The snapshot's Mathlib contains the facts those notes rely on:
- OuterMeasure.IsMetric and borel_le_caratheodory: Measure/Hausdorff.lean:137,161.
- Besicovitch.exist_disjoint_covering_families (Covering/Besicovitch.lean:455), multiplicity and isEmpty_satelliteConfig_multiplicity (BesicovitchVectorSpace.lean:98,488).
- NNRealRMK.integral_rieszMeasure and rieszMeasure_regular (RieszMarkovKakutani/NNReal.lean:47,66); the real RMK (Real.lean:345,357).
- EuclideanSpace.volume_ball and volume_closedBall: Lebesgue/VolumeOfBalls.lean:307,324.
- IsCaratheodory and the caratheodory σ-algebra: OuterMeasure/Caratheodory.lean:55,176,181.
- toMeasure_apply and le_toMeasure_apply (Measure/OuterMeasure.lean:46,50); ae_iff (OuterMeasure/AE.lean:134).
- setLIntegral_trim_ae (Integral/Lebesgue/Add.lean:490); integral_trim and integral_trim_ae (Bochner/Basic.lean:1301,1332); restrict_trim (Measure/Trim.lean:108).
- σ-compactness and compact exhaustions: SigmaCompact.lean:187,376,418.
- Urysohn's lemma: UrysohnsLemma.lean:404.
- Separability of C(X,Y): ContinuousMap/SecondCountableSpace.lean:108. Metrizability: Metrizable/Urysohn.lean:127.
- Compact supersets: LocallyCompact.lean:58. IsCompact.tendsto_subseq: Sequences.lean:298.
- Weak convergence and Prokhorov: FiniteMeasure.lean:727; Prokhorov.lean:176.
The cited Mathlib files are byte-identical to the packages used by the build. The mathematical arguments of the children are the printed proofs of the source and do not depend on these declarations.
