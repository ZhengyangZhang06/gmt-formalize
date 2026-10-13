# Parent-supplied natural-language proof

- Parent DAG node: `root.section3_consequences-a1.chart_projection_positive-a1`
- Child DAG node: `root.section3_consequences-a1.chart_projection_positive-a1.antilipschitz_measure_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Extracted from the parent proof of section3_chart_coordinateProjection_pos, step 7 with its facts (a)-(d). The parent follows Simon, Ch. 3, proof of Lemma 3.3, printed p. 79: “... is a C¹ diffeomorphism onto an open W ... and so Hⁿ(p_{j₁,…,jₙ}(S ∩ N ∩ B_ρ(x))) > 0”. Here the argument is stated for an arbitrary map f and an arbitrary set S.

Notation. ℝᵈ = Rn d = EuclideanSpace ℝ (Fin d) with the Euclidean norm |·|. For a metric space X with its Borel σ-algebra and d ≥ 0, μH[d] is the d-dimensional Hausdorff measure of X (Mathlib hausdorffMeasure). Hⁿ = μHE[n] is its Euclidean normalisation, and Lⁿ = volume on ℝⁿ. All of these are evaluated on arbitrary sets as outer measures. All values lie in [0, ∞], where multiplication is commutative, associative and monotone in each argument.

Statement. Let n, p ∈ ℕ, f : ℝⁿ → ℝᵖ, S ⊆ ℝⁿ an arbitrary set (no measurability assumed), and K ∈ ℝ≥0. Suppose |x − y| ≤ K·|f(x) − f(y)| for all x, y ∈ S. Then Lⁿ(S) ≤ Kⁿ·Hⁿ(f(S)).

Proof.

1. Facts.
(a) For every metric space X, μHE[n] = c_n·μH[n] as measures on X. Here c_n := addHaarScalarFactor(volume on ℝⁿ, μH[n]) ∈ ℝ≥0 is a single constant, independent of X. This is the definition (Mathlib MeasureTheory.Measure.euclideanHausdorffMeasure_def). Evaluated on a set E, it gives μHE[n](E) = c_n·μH[n](E) (Measure.smul_apply).
(b) On ℝⁿ, μHE[n] = Lⁿ (Mathlib EuclideanSpace.euclideanHausdorffMeasure_eq_volume).
(c) Let g : X → Y be a map between metric spaces and K ∈ ℝ≥0 with dist(a, b) ≤ K·dist(g(a), g(b)) for all a, b ∈ X. Then μH[d](E) ≤ K^d·μH[d](g(E)) for every d ≥ 0 and every E ⊆ X.
Mathlib: AntilipschitzWith.le_hausdorffMeasure_image. Its hypothesis AntilipschitzWith K g follows from the displayed inequality by AntilipschitzWith.of_le_mul_dist.
(d) If ι : Z → W is an isometry and d ≥ 0, then μH[d](ι(E)) = μH[d](E) for every E ⊆ Z (Mathlib Isometry.hausdorffMeasure_image, with side condition 0 ≤ d). The inclusion ι : S → ℝⁿ, with S carrying its subspace metric, is an isometry (isometry_subtype_coe).

2. The restricted map is anti-Lipschitz. Give S the subspace metric dist_S(a, b) = |a − b|, and let g : S → ℝᵖ, g(a) := f(a) (Set.domRestrict). For a, b ∈ S the hypothesis reads
dist_S(a, b) = |a − b| ≤ K·|f(a) − f(b)| = K·dist(g(a), g(b)).
So fact (c) applies to g with this K.

3. Hausdorff estimate inside S. Apply (c) to g with d := n ≥ 0 and E := S (the whole space S):
μH[n]_S(S) ≤ Kⁿ·μH[n]_{ℝᵖ}(g(S)), and g(S) = f(S).
In (c) the power K^d has the real exponent d = n, and it equals the natural power Kⁿ (ENNReal.rpow_natCast).

4. Transfer to ℝⁿ. Apply (d) to ι with E := S (the whole space S). Since ι maps the whole space S onto the subset S ⊆ ℝⁿ, μH[n]_{ℝⁿ}(S) = μH[n]_S(S). Together with step 3:
μH[n]_{ℝⁿ}(S) ≤ Kⁿ·μH[n]_{ℝᵖ}(f(S)).

5. Normalisation. Multiply the inequality of step 4 by c_n ≥ 0, then use (a) on ℝⁿ and on ℝᵖ with the same constant c_n:
μHE[n](S) = c_n·μH[n](S) ≤ c_n·(Kⁿ·μH[n](f(S))) = Kⁿ·(c_n·μH[n](f(S))) = Kⁿ·μHE[n](f(S)).

6. Conclusion. By (b), Lⁿ(S) = μHE[n](S), computed in ℝⁿ. Hence Lⁿ(S) ≤ Kⁿ·Hⁿ(f(S)). ∎

Remark. No measurability of S or f is used. The cases K = 0 and n = 0 need no separate treatment, because the argument is uniform. For example, for K = 0 and n ≥ 1, step 3 gives μH[n]_S(S) ≤ 0.

## Key steps

1. The restriction g = f|_S on the metric subspace S is K-anti-Lipschitz (AntilipschitzWith.of_le_mul_dist).
2. The anti-Lipschitz Hausdorff bound in S gives μH[n]_S(S) ≤ Kⁿ·μH[n](f(S)) (AntilipschitzWith.le_hausdorffMeasure_image, ENNReal.rpow_natCast).
3. The isometric inclusion S ↪ ℝⁿ gives μH[n]_S(S) = μH[n]_{ℝⁿ}(S) (Isometry.hausdorffMeasure_image, isometry_subtype_coe).
4. Multiplying by the common normalising constant c_n gives μHE[n](S) ≤ Kⁿ·μHE[n](f(S)) (euclideanHausdorffMeasure_def).
5. Since μHE[n] = volume on ℝⁿ, Lⁿ(S) ≤ Kⁿ·Hⁿ(f(S)).

## Reference use

### local-project

Queries:
- `cat local-references/d498d77b74ea2063/manifest.json`
- `cmp local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean GMT/Ch03/Contract.lean`
- `rg -n "theorem (exists_mem_forall_mem_nhdsWithin_pos_measure|measure_null_of_locally_null)" mathlib/Mathlib -A4`
- `rg -n "theorem (le_hausdorffMeasure_image|hausdorffMeasure_image_le|hausdorffMeasure_image) " mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n "theorem .*euclideanHausdorffMeasure_def|theorem .*euclideanHausdorffMeasure_eq_volume|def euclideanHausdorffMeasure|notation.*μHE" mathlib/Mathlib`
- `rg -n "theorem (LinearMap|ContinuousLinearMap)\.exists_antilipschitzWith|exists_antilipschitzWith" mathlib/Mathlib`
- `rg -n "theorem approximates_deriv_on_nhds|theorem approximates_deriv_on_open_nhds|protected theorem antilipschitz|theorem antilipschitz" mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem`
- `rg -n "^def domRestrict|^def restrict|deprecated.*restrict" mathlib/Mathlib/Data/Set/Restrict.lean`
- `grep -rn "of_le_mul_dist\|add_lipschitzWith\b" mathlib/Mathlib --include=*.lean`
- `grep -rn "theorem LinearMap.finrank_range_of_inj\|theorem finrank_euclideanSpace_fin" mathlib/Mathlib`
- `sed -n 55,70p mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean (ContDiffAt.hasStrictFDerivAt takes hn : n ≠ 0)`
- `rg -n "AntilipschitzWith|le_hausdorffMeasure_image|approximates_deriv_on_nhds" lake-packages-25730c7c/simongmt/Poincare/SimonGMT`
- `rg -n "antilipschitz|Antilipschitz" local-references/d498d77b74ea2063/project/GMT (no match)`
- `rg -n "theorem .*(antilipschitz|Antilipschitz).*(strict|Strict|fderiv)|theorem .*(strict|Strict)FDeriv.*antilipschitz" mathlib/Mathlib (no strict-derivative local antilipschitz lemma)`
- `env.contains `Poincare.SimonGMT.Chapter02.ApproximatesLinearOn.le_euclideanHausdorffMeasure_image after import GMT.Ch03.Submission (false)`
- `rg -l "section3_hasStrictFDerivAt_injective_local_antilipschitz|section3_antilipschitzOn_volume_le_euclideanHausdorff_image" dag.json nodes GMT SimonGMT (no match)`
- `sed -n 470,505p book/chapter-03.txt (Lemma 3.3 and its proof)`
- `lake env lean /tmp/chartpos-decomp-a7f3/Challenge.lean and /tmp/chartpos-decomp-a7f3/Final.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ApproximatesLinearOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/Antilipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Group/Uniform.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Data/Set/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`

Snapshot d498d77b74ea2063 (project d09bc8a, Mathlib 25730c7c): its Contract.lean is byte-identical to the workspace's GMT/Ch03/Contract.lean and Submission.lean.

Mathlib declarations found and used:
- Parent assembly: exists_mem_forall_mem_nhdsWithin_pos_measure (OuterMeasure/Basic.lean:159), LinearMap.finrank_range_of_inj, finrank_euclideanSpace_fin, ContDiffAt.hasStrictFDerivAt (RCLike.lean:62; takes hn : n ≠ 0), and the chain rule with ContinuousLinearMap.hasStrictFDerivAt.
- Child 1: LinearMap.exists_antilipschitzWith (FiniteDimension.lean:231), HasStrictFDerivAt.approximates_deriv_on_nhds (InverseFunctionTheorem/FDeriv.lean:76) and AntilipschitzWith.le_mul_dist.
- Child 2: AntilipschitzWith.le_hausdorffMeasure_image (Hausdorff.lean:807); Isometry.hausdorffMeasure_image (Hausdorff.lean:824) with isometry_subtype_coe; euclideanHausdorffMeasure_def (Volume/Measure.lean:74); EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Volume/Measure.lean:187); Set.domRestrict (Set.restrict is deprecated since 2026-07-19); ENNReal.rpow_natCast.

Gaps that justify the children (no match):
- ApproximatesLinearOn.antilipschitzWith (ApproximatesLinearOn.lean:317) needs an invertible f' : E ≃L F, so it does not cover an injective, non-surjective A.
- Mathlib has no lemma 'injective strict derivative ⇒ locally anti-Lipschitz', and no μHE/volume lower bound for maps that are anti-Lipschitz only on a subset.
- The project snapshot has no antilipschitz lemma.
- SimonGMT ApproximatesLinearOn.le_euclideanHausdorffMeasure_image (Chapter02/AreaApproximation.lean) is related, but GMT.Ch03.Submission does not import it, even transitively, so it is unusable.
- The proposed names do not occur in dag.json (73 nodes), the run nodes, GMT/ or SimonGMT.

Verification: /tmp/chartpos-decomp-a7f3/Final.lean compiles with only import GMT.Ch03.Submission. It contains full proofs of both children and of the parent, assembled from them with the sibling's frozen type as a hypothesis. Axioms used: propext, Classical.choice, Quot.sound.
