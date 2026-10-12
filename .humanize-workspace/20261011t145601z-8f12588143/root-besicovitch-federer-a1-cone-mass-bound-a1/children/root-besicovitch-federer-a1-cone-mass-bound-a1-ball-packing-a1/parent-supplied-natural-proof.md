# Parent-supplied natural-language proof

- Parent DAG node: `root.besicovitch_federer-a1.cone_mass_bound-a1`
- Child DAG node: `root.besicovitch_federer-a1.cone_mass_bound-a1.ball_packing-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is Fact (F2) and Step 7 of the parent proof of bf_coneMass_ball_le: packing disjoint n-balls of W into a larger ball of W (Mattila, Lemma 15.14; Dall'Alba, Lemma 4.6). Here it is stated for an arbitrary countable family. In the parent, ι = ℝ^N, T is the Vitali subfamily, w = W.starProjection, ρ(t) = s·h(t)/20, w₀ = W.starProjection a and R = δ/4.

Claim. Let n, N ∈ ℕ, W ⊆ ℝ^N a linear subspace with dim W = n, and Hⁿ := μHE[n]. Let ι be a type, T ⊆ ι countable, w : ι → ℝ^N, ρ : ι → ℝ, w₀ ∈ W and R ∈ ℝ. Assume w(i) ∈ W, ρ(i) > 0 and B(w(i), ρ(i)) ⊆ B(w₀, R) for all i ∈ T, and that the open balls B(w(i), ρ(i)), i ∈ T, are pairwise disjoint. Then Σ_{i∈T} ofReal(ρ(i)ⁿ) ≤ ofReal(Rⁿ) in [0, ∞].

Notation.
- B(v, r) is the open ball of ℝ^N.
- For v ∈ W, B_W(v, r) := {u ∈ W : |u − v| < r} is the open ball of W for the restricted Euclidean metric.
- μHE[n]_W is the Euclidean Hausdorff measure of the metric space W, with its Borel σ-algebra.
- Hⁿ = μHE[n] on ℝ^N is a measure on the Borel sets of ℝ^N.

1. Trivial case. If T = ∅, the sum is 0 ≤ ofReal(Rⁿ). Otherwise fix i₀ ∈ T. Since w(i₀) ∈ B(w(i₀), ρ(i₀)) ⊆ B(w₀, R), we get 0 ≤ |w(i₀) − w₀| < R, so R > 0.

2. Hⁿ on W is a Haar measure. W, with the restricted inner product, is a finite-dimensional real inner product space with finrank W = n.
- First rewrite n as finrank W, using the hypothesis finrank W = n. Then μHE[finrank W] on W is an additive Haar measure (Mathlib instance MeasureTheory.isAddHaarMeasure_euclideanHausdorffMeasure; equivalently it equals volume, InnerProductSpace.euclideanHausdorffMeasure_eq_volume).
- Put ω := μHE[n]_W(B_W(0, 1)).
- ω > 0, because a Haar measure charges nonempty open sets (Metric.measure_ball_pos).
- ω < ∞, because a Haar measure is finite on balls (measure_ball_lt_top).
- For v ∈ W and r > 0, the scaling law of Haar measures gives μHE[n]_W(B_W(v, r)) = ofReal(rⁿ)·ω (Measure.addHaar_ball_of_pos). This needs no nontriviality assumption, so n = 0 is included.

3. Transfer to ℝ^N. The inclusion map W → ℝ^N is an isometry, so Hⁿ(image of A) = μHE[n]_W(A) for every A ⊆ W (Isometry.euclideanHausdorffMeasure_image applied to isometry_subtype_coe). For v ∈ W and r > 0, W ∩ B(v, r) is exactly the image of B_W(v, r): a point z ∈ ℝ^N lies in W ∩ B(v, r) iff z ∈ W and |z − v| < r, and distances in W are those of ℝ^N. Therefore
 (F2) Hⁿ(W ∩ B(v, r)) = ofReal(rⁿ)·ω for all v ∈ W and r > 0.

4. The disjoint pieces. For i ∈ T let Bᵢ := W ∩ B(w(i), ρ(i)). Then:
- Bᵢ is a Borel set, because W is closed (a finite-dimensional subspace; Submodule.closed_of_finiteDimensional) and balls are open;
- Hⁿ(Bᵢ) = ofReal(ρ(i)ⁿ)·ω by (F2), since w(i) ∈ W and ρ(i) > 0;
- the sets Bᵢ (i ∈ T) are pairwise disjoint, because Bᵢ ⊆ B(w(i), ρ(i)) and these balls are pairwise disjoint;
- Bᵢ ⊆ W ∩ B(w₀, R), because B(w(i), ρ(i)) ⊆ B(w₀, R).

5. Additivity. T is countable, so countable additivity of Hⁿ on pairwise disjoint Borel sets (measure_biUnion), monotonicity, and (F2) for v = w₀ ∈ W and r = R > 0 give
 (Σ_{i∈T} ofReal(ρ(i)ⁿ))·ω = Σ_{i∈T} ofReal(ρ(i)ⁿ)·ω = Σ_{i∈T} Hⁿ(Bᵢ) = Hⁿ(⋃_{i∈T} Bᵢ) ≤ Hⁿ(W ∩ B(w₀, R)) = ofReal(Rⁿ)·ω.
 The first equality is ENNReal.tsum_mul_right.

6. Cancellation. Since 0 < ω < ∞, the factor ω can be cancelled in [0, ∞]. This gives Σ_{i∈T} ofReal(ρ(i)ⁿ) ≤ ofReal(Rⁿ), i.e. ∑' i : T, ENNReal.ofReal (ρ i ^ n) ≤ ENNReal.ofReal (R ^ n). ∎

## Key steps

1. If T = ∅ the sum is 0. Otherwise a nonempty ball B(w(i₀), ρ(i₀)) ⊆ B(w₀, R) forces R > 0.
2. After substituting n = finrank W, μHE[n] on W is an additive Haar measure, so μHE[n]_W(B_W(v, r)) = rⁿ·ω with ω := μHE[n]_W(B_W(0, 1)) ∈ (0, ∞).
3. The inclusion W → ℝ^N is an isometry and W ∩ B(v, r) is the image of B_W(v, r), so Hⁿ(W ∩ B(v, r)) = rⁿ·ω for v ∈ W and r > 0.
4. The sets W ∩ B(w(i), ρ(i)), i ∈ T, are pairwise disjoint Borel subsets of W ∩ B(w₀, R). Countable additivity gives ω·Σρ(i)ⁿ ≤ ω·Rⁿ.
5. Cancel ω ∈ (0, ∞).

## Reference use

### local-project

Queries:
- `cat manifest.json (project d09bc8a18ce60face651f042976e8465f21f0f68, mathlib 25730c7c759d108ef87ab70af2342a196760f79d); cmp project/GMT/Ch03/Contract.lean with workspace GMT/Ch03/Submission.lean (identical)`
- `rg -n "theorem exists_disjoint_subfamily_covering_enlargement" -A 12 mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `rg -n "countable_of_isOpen" mathlib/Mathlib`
- `rg -n "euclideanHausdorffMeasure" mathlib/Mathlib --type lean; sed -n 55,260p mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n "NoAtoms|noAtoms" mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n "theorem addHaar_ball\b|theorem addHaar_ball_center|theorem addHaar_ball_of_pos" mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `rg -n "def starProjection|norm_starProjection_apply_le|starProjection_apply_mem" mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `rg -n "^theorem measure_biUnion |^theorem measure_biUnion_le " mathlib/Mathlib/MeasureTheory; rg -n "theorem tsum_mul_left|theorem tsum_mul_right" mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `rg -n -i "cone|packing|vitali|slab" project/GMT/Ch03`
- `rg -n -i "theorem .*vitali|packing|disjoint_subfamily" simongmt/Poincare/SimonGMT`
- `grep -n "def PurelyUnrectifiable|def CountablyRectifiable" simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n -i "besicovitch|federer|purely|projection" book/chapter-03.txt`
- `lake env lean GMT/Scratch/ConeMassSplitStmts.lean, ConeMassCombinedCheck.lean, ConeMassCombinedCheck2.lean (import GMT.Ch03.Submission + contract namespace/opens; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/ConeMassCombinedCheck2.lean`

The pinned snapshot is project d09bc8a and Mathlib 25730c7c. The snapshot Contract.lean is byte-identical to the workspace Submission.lean used for compilation.

Relevant Mathlib facts, all confirmed by compilation:
- Vitali.exists_disjoint_subfamily_covering_enlargement (5r-lemma, τ > 1) and Set.PairwiseDisjoint.countable_of_isOpen, for Step 6 in the parent.
- For ball_packing: the instance MeasureTheory.isAddHaarMeasure_euclideanHausdorffMeasure (for μHE[finrank E]), Isometry.euclideanHausdorffMeasure_image with isometry_subtype_coe, Measure.addHaar_ball_of_pos, Metric.measure_ball_pos, measure_ball_lt_top, measure_biUnion and ENNReal.tsum_mul_right.
- For Hⁿ{x} = 0 in the parent: Measure.nullSingletonClass_hausdorff (0 < d).
- Submodule.norm_starProjection_apply_le and starProjection_apply_mem, for F1.
- measure_biUnion_le and ENNReal.tsum_mul_left, for Step 8.
- SimonGMT PurelyUnrectifiable n S := ∀ R ⊆ S, CountablyRectifiable n R → μHE[n] R = 0, used with the sibling in Step 2.

No-match results:
- No cone, slab, Vitali or packing lemma exists in project/GMT/Ch03.
- SimonGMT has only a finite separated-set packing lemma (TotallyBounded.exists_uniform_separated_bound) and Ch01 density/Vitali covering lemmas. It has no measure-packing lemma for balls in a subspace and no Mattila 15.14-type slab lemma, so both children are new obligations.
- Simon Ch. 3, Theorem 3.6 (chapter-03.txt lines 530–536) defers the proof to [Fed69]/[Ros84].

The scratch file ConeMassCombinedCheck2.lean compiles. Both children are proven with only standard axioms, and the exact parent type is proven from them plus the sibling's exact frozen type.
