# Parent-supplied natural-language proof

- Parent DAG node: `root.besicovitch_federer-a1.cone_mass_bound-a1`
- Child DAG node: `root.besicovitch_federer-a1.cone_mass_bound-a1.slab_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is Steps 3–4 of the parent proof of bf_coneMass_ball_le (P. Mattila, Geometry of Sets and Measures in Euclidean Spaces, Lemma 15.14; M. G. Dall'Alba, The Besicovitch–Federer Projection Theorem, Lemma 4.6). It is extracted for an arbitrary continuous linear map P and an arbitrary set S; in the parent, P = W.starProjection, S = B ∩ B(a, δ/8) and R = δ/4. Only the linearity of P and s > 0 are used.

Claim. Let N ∈ ℕ, P : ℝ^N → ℝ^N continuous linear, s > 0, R ∈ ℝ, S ⊆ ℝ^N and x ∈ ℝ^N. Assume some y ∈ S has |P(y − x)| < (s/4)|y − x|, and |y − x| ≤ R for all y ∈ S. Then there are h with 0 < h ≤ R and x′ ∈ S such that S ∩ {z : |P(z − x)| < s·h/4} ⊆ {x} ∪ ({y : |P(y − x)| < s|y − x|} ∩ B(x, 3h)) ∪ ({y : |P(y − x′)| < s|y − x′|} ∩ B(x′, 3h)).

Notation.
- |·| is the Euclidean norm.
- B(v, ρ) := {y : |y − v| < ρ} is the open ball (Metric.ball v ρ).
- For v ∈ ℝ^N and t > 0, X_∞(v, t) := {y : |P(y − v)| < t|y − v|}.
- Linearity of P gives P(0) = 0 and P(u − v) = P(u) − P(v).

1. Cone points. Let Y := {y ∈ S : |P(y − x)| < (s/4)|y − x|}. By hypothesis Y ≠ ∅. Every y ∈ Y satisfies y ≠ x: for y = x both sides of the defining inequality equal 0 (|P(0)| = 0 = (s/4)·0), and 0 < 0 is false. Hence |y − x| > 0 for every y ∈ Y. Also |y − x| ≤ R for every y ∈ Y, because Y ⊆ S.

2. The radius h. The set D := {|y − x| : y ∈ Y} ⊆ ℝ is nonempty (Step 1) and bounded above by R. Let h := sup D. Then:
 (★) |y − x| ≤ h for every y ∈ Y;
 h ≤ R, because R is an upper bound of D;
 h > 0, because for any y₀ ∈ Y we have h ≥ |y₀ − x| > 0.

3. The far point x′. Since h > 0 we have 3h/4 < h = sup D, so some element of D exceeds 3h/4. That is, there is x′ ∈ Y with |x′ − x| > 3h/4. Then x′ ∈ S, |x′ − x| ≤ h by (★), and |P(x′ − x)| < (s/4)|x′ − x|.

4. The slab inclusion. Let z ∈ S with |P(z − x)| < s·h/4. If z = x, then z ∈ {x} and we are done. Assume from now on z ≠ x.
 (a) |z − x| ≤ h. Suppose instead |z − x| > h. Since s > 0, |P(z − x)| < s·h/4 < (s/4)|z − x|, so z ∈ Y, and (★) gives |z − x| ≤ h, a contradiction. Consequently:
 - |z − x| ≤ h < 3h, i.e. z ∈ B(x, 3h);
 - |z − x′| ≤ |z − x| + |x − x′| ≤ h + h = 2h < 3h, i.e. z ∈ B(x′, 3h).
 (b) If z = x′, then |P(z − x)| < (s/4)|z − x| ≤ s|z − x|, so z ∈ X_∞(x, s). With (a), z ∈ X_∞(x, s) ∩ B(x, 3h).
 (c) If z ∈ X_∞(x′, s), then with (a), z ∈ X_∞(x′, s) ∩ B(x′, 3h).
 (d) Otherwise z ∉ X_∞(x′, s), i.e. s|z − x′| ≤ |P(z − x′)|.
 - Since z − x′ = (z − x) − (x′ − x), linearity and the triangle inequality give |P(z − x′)| ≤ |P(z − x)| + |P(x′ − x)|.
 - The right-hand side is < s·h/4 + (s/4)|x′ − x| ≤ s·h/4 + s·h/4 = s·h/2, using |x′ − x| ≤ h and s > 0.
 - Hence s|z − x′| < s·h/2, and dividing by s > 0 gives |z − x′| < h/2.
 - By the triangle inequality, |z − x| ≥ |x′ − x| − |z − x′| > 3h/4 − h/2 = h/4.
 - Therefore |P(z − x)| < s·h/4 < s|z − x|, i.e. z ∈ X_∞(x, s). With (a), z ∈ X_∞(x, s) ∩ B(x, 3h).
 In every case z ∈ {x} ∪ (X_∞(x, s) ∩ B(x, 3h)) ∪ (X_∞(x′, s) ∩ B(x′, 3h)). The computation in (d) also covers z = x′, since x′ ∉ X_∞(x′, s).

5. Conclusion. The number h from Step 2 and the point x′ ∈ S from Step 3 satisfy 0 < h ≤ R and S ∩ {z : |P(z − x)| < s·h/4} ⊆ {x} ∪ ({y : |P(y − x)| < s|y − x|} ∩ B(x, 3h)) ∪ ({y : |P(y − x′)| < s|y − x′|} ∩ B(x′, 3h)). In Lean the right-hand side is insert x (A ∪ A′), where A = {y | ‖P (y - x)‖ < s * ‖y - x‖} ∩ Metric.ball x (3 * h) and A′ is the same set with x′ in place of x. ∎

Lean pointers. Take h := sSup ((fun y ↦ ‖y - x‖) '' Y). Useful lemmas: le_csSup, csSup_le, exists_lt_of_lt_csSup, map_sub, norm_sub_le, dist_eq_norm, Set.mem_insert_iff, Set.mem_union.

## Key steps

1. Y := {y ∈ S : |P(y − x)| < (s/4)|y − x|} is nonempty, avoids x (so |y − x| > 0 on Y), and lies within distance R of x.
2. h := sup{|y − x| : y ∈ Y} satisfies 0 < h ≤ R and |y − x| ≤ h for all y ∈ Y; choose x′ ∈ Y with |x′ − x| > 3h/4.
3. Maximality of h: every z ∈ S with |P(z − x)| < s h/4 has |z − x| ≤ h, hence z ∈ B(x, 3h) and |z − x′| ≤ 2h < 3h.
4. If such a z ≠ x is in the s-cone at x′ it lies in X(x′, 3h, s). Otherwise linearity gives |z − x′| < h/2, hence |z − x| > h/4, |P(z − x)| < s|z − x| and z ∈ X(x, 3h, s).

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
