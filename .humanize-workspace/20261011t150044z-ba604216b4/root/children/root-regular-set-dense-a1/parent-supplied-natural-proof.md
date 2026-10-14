# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.regular_set_dense-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon 7.4.2 (chapter-07.txt lines 605–612: "an immediate consequence of the Allard Theorem 5.2 of Ch. 5 and Lemma 1.2"). The omitted argument is Simon Ch. 5, Corollary 7.3 and its proof (chapter-05.txt lines 1378–1395), in which the use of Allard's theorem (Ch. 5, 7.1) is supplied here by the sibling density_one_implies_regular.
1. If n = 0 then T = 0 (a minimizing 0-current supported in N loses mass when a point is deleted), so spt T = ∅. Assume n ≥ 1. Fix a representation T = τ(M, θ, ξ); μ_T = θH^n⌞M.
2. Density facts. By the sibling density_and_tangent_cones (part (1); spt ∂T = ∅), Θ(x) := Θ^n(μ_T, x) exists for every x ∈ U and is upper semicontinuous on U. Moreover Θ = θ μ_T-a.e. (Ch. 3, Remark 1.8(2) with Theorem 1.9, as used in Ch. 4 at chapter-04.txt line 350: densities of θH^n⌞M), so Θ is a positive integer μ_T-a.e. If x ∈ spt T, every ball B_r(x) has μ_T(B_r(x)) > 0, hence contains points w_j → x with Θ(w_j) ∈ ℤ_{≥1}; by upper semicontinuity Θ(x) ≥ 1.
3. Choice of a point (Ch. 5, proof of 7.3). Let x ∈ spt T and ρ > 0 with B_ρ(x) ⊆ U; we show reg T ∩ B_ρ(x) ≠ ∅. Let N₀ := min{j ∈ ℤ_{≥1} : Θ(z) = j for some z ∈ B_ρ(x)} (the set is nonempty by step 2). At μ_T-a.e. point of B_ρ(x), Θ is an integer ≥ N₀; as in step 2, upper semicontinuity gives Θ ≥ N₀ at every point of spt T ∩ B_ρ(x), hence θ ≥ N₀ μ_T-a.e. in B_ρ(x). Pick z₀ ∈ B_ρ(x) with Θ(z₀) = N₀ (so z₀ ∈ spt T ⊆ N) and, by upper semicontinuity, r > 0 with B_r(z₀) ⊆ B_ρ(x) and Θ < N₀ + 1 on B_r(z₀). Then θ = N₀ μ_T-a.e. in B_r(z₀).
4. The reduced current. Let U₀ := B_r(z₀) and T₀ := N₀^{−1}·(T restricted to U₀) ∈ 𝒟_n(U₀). T₀ = τ(M ∩ U₀, 1, ξ) up to a μ_T-null set, so it is integer multiplicity; ∂T₀ = 0 in U₀; spt T₀ ⊆ N; (N̄∖N) ∩ U₀ = ∅; and T₀ is minimizing in U₀ ∩ N: if W ⊂⊂ U₀ is open and S₀ is an integer multiplicity competitor for T₀ (∂S₀ = 0, spt(S₀ − T₀) ⊆ U₀ ∩ N ∩ W compact), then S := T + N₀(S₀ − T₀) (the compactly supported difference extended by zero) is an integer multiplicity competitor for T, with M_W(S) = N₀M_W(S₀) and M_W(T) = N₀M_W(T₀) (multiplicity N₀ a.e. on W ∩ M; the competitor S₀ − T₀ changes T only inside W), so M_W(T₀) ≤ M_W(S₀). Also sup M_W(T₀) < ∞ for W ⊂⊂ U₀, and Θ^n(μ_{T₀}, z₀) = Θ(z₀)/N₀ = 1.
5. Apply the sibling density_one_implies_regular with U := U₀, the constant sequences T_i := T₀, y_i := z₀, limit T₀ and y := z₀ (z₀ ∈ N ∩ U₀, z₀ ∈ spt T₀, HasMassDensity T₀ z₀ 1). It gives z₀ ∈ reg T₀: there are ρ' > 0 with B_{ρ'}(z₀) ⊆ U₀, m ∈ ℤ∖{0}, and an embedded oriented C¹ submanifold M' ∋ z₀ of locally finite H^n-measure with T₀ = m[[M']] in B_{ρ'}(z₀). Then T = N₀m[[M']] in B_{ρ'}(z₀) ⊆ U, with N₀m ≠ 0 and z₀ ∈ spt T, so z₀ ∈ reg T ∩ B_ρ(x).
6. Since ρ was arbitrary, x ∈ closure(reg T); hence spt T ⊆ closure(reg T).

## Key steps

1. Densities exist, are upper semicontinuous, integer a.e. and ≥ 1 on spt T.
2. Near a point of least integer density N₀ in a ball, T/N₀ is a minimizing cycle with density 1.
3. density_one_implies_regular (constant sequences) gives a regular point in every ball.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n sorry local-references/123e8435b4a2469b/project/GMT -t lean -c`
- `rg -n 'μHE\[' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n '^(theorem|lemma|def|structure) ' simongmt/Poincare/SimonGMT/{Chapter06/Product.lean,Chapter02/BV.lean,Chapter03/FinitePerimeter.lean,AppendixA/Foundations.lean,Chapter07/Basic.lean}`
- `rg -n -i 'allard|federer|fleming|compactness theorem|open obligation|slice' simongmt/Poincare/SimonGMT`
- `lake env lean /tmp/ch07-attempt3/Check.lean (ten child types + conditional root assembly + #print axioms)`
- `lake env lean /tmp/ch07-attempt3/Lib.lean (#print axioms of minimizing_summands_source, cone_simonsDefect_lower_bound, bvVariationOn_le_liminf_of_locallyL1)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Product.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/FinitePerimeter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter05/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter07/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixA/Foundations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/ConeDefect.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-07-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root/decomposition-audit-v2.json`
- `/tmp/ch07-attempt3/Check.lean`
- `/tmp/ch07-attempt3/Lib.lean`

The snapshot contract (project b4d606d, mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean; each snapshot chapter contract has only its frozen final sorry. All ten child Lean types elaborate after the contract's definitions in namespace GMT.Ch07 with its opens (only the stub sorry warnings), and the conditional assembly of the eleven-conjunct root depends only on propext, Classical.choice and Quot.sound. Reusable library lemmas, each using only standard axioms: Chapter06.WeaklyConvergesOn.massOn_le_liminf (lower semicontinuity of mass), Chapter07.minimizing_summands_source (Lemma 1.4), AppendixB.cone_simonsDefect_lower_bound (B.11) and Chapter02.bvVariationOn_le_liminf_of_locallyL1 (lower semicontinuity of variation). The library proves none of the following, so they are cited from Simon: Appendix A.4 (Foundations.lean calls the dimension-reduction proof an open obligation), Allard regularity (Chapter05/Basic.lean has only analytic foundations), Federer–Fleming compactness (Currents.lean: separate obligation), BV compactness (BV.lean does not claim subsequence compactness), and products [[ℝ^m]] × S₀ (Product.lean has only point products). μHE[n] is a nonzero finite multiple of μH[n] (Measure.lean), so H^n and μH[n] have the same null sets. The DAG contains only root, so no reserved names collide.
