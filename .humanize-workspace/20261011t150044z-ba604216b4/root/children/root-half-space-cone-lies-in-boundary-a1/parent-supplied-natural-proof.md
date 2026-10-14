# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.half_space_cone_lies_in_boundary-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon 7.4.5 and its proof (chapter-07.txt lines 689–737), using the weighted first-variation identity of Ch. 4, 5.1 (chapter-04.txt lines 596–612) with H = 0 and the monotonicity identity Ch. 4, 3.6. Corrections, made explicit: the identity (1) is d/dρ[ρ^{−n}∫hφ(r/ρ)dμ] = +ρ^{−n−1}∫(x·∇^V h)φ(r/ρ)dμ (it is derived in step 4); the printed primitive ψ(x) = ∫_{|x|}^∞ rφ(r/ρ)dr has the opposite sign of the one used below, which does not affect the vanishing; φ is taken constant near 0 so that the test fields are C¹.
1. Case n = 0: a 0-current C minimizing in ℝ^k is 0 (deleting one point of a representation gives an integer multiplicity competitor of smaller mass), so spt C = ∅ and the claim holds. Assume n ≥ 1, P := n + k. Fix a representation R = (M, θ, ξ) of C (C is integer multiplicity, being minimizing) and put μ := R.measure = θH^n⌞M, the mass measure of C (Ch. 6, 3.2(3)). Then spt C = spt μ: if μ(B) = 0 for an open ball B, |C(ω)| ≤ ∫|ω|dμ = 0 for forms supported in B; if C vanishes on all forms supported in B, M_B(C) = μ(B) = 0. Let e := v/|v| and h(x) := e·x; then H := {x : 0 < ⟨v, x⟩} = {h > 0}, closure H = {h ≥ 0} and frontier H = {h = 0} (v ≠ 0).
2. Stationarity (book line 697). Apply the sibling minimizing_implies_stationary with ℓ = k, U = N = ℝ^P: univ is an embedded C² (n+k)-submanifold (chart the identity), closure univ ∖ univ = ∅, spt C ⊆ univ, C is minimizing in univ ∩ univ = univ, ∂C = 0. Hence ∫ div_M X dμ = 0 for every X ∈ C¹_c(ℝ^P; ℝ^P) (every vector is tangent to ℝ^P), where div_M X(x) = trace(p_{T_xM}∘DX(x)), T_xM the approximate tangent plane (an n-plane for μ-a.e. x).
3. Radial tangency (book line 698: "(Dr)^⊥ = 0 by virtue of the fact that C is a cone"). IsConeCurrent C gives η_{0,λ#}C = C for λ > 0; the mass measure of η_{0,λ#}C is λ^{−n}(η_{0,λ})_#μ (area formula for the homothety), so μ(λA) = λ^nμ(A) for Borel A, μ({0}) = 0, and ρ^{−n}μ(B_ρ(0)) is constant in ρ > 0. The monotonicity identity (Ch. 4, 3.6, H = 0) ρ^{−n}μ(B_ρ(0)) − σ^{−n}μ(B_σ(0)) = ∫_{B_ρ(0)∖B_σ(0)}|D^⊥r|²r^{−n}dμ (r = |x|, D^⊥r the projection of Dr = x/r onto (T_xM)^⊥) therefore gives D^⊥r = 0 μ-a.e., i.e. x^T := p_{T_xM}(x) = x for μ-a.e. x.
4. The weighted identity (book (1); Ch. 4, 5.1 with H = 0). Let φ ∈ C¹(ℝ), φ ≥ 0, constant on (−∞, δ₀] for some δ₀ > 0 and φ = 0 on [1, ∞). For ρ > 0 put I(ρ) := ∫ φ(r/ρ)h dμ. The field X_ρ(x) := φ(|x|/ρ)h(x)x is C¹ (x ↦ φ(|x|/ρ) is C¹ because φ is constant near 0) with support in B̄_ρ(0). Using div_M x = n, ∇^M(φ(r/ρ)) = ρ^{−1}φ'(r/ρ)∇^M r and x·∇^M r = |x^T|²/r = r|∇^M r|² = r(1 − |D^⊥r|²): div_M X_ρ = nφ(r/ρ)h + (r/ρ)φ'(r/ρ)(1 − |D^⊥r|²)h + φ(r/ρ)x·∇^M h. Differentiation under the integral sign (|∂_ρφ(r/ρ)| = rρ^{−2}|φ'(r/ρ)| is bounded on B_b(0) uniformly for ρ ∈ [a, b] ⊂ (0,∞), and μ(B_b(0)) < ∞) gives ρI'(ρ) = −∫(r/ρ)φ'(r/ρ)h dμ, and likewise for J(ρ) := ∫φ(r/ρ)|D^⊥r|²h dμ. Stationarity ∫div_M X_ρ dμ = 0 thus reads nI − ρI' + ρJ' + ∫φ(r/ρ)x·∇^M h dμ = 0, i.e. d/dρ[ρ^{−n}I(ρ)] = ρ^{−n}J'(ρ) + ρ^{−n−1}∫(x·∇^M h)φ(r/ρ)dμ. By step 3, J ≡ 0, so (1): d/dρ[ρ^{−n}I(ρ)] = +ρ^{−n−1}∫(x·∇^M h)φ(r/ρ)dμ for all ρ > 0.
5. The right side of (1) vanishes (book lines 708–719). Since ∇^M h = p_{T_xM}(e) and r∇^M r = x^T: x·∇^M h = e·x^T = r e·∇^M r. Let Ψ_ρ(s) := −∫_s^∞ tφ(t/ρ)dt (s ≥ 0), so Ψ_ρ'(s) = sφ(s/ρ), Ψ_ρ(s) = 0 for s ≥ ρ, and put Y_ρ(x) := Ψ_ρ(|x|)e. Then DY_ρ(x)w = (φ(|x|/ρ)x·w)e, which is continuous on ℝ^P (also at 0), so Y_ρ ∈ C¹_c(ℝ^P; ℝ^P) with spt Y_ρ ⊆ B̄_ρ(0), and div_M Y_ρ = trace(p_{T_xM}∘DY_ρ) = φ(r/ρ)(e·x^T) = rφ(r/ρ)e·∇^M r = (x·∇^M h)φ(r/ρ). By step 2, ∫(x·∇^M h)φ(r/ρ)dμ = ∫div_M Y_ρ dμ = 0. Hence ρ ↦ ρ^{−n}I(ρ) is constant on (0, ∞). (Since x^T = x a.e., the same computation shows directly ∫hφ(r/ρ)dμ = ∫div_M Y_ρ dμ = 0.)
6. Vanishing (book lines 720–735). For every admissible φ, |I(ρ)| ≤ (sup φ)∫_{B_ρ(0)}|x|dμ ≤ (sup φ)ρμ(B_ρ(0)) = (sup φ)ρ^{n+1}μ(B_1(0)), so ρ^{−n}I(ρ) → 0 as ρ ↓ 0; the constant is 0 and I(ρ) = 0 for all ρ > 0. Take φ_k(s) := χ(k(1 − s)) with χ ∈ C¹ nondecreasing, χ = 0 on (−∞, 1/2], χ = 1 on [1, ∞): φ_k is admissible (φ_k = 1 on (−∞, 1 − 1/k], φ_k = 0 on [1 − 1/(2k), ∞)) and φ_k(s) ↑ 1_{s<1}; dominated convergence (|h|1_{B_ρ(0)} ∈ L¹(μ)) gives ∫_{B_ρ(0)} h dμ = 0 for every ρ > 0.
7. Conclusion (book line 737). spt C ⊆ closure H = {h ≥ 0} and μ(ℝ^P ∖ spt μ) = 0, so h ≥ 0 μ-a.e.; with step 6, h = 0 μ-a.e. on every B_ρ(0), so μ({h > 0}) = 0. The open set {h > 0} therefore does not meet spt μ = spt C, and spt C ⊆ {h ≥ 0} ∩ {h ≤ 0} = {h = 0} = frontier H, i.e. C.support ⊆ frontier {x | 0 < ⟪v, x⟫}.

## Key steps

1. Stationarity (sibling, U = N = ℝ^P); the cone property gives D^⊥r = 0 a.e.
2. First variation of φ(r/ρ)h(x)x gives d/dρ[ρ^{−n}∫hφ(r/ρ)dμ] = +ρ^{−n−1}∫(x·∇^M h)φ(r/ρ)dμ.
3. The right side is ∫div_M(Ψ_ρ(r)e)dμ = 0 with Ψ_ρ'(s) = sφ(s/ρ); the ratio is constant, hence 0.
4. ∫_{B_ρ}h dμ = 0 and h ≥ 0 on spt C give spt C ⊆ {h = 0} = frontier H.

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
