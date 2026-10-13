# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.retraction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1(a) of the parent proof (nearest point retraction, tubular neighbourhood theorem: Foote, Proc. AMS 92 (1984) 153–155; Leobacher–Steinicke, Ann. Global Anal. Geom. 60 (2021), arXiv:1811.10578), written out from a chart. The witness π is constructed below as the nearest point retraction onto N near y. Nearestness is a feature of this construction, used only inside the proof; the statement exports exactly the five listed properties. The hypothesis (N̄ ∖ N) ∩ U = ∅ is not needed. B_s := B_s(y); |·| is the Euclidean norm and ‖·‖ the operator norm.
1. Chart. By IsEmbeddedSubmanifold 2 d N at y there are open V ⊆ ℝ^d, open W ∋ y and ψ with the following properties: ψ is C² on V and injective on V; ψ(V) = W ∩ N; V ∩ ψ⁻¹(K) is compact for every compact K ⊆ W; Dψ(v) is injective for v ∈ V. Let v₀ ∈ V with ψ(v₀) = y. The map ψ|_V : V → W ∩ N is a homeomorphism: it is continuous and injective, and closed because it is proper into W.
2. Tangent projections.
 (a) For v ∈ V let D(v) := Dψ(v) (C¹ in v) and G(v) := D(v)ᵀD(v) (invertible). Then P̂(v) := D(v)G(v)⁻¹D(v)ᵀ is the orthogonal projection onto range D(v), and P̂ is C¹ on V.
 (b) Fix a closed ball V₀ := B̄_{s₀}(v₀) ⊆ V. Put a := sup_{V₀}‖DP̂‖ < ∞ and b := sup_{v∈V₀}‖G(v)⁻¹D(v)ᵀ‖ < ∞. Since G⁻¹Dᵀ is a left inverse of D, |w| ≤ b|D(v)w| for v ∈ V₀ and w ∈ ℝ^d.
3. Normal coordinates.
 (a) Let E := (range D(v₀))^⊥ (dimension P − d) and Φ : V × E → ℝ^P, Φ(v, e) := ψ(v) + (I − P̂(v))e. Φ is C¹, and DΦ(v₀, 0)(w, e) = D(v₀)w + e is an isomorphism ℝ^d × E → ℝ^P.
 (b) By the inverse function theorem (Mathlib ContDiffAt.toOpenPartialHomeomorph) there is δ₁ ∈ (0, s₀] with the following properties, where V₁ := B_{δ₁}(v₀) and E_{δ₁} := E ∩ B_{δ₁}(0): Φ is injective on V₁ × E_{δ₁}; O := Φ(V₁ × E_{δ₁}) is open; and Φ⁻¹ : O → V₁ × E_{δ₁} is C¹.
 (c) Shrink δ₁ further so that, for v ∈ V₁, the map (I − P̂(v))|_E : E → (range D(v))^⊥ is a linear isomorphism whose inverse has norm ≤ 2. This is possible because the map is the identity of E at v₀, depends continuously on v, and the dimensions agree.
4. Radii.
 (a) ψ⁻¹ : W ∩ N → V is continuous at y. So there is ρ₁ > 0 with B̄_{ρ₁} ⊆ W ∩ U and N ∩ B̄_{ρ₁} ⊆ ψ(V₁). Moreover N ∩ B̄_{ρ₁} = ψ(V ∩ ψ⁻¹(B̄_{ρ₁})) is compact.
 (b) Let r' := min(ρ₁/2, δ₁/4). Choose r ∈ (0, r'] with B̄_r ⊆ U and 2abr ≤ 1. Put β := ab and c := 2β ≥ 0.
5. Nearest points. Let x ∈ B_{r'}.
 (a) Existence and location. Points of N ∖ B̄_{ρ₁} have distance > ρ₁ − r' ≥ r' > |x − y| ≥ dist(x, N) from x. So dist(x, N) is attained on the compact set N ∩ B̄_{ρ₁}. Every nearest point p satisfies |p − x| ≤ |x − y| and |p − y| ≤ 2|x − y| < ρ₁, so p = ψ(v) with v ∈ V₁.
 (b) Normality. The function w ↦ |x − ψ(w)|² has a local minimum at v, so D(v)ᵀ(x − p) = 0. Thus ν := x − p ⊥ range D(v) and P̂(v)ν = 0.
 (c) Uniqueness. By 3(c), ν = (I − P̂(v))e for a unique e ∈ E with |e| ≤ 2|ν| < 2r' ≤ δ₁/2. So x = Φ(v, e) with (v, e) ∈ V₁ × E_{δ₁}. As Φ is injective there, (v, e) = Φ⁻¹(x) is determined by x: the nearest point is unique, and B_{r'} ⊆ O.
 (d) Definition. Put π(x) := ψ(pr₁Φ⁻¹(x)), the nearest point of x in N. For x ∉ B_{r'} put π(x) := x.
6. Properties.
 (a) π is C¹ on B_{r'} ⊇ B_r, as a composition of C¹ maps, and π(B_{r'}) ⊆ ψ(V₁) ⊆ N.
 (b) If x ∈ N ∩ B_{r'}, then x is its own nearest point, so π(x) = x.
 (c) Let x ∈ N ∩ B_r and v ∈ tangentSpace N x. There is γ, C¹ on (−1,1), with γ((−1,1)) ⊆ N, γ(0) = x and γ'(0) = v. For |s| small, γ(s) ∈ N ∩ B_r, so π(γ(s)) = γ(s). Since π is differentiable at x, the chain rule gives Dπ(x)v = γ'(0) = v.
7. Derivative bound.
 (a) Let g := pr₁∘Φ⁻¹ on B_{r'} (C¹). Then π = ψ∘g on B_{r'}, and by step 5, F(x) := P̂(g(x))(x − ψ(g(x))) = 0 for all x ∈ B_{r'}.
 (b) Fix x ∈ B_r and h ∈ ℝ^P; put v := g(x), p := π(x) and ν := x − p, so |ν| ≤ |x − y|. Differentiating F at x in direction h gives [DP̂(v)(Dg(x)h)]ν + P̂(v)(h − Dπ(x)h) = 0.
 (c) Since Dπ(x)h = D(v)Dg(x)h ∈ range D(v), P̂(v)Dπ(x)h = Dπ(x)h. Hence Dπ(x)h = P̂(v)h + [DP̂(v)(Dg(x)h)]ν.
 (d) Using ‖P̂(v)‖ ≤ 1, ‖DP̂(v)‖ ≤ a and |Dg(x)h| ≤ b|Dπ(x)h|, we get |Dπ(x)h| ≤ |h| + β|ν||Dπ(x)h| ≤ |h| + β|x − y||Dπ(x)h|.
 (e) As β|x − y| < βr ≤ 1/2, ‖Dπ(x)‖ ≤ 1/(1 − β|x − y|) ≤ 1 + 2β|x − y| = 1 + c|x − y|, using 1/(1 − s) ≤ 1 + 2s for 0 ≤ s ≤ 1/2.
8. Conclusion. r > 0, c ≥ 0 and π have all the stated properties; B̄_r ⊆ U by the choice of r. The degenerate cases are included: for d = 0, N ∩ W = {y} and π ≡ y near y; for d = P, E = {0} and π = id near y. ∎

## Key steps

1. C² chart ψ at y; tangent projection P̂ = D(DᵀD)⁻¹Dᵀ is C¹; normal map Φ(v, e) = ψ(v) + (I − P̂(v))e is a local C¹ diffeomorphism (inverse function theorem).
2. Construction: near y every point has nearest points in a compact chart piece; normality plus injectivity of Φ give uniqueness, and the chosen witness π = ψ∘pr₁∘Φ⁻¹ is C¹ with values in N.
3. π = id on N; the chain rule along C¹ curves gives Dπ(x)v = v on T_xN.
4. Differentiating P̂(π(x))(x − π(x)) = 0 gives |Dπ(x)h| ≤ |h| + β|x − y||Dπ(x)h|, hence ‖Dπ(x)‖ ≤ 1 + 2β|x − y|.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `rg -c sorry local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean (1, the final main_theorem)`
- `rg -l -i 'slice|slicing|flat metric|flat norm|deformation theorem|nearest.point|tubular' simongmt/Poincare/SimonGMT local-references/123e8435b4a2469b/project -t lean`
- `rg -n 'def .*[Pp]ushforward' simongmt/Poincare/SimonGMT -t lean`
- `rg -n -i 'theorem .*area.*rectifiable|rectifiable.*area_formula|areaFormula.*Rectifiable' simongmt/Poincare/SimonGMT -t lean (no match)`
- `grep -n '^theorem|^def' simongmt Chapter02/AreaNoninjective.lean, Chapter03/{SubmanifoldCover,DisjointCover,Rectifiable,Differential}.lean, Chapter06/{Currents,Mass,CurrentLocalEquality,Forms}.lean`
- `grep -n 'measure_compl_support|hausdorffMeasure_image_le|norm_image_sub_le_of_norm_fderiv_le|toOpenPartialHomeomorph|exists_isCompact_diff_lt' in snapshot mathlib Support.lean, Hausdorff.lean, MeanValue.lean, InverseFunctionTheorem/ContDiff.lean, Regular.lean`
- `grep -rln 'def compContinuousLinearMap' snapshot mathlib Topology/Algebra/Module/Alternating`
- `dag.json lean_name scan for the eight proposed dor_lmb_* names (164 nodes at 2026-10-12T01:39Z; no collision); git grep dor_lmb over all branches (no match)`
- `python3 -I: verifier/lean_contract.py validate_lean_statement and verifier/gmt-compare.py contract_scope on all eight lean_statement strings`
- `lake env lean /tmp/lmb-decomp-v2/Types.lean (eight child types in the exact comparator scope, each also checked as `example : Prop`)`
- `lake env lean /tmp/lmb-decomp-v2/Assembly.lean (#print axioms Submission.dor_minimizing_limsup_mass_bound)`
- `lake env lean /tmp/lmb-decomp-v2/Inst.lean (implicit volume on ℝ, Measure.le_iff', ENNReal smul of measures)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaNoninjective.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Product.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DeformationIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1/decomposition-audit-v1.json`
- `/tmp/lmb-decomp-v2/v2_subproblems.json`
- `/tmp/lmb-decomp-v2/Types.lean`
- `/tmp/lmb-decomp-v2/Assembly.lean`
- `/tmp/lmb-decomp-v2/Inst.lean`

Snapshot: project b4d606d, mathlib 25730c7c; simongmt is pinned at 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. Its only sorry is main_theorem.

Reusable facts found:
- SimonGMT Chapter03/Rectifiable.lean: HasApproximateTangentSpaceAt (Simon 1.4, unweighted), .unique, CountablyRectifiable and CountablyRectifiable.mono.
- Chapter03/DisjointCover.lean: simon_remark_1_3 (disjoint Borel pieces).
- Chapter03/SubmanifoldCover.lean: countablyRectifiable_of_submanifold_cover, measurableSet_of_isSimonSubmanifold, countablyRectifiable_image_contDiffOn_open. Its header says the converse direction of Lemma 1.2 "remains a separate theorem".
- Chapter02/AreaNoninjective.lean: weighted_area_formula_lipschitz_fiberSum, a non-injective weighted Lipschitz area formula. It is for maps on a Euclidean domain, not on rectifiable subsets of ℝ^P.
- Chapter06: massOn and massAdmissibleOn (Mass.lean); support as U minus the zero region (CurrentLocalEquality.lean); GeometricCurrentOn with sequential continuity, and boundary (Currents.lean).
- Mathlib: measure_compl_support, LipschitzOnWith.hausdorffMeasure_image_le, Convex.norm_image_sub_le_of_norm_fderiv_le, ContDiffAt.toOpenPartialHomeomorph, MeasurableSet.exists_isCompact_diff_lt, ContinuousAlternatingMap.compContinuousLinearMap, μHE[d].

Not available, so cited from Simon in the child proofs:
- current slicing (6.4) and flat convergence (6.7.2): the keyword hits are only linear co-area slices, product point slices and varifold deformation slices;
- the Deformation Theorem (6.5.3) and completeness (6.3.13);
- C¹ or Lipschitz push-forward of currents: only affinePushforward and varifold push-forwards exist;
- the rectifiable-set area formula (Ch. 3, 2.6), the only-if direction of Lemma 1.2, and a nonlinear tubular-neighbourhood retraction.

Lean checks:
- All eight child types elaborate as Prop in the exact comparator scope and pass validate_lean_statement.
- The conditional assembly of the exact frozen parent type compiles. It depends only on propext, Classical.choice, Quot.sound and the stubs' sorryAx.
- No proposed name collides.
