# Parent-supplied natural-language proof

- Parent DAG node: `root.submanifold_tangent-a1`
- Child DAG node: `root.submanifold_tangent-a1.tangent_space_eq_range-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2–4 of the parent-supplied proof of simon_submanifold_tangent_basics. This is Simon, Introduction to GMT, Ch. 2, 4.3, p. 55: T_yM is a linear subspace with basis D₁ψ(x), …, D_nψ(x); the printed text only says 'one readily checks'. Step 1 of the parent proof (continuity of ψ⁻¹ on W ∩ M) is the sibling theorem chart_inverse_continuous, used in step 7 below.

Setting and notation. Fix x₀ ∈ V. Put y₀ := ψ(x₀), A := Dψ(x₀) = fderiv ℝ ψ x₀, and T := range A, a linear subspace of ℝᴺ. Let G be the set of generators of tangentSpace M y₀: v ∈ G iff there is γ : ℝ → ℝᴺ that is C¹ on (−1,1), maps (−1,1) into M, has γ(0) = y₀ and has derivative v at 0. Thus tangentSpace M y₀ = span G. Note that y₀ ∈ ψ(V) = W ∩ M.

Proof.
1. Differentiability. V is open and ψ is C^r on V with r ≥ 1, so ψ is C¹ on V and differentiable at every point x of V, with derivative fderiv ℝ ψ x. Write e(x) := ψ(x) − ψ(x₀) − A(x − x₀). Then for every ε > 0 there is δ_ε > 0 with |e(x)| ≤ ε|x − x₀| whenever |x − x₀| < δ_ε.

Part A: T ⊆ tangentSpace M y₀.
2. Let w ∈ ℝⁿ. If w = 0, then Aw = 0 ∈ tangentSpace M y₀. Now let w ≠ 0. Choose ρ > 0 with B(x₀, ρ) ⊆ V, which is possible because V is open. Put c := ρ/(2|w|) > 0, ℓ(t) := x₀ + c t w and γ(t) := ψ(ℓ(t)) for t ∈ ℝ.
3. For t ∈ (−1,1), |ℓ(t) − x₀| = c|t||w| < ρ/2, so ℓ(t) ∈ V and γ(t) ∈ ψ(V) = W ∩ M ⊆ M. The affine map ℓ is C^∞ and maps (−1,1) into V, and ψ is C¹ on V, so γ = ψ ∘ ℓ is C¹ on (−1,1). Also γ(0) = ψ(x₀) = y₀.
4. We have ℓ(0) = x₀ and ℓ′(0) = c w, and ψ is differentiable at x₀ with derivative A. The chain rule gives γ′(0) = A(c w) = c·Aw. Hence c·Aw ∈ G ⊆ tangentSpace M y₀. Since tangentSpace M y₀ is a linear subspace, Aw = c⁻¹·(c·Aw) ∈ tangentSpace M y₀. Thus T ⊆ tangentSpace M y₀.

Part B: tangentSpace M y₀ ⊆ T.
5. T is a linear subspace and tangentSpace M y₀ = span G, so it suffices to show G ⊆ T. Let v ∈ G, witnessed by γ: C¹ on (−1,1), γ((−1,1)) ⊆ M, γ(0) = y₀, and derivative v at 0.
6. γ is differentiable, hence continuous, at 0. Since γ(0) = y₀ ∈ W and W is open, there is τ ∈ (0,1) with γ(t) ∈ W for |t| < τ. Also γ(t) ∈ M for |t| < 1, so γ(t) ∈ W ∩ M for |t| < τ.
7. Let g := Function.invFunOn ψ V and c(t) := g(γ(t)). For |t| < τ, γ(t) ∈ W ∩ M = ψ(V), hence c(t) ∈ V and ψ(c(t)) = γ(t). Also c(0) = g(ψ(x₀)) = x₀, because ψ is injective on V. By chart_inverse_continuous, g is continuous on W ∩ M. Since γ(t) → y₀ as t → 0 and γ(t) ∈ W ∩ M for |t| < τ, we get c(t) → g(y₀) = x₀ as t → 0.
8. A is injective and ℝⁿ is finite-dimensional, so there is λ > 0 with |Aζ| ≥ λ|ζ| for all ζ ∈ ℝⁿ. Indeed, if n = 0 take λ = 1. Otherwise ζ ↦ |Aζ| is continuous and, by injectivity, positive on the compact nonempty unit sphere, so it has a positive minimum λ there; apply this to ζ/|ζ| for ζ ≠ 0.
9. By step 7 there is τ₁ ∈ (0, τ] with |c(t) − x₀| < δ_{λ/2} for |t| < τ₁. For such t, using ψ(c(t)) = γ(t), step 1 with ε = λ/2, and step 8:
|γ(t) − γ(0)| = |A(c(t) − x₀) + e(c(t))| ≥ λ|c(t) − x₀| − (λ/2)|c(t) − x₀| = (λ/2)|c(t) − x₀|.
Since γ has derivative v at 0, there is τ₂ ∈ (0, τ₁] with |γ(t) − γ(0) − t v| ≤ |t| for |t| < τ₂, so |γ(t) − γ(0)| ≤ (|v| + 1)|t|. Hence ζ(t) := t⁻¹(c(t) − x₀) satisfies |ζ(t)| ≤ C := 2(|v| + 1)/λ for 0 < |t| < τ₂.
10. Let t_j := τ₂/(j + 2) for j ∈ ℕ. Then 0 < t_j < τ₂, t_j → 0 and |ζ(t_j)| ≤ C. By Bolzano–Weierstrass in ℝⁿ, some subsequence s_k := t_{j_k} has ζ(s_k) → ζ for a point ζ ∈ ℝⁿ. Still s_k ≠ 0 and s_k → 0.
11. For every k, |s_k| < τ, so γ(s_k) = ψ(c(s_k)) and
(γ(s_k) − γ(0))/s_k = (A(c(s_k) − x₀) + e(c(s_k)))/s_k = Aζ(s_k) + e(c(s_k))/s_k.
(a) The left side tends to v, because γ has derivative v at 0, s_k → 0 and s_k ≠ 0.
(b) Aζ(s_k) → Aζ, because A is linear on the finite-dimensional ℝⁿ, hence continuous.
(c) e(c(s_k))/s_k → 0. Given ε > 0, c(s_k) → x₀ by step 7, so |c(s_k) − x₀| < δ_ε for large k. Then |e(c(s_k))/s_k| ≤ ε|c(s_k) − x₀|/|s_k| = ε|ζ(s_k)| ≤ εC.
By uniqueness of limits in ℝᴺ, v = Aζ ∈ T. Hence G ⊆ T, and tangentSpace M y₀ = span G ⊆ T.
12. Conclusion. Parts A and B give tangentSpace M (ψ x₀) = T = LinearMap.range (fderiv ℝ ψ x₀).toLinearMap. Since x₀ ∈ V, and n, N, r, M, V, W, ψ, were arbitrary, the theorem follows.

Formal references (Mathlib): ContDiffOn.differentiableOn, DifferentiableOn.differentiableAt, ContDiffOn.comp, HasFDerivAt.comp_hasDerivAt (Analysis/Calculus/Deriv/Comp.lean:374), Submodule.span_le, Submodule.subset_span, Submodule.smul_mem, Function.invFunOn_mem and Function.invFunOn_eq. For step 8: LinearMap.exists_antilipschitzWith (Analysis/Normed/Module/FiniteDimension.lean:231). For step 10: tendsto_subseq_of_bounded (Topology/MetricSpace/Sequences.lean:38).

## Key steps

1. ψ is C¹ on the open set V, so it is differentiable at x₀ with derivative A = Dψ(x₀) and remainder e(x) = o(|x − x₀|).
2. range A ⊆ T_{y₀}M: for w ≠ 0, the curve t ↦ ψ(x₀ + c t w) with c = ρ/(2|w|) is C¹ on (−1,1), stays in ψ(V) ⊆ M, and has velocity c·Aw; then divide by c.
3. T_{y₀}M ⊆ range A, setup: for a generating curve γ, γ(t) ∈ W ∩ M near 0, and the lift c(t) = invFunOn ψ V (γ(t)) tends to x₀ by chart_inverse_continuous.
4. Injectivity of A gives |Aζ| ≥ λ|ζ|, hence (λ/2)|c(t) − x₀| ≤ |γ(t) − γ(0)| ≤ (|v| + 1)|t|, so ζ(t) = (c(t) − x₀)/t is bounded.
5. Along a Bolzano–Weierstrass subsequence s_k → 0, the quotient (γ(s_k) − γ(0))/s_k = Aζ(s_k) + e(c(s_k))/s_k tends to both v and Aζ. So v = Aζ ∈ range A, and taking spans finishes the inclusion.

## Reference use

### local-project

Queries:
- `rg -n '^def tangentSpace|^def tangentProjection|^abbrev Rn' project/GMT/Ch02/Contract.lean`
- `rg -n 'Submission\.' project`
- `rg -n 'isEmbedding_chartMap|exists_open_image_eq_inter|IsSimonLocalRepresentation\.|IsSimonSubmanifold\.' lake-packages-25730c7c/simongmt (then full reads of Chapter02/Submanifold.lean and Chapter02/SubmanifoldTopology.lean)`
- `rg -n 'starProjection|orthogonalProjection' -l lake-packages-25730c7c/simongmt/Poincare; sed -n 780,900p Chapter08/Varifold.lean`
- `rg -n 'theorem IsLocallyClosed\.(measurableSet|nullMeasurableSet)|IsLocallyClosed.measurableSet' mathlib/Mathlib; rg -n '^theorem|^lemma' mathlib/Mathlib/Topology/LocallyClosed.lean`
- `rg -n 'class HasOrthogonalProjection|def starProjection|theorem eq_starProjection_of_mem_of_inner_eq_zero|isSymmetricProjection_iff_eq_coe_starProjection_range' mathlib/Mathlib/Analysis/InnerProductSpace/`
- `rg -n 'theorem inverse_continuousAt' mathlib/Mathlib/Analysis/Normed/Ring/Units.lean; rg -n '^def adjoint|theorem adjoint_inner_left' mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `rg -n 'theorem ContDiffOn.continuousOn_fderiv_of_isOpen|theorem ContDiffOn.differentiableOn' mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `rg -n '^noncomputable def invFunOn|^theorem invFunOn_mem|^theorem invFunOn_eq|^theorem InjOn.leftInvOn_invFunOn' mathlib/Mathlib/Data/Set/Function.lean`
- `rg -n 'theorem tendsto_subseq_of_bounded|theorem IsCompact.tendsto_subseq |theorem mem_closure_iff_seq_limit|theorem isOpen_iUnion_countable|theorem continuousWithinAt_inter |exists_antilipschitzWith|theorem ContinuousLinearMap.isOpen_injective|theorem HasFDerivAt.comp_hasDerivAt ' mathlib/Mathlib`
- `python3 -I gen_checks.py (loads verifier/gmt-compare.py child_modules + contract_scope and verifier/lean_contract.py validate_lean_statement) on the five lean_statements; lake env lean final/NodeChallenge_00..04.lean against a scratch build of GMT.Ch02.Submission`
- `lake env lean final/FinalAssembly.lean (real proofs of chart_inverse_continuous, range_projection_continuous, submanifold_measurable; sorried tangent_space_eq_range; tangent_projection_continuous from siblings; parent frozen type assembled; #print axioms)`
- `python3 -I lean_name scan of dag.json; grep lean_name nodes/*/decomposition-v*.json; rg -l 'simon_submanifold_' lake-packages-25730c7c/simongmt/Poincare; git grep -l 'simon_submanifold_' (snapshot mathlib)`
- `sed -n 845,875p book/chapter-02.txt (printed Simon 4.1-4.3)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Data/Set/Function.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/ContinuousOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/LocallyClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-submanifold-tangent-a1/parent-child-handoff.json`
- `/tmp/gmt-ch02-subtan-r3I2jM/final/FinalAssembly.lean`

Contract.lean:48/86/91 fixes Rn, tangentSpace (the span of velocities of C¹ curves (−1,1) → M) and tangentProjection (Submodule.starProjection). The project snapshot has no Submission.* declarations. The pinned SimonGMT Submanifold.lean (IsProperOnInto:30, IsSimonLocalRepresentation:37, IsSimonSubmanifold:48) matches the hypotheses used by every child. SubmanifoldTopology.lean proves isProperMap_chartMap:54, isEmbedding_chartMap:90 and exists_open_image_eq_inter:100, which state chart_inverse_continuous in closed-embedding form. That module is not imported by the Contract, but a child file under GMT/Ch02 may import it. SimonGMT has no tangentSpace = range Dψ theorem, no measurability theorem for submanifolds, and no continuity theorem for range projections. Its Chapter08/Varifold.lean projection formula is specific to matrices and its Grassmannian. Mathlib supplies everything the children need: HasOrthogonalProjection (a Prop class, Projection/Basic.lean:48), starProjection:131, eq_starProjection_of_mem_of_inner_eq_zero:180, ContinuousLinearMap.adjoint (Adjoint.lean:112), NormedRing.inverse_continuousAt (Normed/Ring/Units.lean:183), ContDiffOn.continuousOn_fderiv_of_isOpen (ContDiff/Defs.lean:916), invFunOn and its lemmas (Data/Set/Function.lean:953-987), tendsto_subseq_of_bounded (MetricSpace/Sequences.lean:38), IsCompact.tendsto_subseq (Sequences.lean:298), mem_closure_iff_seq_limit (Sequences.lean:108), isOpen_iUnion_countable (Bases.lean:932), continuousWithinAt_inter (ContinuousOn.lean:259), LinearMap.exists_antilipschitzWith (FiniteDimension.lean:231) and HasFDerivAt.comp_hasDerivAt (Deriv/Comp.lean:374). Mathlib has no IsLocallyClosed.measurableSet. All five child statements elaborate in the comparator's replayed Contract scope, and the frozen parent type follows from them by a one-line term. Scratch Lean proofs of chart_inverse_continuous, range_projection_continuous and submanifold_measurable depend only on propext, Classical.choice and Quot.sound. tangent_projection_continuous compiles from its three sibling statements. No proposed lean_name collides with dag.json (41 nodes), with pending decompositions, or with SimonGMT or Mathlib.
