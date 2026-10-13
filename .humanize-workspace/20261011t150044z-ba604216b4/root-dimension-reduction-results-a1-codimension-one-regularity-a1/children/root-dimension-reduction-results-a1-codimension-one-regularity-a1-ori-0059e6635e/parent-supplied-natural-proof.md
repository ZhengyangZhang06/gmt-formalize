# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.oriented_piece_mass-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon Ch. 6, 2.5 (the mass M_W) and 3.2(3) (for an integer multiplicity current, M_W(T) = μ_T(W)); chapter-06.txt lines 224–240 and 755–770. This is the argument of the facts (G5c) and (G6) of the previously reviewed analytic core of this node, written once with a general weight θ' in place of a constant multiplicity, so that the three analytic children region_density_one, simons_regular_cone and low_density_regular can cite it instead of re-proving it. It is needed because those children cannot use the parent's sibling im_mass_measure, and because they apply it to local pieces c·[[M']] that are not given by a global integer multiplicity representation.

Sibling child used (an accepted declaration, reused with its identical frozen type):
- unit_orientation_dual (Submission.dor_ims_unitOrientation_dual): for all P, k there is a continuous linear map L : Λ_k(ℝ^P) → Λ^k(ℝ^P) (MultiVector P k →L[ℝ] Covector (Euclid P) k) such that for every ξ that is a unit orientation of some subspace Q (IsUnitOrientationOf ξ Q): (a) |ξ(α)| ≤ |α| for every k-covector α; (b) |L(ξ)| ≤ 1; (c) ξ(L(ξ)) = 1.

Notation.
- H^k := μHE[k]; Λ^k := Covector (Euclid P) k, a finite-dimensional real vector space; |α| := covectorEuclideanNorm α, the Euclidean coefficient norm, which is a norm on Λ^k (it is the Euclidean norm of the coordinate vector (α(e_{I_1}, …, e_{I_k}))_{I strictly increasing}, and these coordinates determine α by multilinearity and alternation).
- For an open W ⊆ V put I(W) := ∫⁻_{M'∩W} ofReal(θ') dH^k ∈ [0, ∞]. Since θ' ≥ 0, ofReal(θ') = θ'.
- M_W(T) = T.massOn W = sup{ofReal(T(ω)) : ω ∈ 𝒟^k(U), tsupport ω ⊆ W, |ω(x)| ≤ 1 for all x}; such ω are called admissible for M_W(T).

Proof. Fix the data and hypotheses of the statement and an open W ⊆ V.

1. (Pointwise facts.) Let L be the map of unit_orientation_dual for (P, k). Let G ⊆ M' be the set of x ∈ M' at which ξ'(x) is a unit orientation of some subspace. By hypothesis M' ∖ G is contained in a Borel set Z with H^k(Z ∩ M') = 0. For every x ∈ G:
 (1a) |ξ'(x)(α)| ≤ |α| for every α ∈ Λ^k;
 (1b) |L(ξ'(x))| ≤ 1;
 (1c) ξ'(x)(L(ξ'(x))) = 1.

2. (Upper bound: M_W(T) ≤ I(W).) If I(W) = ∞ there is nothing to prove; assume I(W) < ∞. Let ω be admissible for M_W(T).
- tsupport ω ⊆ W ⊆ V, so the hypothesis gives T(ω) = ∫_{M'} g dH^k with g(x) := θ'(x)·ξ'(x)(ω(x)).
- Let x ∈ G. If x ∉ W, then x ∉ tsupport ω, so ω(x) = 0 and g(x) = 0. If x ∈ W, then |g(x)| ≤ θ'(x)|ω(x)| ≤ θ'(x) by (1a). Hence |g| ≤ θ'·1_W at H^k-a.e. point of M'.
- θ'·1_W is integrable on M' with integral I(W) < ∞ (θ' ≥ 0 is measurable and W is Borel). So g is integrable on M' and T(ω) = ∫_{M'} g dH^k ≤ ∫_{M'} θ'1_W dH^k = I(W).
- Hence ofReal(T(ω)) ≤ I(W), and taking the supremum over admissible ω gives M_W(T) ≤ I(W).
This proves the first conclusion.

3. (Lower bound when I(W) < ∞.) Assume I(W) < ∞ and fix ε > 0.
(3a) ν := θ'·H^k⌞(M' ∩ W), i.e. ν(A) = ∫⁻_{M'∩W∩A} θ' dH^k, is a finite Borel measure on ℝ^P with ν(ℝ^P) = I(W). A finite Borel measure on the Polish space ℝ^P is inner regular with respect to compact sets. Moreover ν(Z) = 0, because ν ≪ H^k⌞M'.
(3b) (Lusin.) The map h := L∘ξ' : ℝ^P → Λ^k is ν-a.e. strongly measurable, since L is continuous, ξ' is a.e. strongly measurable for H^k⌞M', and ν ≪ H^k⌞M'. By Lusin's theorem for the finite inner regular measure ν and the map h into the finite-dimensional space Λ^k, applied inside the Borel set (M' ∩ W) ∖ Z, there is a compact K ⊆ (M' ∩ W) ∖ Z ⊆ G ∩ W with ν((M' ∩ W) ∖ K) < ε such that h restricted to K is continuous.
(3c) (Extension.) Fix a basis of Λ^k and apply the Tietze extension theorem to each coordinate of h|_K. This gives a continuous α₀ : ℝ^P → Λ^k with α₀ = h on K. Put α₁(y) := α₀(y)/max{1, |α₀(y)|}. Then α₁ is continuous, |α₁| ≤ 1 everywhere, and α₁ = h on K, because |h| ≤ 1 on K ⊆ G by (1b).
(3d) (Smoothing.) Let ρ_j ≥ 0 be smooth with ∫ρ_j = 1 and support in B_{1/j}(0), and put α_j := α₁ * ρ_j (coordinatewise convolution). Each α_j is smooth; |α_j(y)| ≤ ∫|α₁(y − z)|ρ_j(z) dz ≤ 1 because |·| is a norm; and α_j(y) → α₁(y) for every y, by continuity of α₁.
(3e) (Cut-off.) K is a compact subset of the open set W. By the smooth Urysohn lemma choose φ ∈ C^∞(ℝ^P) with 0 ≤ φ ≤ 1, φ = 1 on K, and tsupport φ a compact subset of W. Put ω_j := φ·α_j. Then ω_j is a smooth k-form with compact tsupport ω_j ⊆ tsupport φ ⊆ W ⊆ V ⊆ U, so ω_j ∈ 𝒟^k(U), and |ω_j| ≤ φ|α_j| ≤ 1. Thus ω_j is admissible for M_W(T), and ofReal(T(ω_j)) ≤ M_W(T) for every j.
(3f) (Passage to the limit.) By hypothesis T(ω_j) = ∫_{M'} θ'φ·ξ'(α_j) dH^k (the integrand evaluated at x is θ'(x)φ(x)ξ'(x)(α_j(x))). For x ∈ G the integrand is bounded by θ'(x)1_W(x), by (1a), |α_j| ≤ 1 and φ = 0 off W; this dominant is integrable on M' with integral I(W) < ∞. The integrand converges pointwise to θ'φ·ξ'(α₁), since each ξ'(x) is continuous. By dominated convergence, T(ω_j) → J := ∫_{M'} θ'φ·ξ'(α₁) dH^k.
(3g) (Estimate of J.) Off W the integrand of J vanishes because φ = 0 there. On K we have φ = 1 and α₁ = L(ξ'), so the integrand equals θ' by (1c). At H^k-a.e. point of (M' ∩ W) ∖ K the integrand is ≥ −θ', by (1a), |α₁| ≤ 1 and 0 ≤ φ ≤ 1. Hence
 J ≥ ν(K) − ν((M' ∩ W) ∖ K) ≥ (I(W) − ε) − ε = I(W) − 2ε.
(3h) ofReal is continuous, so ofReal(J) = lim ofReal(T(ω_j)) ≤ M_W(T). Hence M_W(T) ≥ ofReal(I(W) − 2ε) for every ε > 0, and M_W(T) ≥ I(W).
Together with step 2, M_W(T) = I(W) whenever I(W) < ∞. This proves the second conclusion. ∎

## Key steps

1. unit_orientation_dual gives, a.e. on M', |ξ'(α)| ≤ |α| and a continuous dual L with |L(ξ')| ≤ 1, ξ'(L(ξ')) = 1.
2. Upper bound: for admissible ω supported in W, |θ'ξ'(ω)| ≤ θ'1_W a.e. on M', so T(ω) ≤ I(W) and M_W(T) ≤ I(W).
3. Lower bound when I(W) < ∞: Lusin for the finite measure θ'H^k⌞(M' ∩ W) gives a compact K with small complement on which L∘ξ' is continuous; Tietze, normalization, mollification and a smooth cut-off equal to 1 on K give admissible forms ω_j.
4. Dominated convergence gives T(ω_j) → J ≥ I(W) − 2ε; hence M_W(T) ≥ I(W), and equality holds.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; grep -n simongmt -A4 local-references/123e8435b4a2469b/project/lake-manifest.json`
- `sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `grep -n 'theorem finrank_add_inf_finrank_orthogonal|theorem IsCompact.tendsto_subseq|theorem isOpen_iUnion_countable' local-references/123e8435b4a2469b/mathlib/Mathlib/{Analysis/InnerProductSpace/Projection/FiniteDimensional,Topology/Sequences,Topology/Bases}.lean`
- `grep -n 'def massOn|massOn_mono|def zeroRegion|def support|Zero (GeometricCurrentOn' simongmt/Poincare/SimonGMT/Chapter06/{Mass,CurrentLocalEquality,Currents}.lean`
- `grep -rn 'theorem <name>' simongmt/Poincare/SimonGMT for bvVariationOn_le_liminf_of_locallyL1, cone_simonsDefect_lower_bound, exists_final_exponent, injective_area_formula_of_injective_derivative, exteriorDerivative_affinePullbackForm, tsupport_exteriorDerivative_subset, exteriorDerivative_sq, simonsDefect_eq_sum_skew, four_mul_radialSkewSum_le, WeakDerivativesZero.ae_eq_const`
- `header of simongmt Chapter03/FinitePerimeter.lean and Chapter05/Basic.lean; grep -rln 'Allard|DeGiorgi|BVCompact' simongmt/Poincare/SimonGMT`
- `python3 scan of dag.json: statuses and frozen types of the 8 siblings, the 5 reused names, the 6 new codim1_ names, the root theorems DensityAndTangentCones, DensityOneImpliesRegular, MinimizingImpliesStationary and dor_stationary_cycle_epsilon_regularity; keyword scan for overlapping nodes (regcomp_codim_one_preliminaries, regcomp_cop_region_support_subset, regcomp_cop_region_boundary_vanishes)`
- `for r in $(git for-each-ref refs/heads refs/remotes): git grep -l codim1_ $r -- 'GMT/*.lean' (2056 refs, no match)`
- `lean -DautoImplicit=false /tmp/codim1-v6/check/Types.lean; lean -DautoImplicit=false /tmp/codim1-v6/check/Assembly.lean (LEAN_PATH taken from .lake/build/lib/lean/GMT/Ch07/Submission.trace)`
- `ps -eo pid,lstart,args; max_nodes timeline over .humanize/swarm-configs; /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py _decompose, _solve_children, _existing_lean_name_problem, _install_parent_supplied_child_handoff; store.py ensure`
- `sed -n 560,1000p book/sources/chapter-07-source.txt (7.4–7.5.8); sed -n 1286,1330p book/sources/chapter-02-source.txt (5.6–5.8); sed -n 1300,1370p book/sources/chapter-05-source.txt (Theorem 7.1)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/FinitePerimeter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter05/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/ConeDefect.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/SimonsInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1/decomposition-v5.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1/decomposition-audit-v5.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-07-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-02-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-05-source.txt`
- `/tmp/codim1-v6/check/Types.lean`
- `/tmp/codim1-v6/check/Assembly.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/33c6cc03ee394bfbb35f84931b68580c.json`

Pins match. The snapshot manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib; the snapshot lake-manifest pins simongmt 2b366308, equal to .lake/packages/simongmt. The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…), so the frozen types of this node and of the 8 siblings are unchanged since v5.
Library.
- The snapshot Mathlib has finrank_add_inf_finrank_orthogonal (FiniteDimensional.lean:89), IsCompact.tendsto_subseq (Sequences.lean:298) and isOpen_iUnion_countable (Bases.lean:932); the glue uses all three.
- SimonGMT supplies massOn and massOn_mono, support = U \ zeroRegion and the zero current (Chapter06). It also supplies BV lower semicontinuity (Chapter02/BV.lean:225), the Simons algebra (AppendixB/ConeDefect.lean:228, SimonsInequalities.lean:88), and the area-formula, exterior-derivative and affine-pullback lemmas cited by the children.
- Its headers state that De Giorgi's theorem (Chapter03/FinitePerimeter.lean) and Allard's theorem (Chapter05/Basic.lean) are not provided, and no BV compactness theorem exists. These remain book citations inside the children.
DAG.
- The 5 reused declarations are accepted with byte-identical types.
- DensityAndTangentCones, DensityOneImpliesRegular, MinimizingImpliesStationary and dor_stationary_cycle_epsilon_regularity are not accepted, so they cannot be reused.
- regcomp_codim_one_preliminaries and its children overlap region_support_cycle, but they are unaccepted and have other types.
- The 6 new codim1_ names are free in dag.json, GMT/, SimonGMT and all 2056 refs.
Lean.
- Types.lean elaborates all 11 child types (exit 0, only sorry warnings).
- Assembly.lean proves CodimensionOneRegularity from the 8 sibling and 11 child types taken as axioms (exit 0). Its axioms are propext, Classical.choice, Quot.sound, 5 new children and 7 siblings; no root proposition occurs.
Infrastructure. The current controller (pid 23222) runs with max_nodes = 1000 and dag.json has 457 nodes, so the 6 new nodes can be activated. The accepted v5 was dropped by the old controller, which had max_nodes = 200 loaded.
