# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_decay-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_decay-a1.planes_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 4 (Simon Ch. 5, proof of Theorem 5.2, displays (4)–(5), book/chapter-05.txt lines 1068–1077: "(4) evidently implies that there is S(ξ) (= lim S_ℓ) such that (5)"); in the parent this lemma is applied with q = θ₀ and a = C₁₀θ₀^{−n}E_*. Notation as in the statement; ⟨·,·⟩ is the inner product of E, and every x ∈ E is x = Σ_i x_i e_i with x_i = ⟨e_i, x⟩.
1. a ≥ 0. The hypothesis with j = 0 (q⁰ = 1) gives 0 ≤ d(p_{S_1}, p_{S_0}) ≤ a, a sum of squares being ≥ 0.
2. Put h := √q. Then h ≥ 0 and h² = q (as q ≥ 0), and h ≤ √(1/4) = 1/2 by monotonicity of √; so h < 1 and 1 − h ≥ 1/2. For every j, q^j = (h²)^j = (h^j)².
3. Hilbert–Schmidt vectors. Let 𝒱 := PiLp 2 (fun _ : Fin P => E), the P-tuples u = (u_i)_{i<P} of vectors of E with the ℓ²-norm, ‖u‖² = Σ_i ‖u_i‖² (Mathlib PiLp.norm_sq_eq_of_L2). 𝒱 is complete (a finite product of complete spaces; instance PiLp.completeSpace) and each coordinate map u ↦ u_i is continuous (PiLp.continuous_apply). For j ∈ ℕ let v_j := (p_{S_j}e_i)_{i<P} ∈ 𝒱 (WithLp.toLp 2 (fun i => p_{S_j} e_i)). As (v_j − v_k)_i = p_{S_j}e_i − p_{S_k}e_i, we have dist(v_j, v_k)² = ‖v_j − v_k‖² = Σ_i ‖p_{S_j}e_i − p_{S_k}e_i‖² = d(p_{S_j}, p_{S_k}) for all j, k; and d(A, B) = d(B, A) because ‖y − z‖ = ‖z − y‖.
4. Geometric bound. For every j, by Steps 1–3, dist(v_j, v_{j+1})² = d(p_{S_{j+1}}, p_{S_j}) ≤ a·q^j = (√a·h^j)², hence dist(v_j, v_{j+1}) ≤ √a·h^j, both sides being ≥ 0.
5. Convergence. Since 0 ≤ h < 1, Step 4 makes (v_j) a Cauchy sequence (Mathlib cauchySeq_of_le_geometric), so by completeness v_j → w for some w ∈ 𝒱. For m ≥ j the triangle inequality gives dist(v_j, v_m) ≤ Σ_{l=j}^{m−1} √a·h^l ≤ √a·h^j/(1 − h); letting m → ∞, dist(v_j, w) ≤ √a·h^j/(1 − h) (Mathlib dist_le_of_le_geometric_of_tendsto), and as 1 − h ≥ 1/2, dist(v_j, w) ≤ 2√a·h^j for every j. By continuity of the coordinate maps, p_{S_j}e_i → w_i as j → ∞, for every i < P.
6. The limit operator. Let L : E → E be the linear map with L e_i = w_i for all i, i.e. L x = Σ_i x_i w_i (in Lean (EuclideanSpace.basisFun (Fin P) ℝ).toBasis.constr ℝ (fun i => w i) — note WithLp is a structure, so the family of coordinates is fun i => w i — made a continuous linear map by LinearMap.toContinuousLinearMap since E is finite-dimensional; Basis.constr_basis gives L e_i = w_i). Every linear A : E → E satisfies A x = Σ_i x_i A e_i (expand x in the standard basis, OrthonormalBasis.sum_repr, and use linearity). Hence for every x ∈ E, p_{S_j}x = Σ_i x_i p_{S_j}e_i → Σ_i x_i w_i = L x as j → ∞, a finite sum of convergent sequences (Step 5).
7. L is idempotent. Fix x ∈ E. For each j, p_{S_j}x ∈ S_j and p_{S_j} fixes the vectors of S_j, so p_{S_j}(p_{S_j}x) = p_{S_j}x (Submodule.starProjection_eq_self_iff). Also ‖p_{S_j}(p_{S_j}x) − p_{S_j}(Lx)‖ = ‖p_{S_j}(p_{S_j}x − Lx)‖ ≤ ‖p_{S_j}x − Lx‖ → 0, because orthogonal projections do not increase norms (Submodule.norm_starProjection_apply_le), and p_{S_j}(Lx) → L(Lx) by Step 6 applied to the vector Lx. Hence p_{S_j}(p_{S_j}x) → L(Lx). But p_{S_j}(p_{S_j}x) = p_{S_j}x → Lx, so L(Lx) = Lx by uniqueness of limits.
8. L is symmetric. For x, y ∈ E and every j, ⟨p_{S_j}x, y⟩ = ⟨x, p_{S_j}y⟩ (orthogonal projections are self-adjoint, Submodule.inner_starProjection_left_eq_right). Letting j → ∞ and using Step 6 and continuity of the inner product, ⟨Lx, y⟩ = ⟨x, Ly⟩.
9. Identification. By Steps 7–8, L is idempotent and self-adjoint (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric), i.e. IsStarProjection L. A self-adjoint idempotent operator on a complete inner product space is the orthogonal projection onto its range (isStarProjection_iff_eq_starProjection_range). Put S' := range L; then L = p_{S'}.
10. dim S' = n. For every linear A : E → E, trace A = Σ_i ⟨e_i, A e_i⟩ (LinearMap.trace_eq_sum_inner with the orthonormal basis EuclideanSpace.basisFun (Fin P) ℝ, whose i-th vector is e_i). An idempotent linear map is the projection onto its range along its kernel, so its trace equals the dimension of its range (LinearMap.IsIdempotentElem.isProj_range and LinearMap.IsProj.trace). Each p_{S_j} is idempotent (Step 7) with range S_j (Submodule.range_starProjection), so trace p_{S_j} = dim S_j = n. By Step 6 and continuity of the inner product, trace p_{S_j} = Σ_i ⟨e_i, p_{S_j}e_i⟩ → Σ_i ⟨e_i, L e_i⟩ = trace L; since this sequence is constantly n, trace L = n. As L is idempotent (Step 7), trace L = dim(range L) = dim S'. Hence dim S' = n, the cast ℕ → ℝ being injective.
11. Tail bound. By Steps 6 and 9, w_i = L e_i = p_{S'}e_i for every i, i.e. w = (p_{S'}e_i)_i. Hence for every j, by Steps 3 and 5, d(p_{S'}, p_{S_j}) = Σ_i ‖p_{S'}e_i − p_{S_j}e_i‖² = ‖w − v_j‖² = dist(v_j, w)² ≤ (2√a·h^j)² = 4·a·(h²)^j = 4·a·q^j.
Steps 10 and 11 are the two conclusions. ∎

## Key steps

1. a ≥ 0 from the hypothesis at j = 0; h := √q ∈ [0, 1/2], q^j = (h^j)².
2. Vectorize: v_j := (p_{S_j}e_i)_i in the complete ℓ²-product PiLp 2; dist(v_j, v_k)² = d(p_{S_j}, p_{S_k}), so dist(v_j, v_{j+1}) ≤ √a·h^j.
3. Geometric Cauchy sequence: v_j → w with dist(v_j, w) ≤ √a·h^j/(1 − h) ≤ 2√a·h^j; columns p_{S_j}e_i → w_i.
4. L e_i := w_i gives p_{S_j}x → Lx for all x; L is idempotent and self-adjoint, hence L = p_{S'} with S' := range L.
5. dim S' = trace L = lim trace p_{S_j} = n (trace = Σ_i⟨e_i, A e_i⟩; trace of an idempotent = rank).
6. d(p_{S'}, p_{S_j}) = dist(v_j, w)² ≤ 4·a·q^j.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json  (mode local-project; project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean  (both identical)`
- `rg -n -i 'tilt|excess|hilbert.?schmidt|grassmann' <snapshot>/project/GMT --glob '*.lean'`
- `rg -n 'starProjection' <snapshot>/project/GMT --glob '*.lean'`
- `rg -n -i 'tendsto.*starProjection|starProjection.*tendsto|closed.*starProjection|isClosed.*IsStarProjection|IsStarProjection.*isClosed' <snapshot>/mathlib/Mathlib --glob '*.lean'`
- `rg -n 'IsStarProjection' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/`
- `rg -n 'theorem IsProj.trace|isProj_range|trace_eq_sum_inner|range_starProjection|isIdempotentElem_starProjection|inner_starProjection_left_eq_right|starProjection_eq_self_iff' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem norm_sq_eq_of_L2|instance completeSpace' <snapshot>/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean; rg -n 'theorem cauchySeq_of_le_geometric |theorem dist_le_of_le_geometric_of_tendsto ' <snapshot>/mathlib/Mathlib`
- `rg -n "theorem mul_le_mul_left'|theorem mul_le_mul_right" <snapshot>/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`
- `rg -n -i 'tilt|hilbert.?schmidt|hsNorm|grassmann' Poincare --glob '*.lean'; rg -n 'starProjection' Poincare | rg -i 'tendsto|limit|cauchy|finrank|trace'  (in lake-packages-25730c7c/simongmt at rev 2b3663083f3fe399b6296fb8eaee52169170e197)`
- `grep -rIl -e dorag_ted_planes_limit -e dorag_ted_hs_integral_compare over every workspace's .humanize JSON/MD; python3 lean_name scan of dag.json (216 nodes)  (no match)`
- `python3 -I lean_contract.validate_lean_statement and lean (v4.35.0-rc3, LEAN_PATH of the built workspace) on Challenge_<key>.lean in the verifier/gmt-compare.py contract_scope (open …; namespace GMT.Ch07; open …; noncomputable section; end)`
- `lean final/Solution_planes_limit.lean, final/Solution_hs_integral_compare.lean, final/Assembly.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Submodule.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Projection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter05/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-graph-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-722e7cab72/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/tmp/ted-decomp-k7q2/v1/Challenge_planes_limit.lean`
- `/tmp/ted-decomp-k7q2/v1/Challenge_hs_integral_compare.lean`
- `/tmp/ted-decomp-k7q2/v1/Challenge_PARENT.lean`
- `/tmp/ted-decomp-k7q2/final/Solution_planes_limit.lean`
- `/tmp/ted-decomp-k7q2/final/Solution_hs_integral_compare.lean`
- `/tmp/ted-decomp-k7q2/final/Assembly.lean`

The snapshot pins project b4d606d and Mathlib 25730c7c. Its GMT/Ch07/Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, which form the compiler context of the child types.

Nothing in the snapshot proves either child:
- The project's Ch05 tilt-excess objects (tiltExcess, tiltExcessStar, hsNormSq, TiltExcessDecayTheorem) are definitions used only in a main_theorem that is `sorry`.
- SimonGMT Chapter05/Basic.lean defines tiltEnergy and tiltExcess but states that excess decay is not formalized.
- Mathlib has only starProjection_tendsto_closure_iSup, which covers monotone families. It has no closedness result for rank-n star projections and no integrated Hilbert–Schmidt comparison.

The Mathlib API the child proofs need exists at the pin:
- isStarProjection_iff_eq_starProjection_range (Adjoint.lean);
- Submodule.range_starProjection, starProjection_eq_self_iff, inner_starProjection_left_eq_right, norm_starProjection_apply_le (Projection/Basic.lean);
- LinearMap.trace_eq_sum_inner (InnerProductSpace/Trace.lean:25);
- LinearMap.IsProj.trace (LinearAlgebra/Trace.lean:327);
- LinearMap.IsIdempotentElem.isProj_range (Projection.lean:564);
- PiLp.norm_sq_eq_of_L2 and PiLp.completeSpace (PiLp.lean);
- cauchySeq_of_le_geometric and dist_le_of_le_geometric_of_tendsto (SpecificLimits/Basic.lean);
- exists_nat_pow_near_of_lt_one.
Note: `mul_le_mul_left'` no longer exists in this Mathlib; use mul_le_mul_right or gcongr. SimonGMT Chapter04 also has trace_starProjection.

Lean checks:
- Both child types, and the frozen parent and sibling types, elaborate in comparator scope; the only diagnostic is the expected sorry warning.
- Complete proofs of both children compile as Submission.dorag_ted_planes_limit and Submission.dorag_ted_hs_integral_compare, with axioms [propext, Classical.choice, Quot.sound].
- Assembly.lean proves the exact frozen parent type from the exact child types and the exact frozen sibling types, with the same axioms.
- An independent reviewer recompiled all three files and returned ACCEPT.
- No lean_name collision.
