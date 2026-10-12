# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_decay-a1.planes_limit-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_decay-a1.planes_limit-a1.proj_limit_rank-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 6–10 of the parent proof of dorag_ted_planes_limit (Simon Ch. 5, proof of Theorem 5.2: "(4) evidently implies that there is S(ξ) (= lim S_ℓ) such that (5)", book/chapter-05.txt lines 1068–1077). That step uses the fact that the limit of the projections p_{S_ℓ} is again the orthogonal projection onto an n-plane; the statement below isolates that fact, with convergence given column by column.
Notation as in the statement; ⟨·,·⟩ is the inner product of E. The standard basis b := EuclideanSpace.basisFun (Fin P) ℝ is an orthonormal basis of E whose i-th vector is e_i (EuclideanSpace.basisFun_apply) and whose i-th coordinate functional is x ↦ x_i, the i-th coordinate of x. In particular every x ∈ E is x = Σ_i x_i e_i (OrthonormalBasis.sum_repr).
1. Column expansion. Let A : E → E be linear and x ∈ E. Expanding x = Σ_i x_i e_i and using linearity (map_sum, map_smul) gives A x = Σ_i x_i·A e_i.
2. The limit operator. Let L : E → E be the linear map with L e_i = w_i for every i. In Lean this is b.toBasis.constr ℝ w, and Basis.constr_basis gives L e_i = w_i. L is continuous because E is finite-dimensional (LinearMap.toContinuousLinearMap). By Step 1, L x = Σ_i x_i·w_i for every x.
3. Pointwise convergence. Fix x ∈ E. By Step 1, p_{S_j}x = Σ_i x_i·p_{S_j}e_i. By hypothesis p_{S_j}e_i → w_i for each i, and multiplying by the fixed scalar x_i preserves this (Tendsto.const_smul). A finite sum of convergent sequences converges to the sum of the limits (tendsto_finsetSum). Hence p_{S_j}x → Σ_i x_i·w_i = L x as j → ∞, for every x ∈ E.
4. L is idempotent. Fix x ∈ E.
   (a) For each j, p_{S_j}x ∈ S_j (Submodule.starProjection_apply_mem), and p_{S_j} fixes every vector of S_j (Submodule.starProjection_eq_self_iff). Hence p_{S_j}(p_{S_j}x) = p_{S_j}x, and this tends to Lx by Step 3.
   (b) Orthogonal projections do not increase norms (Submodule.norm_starProjection_apply_le). So ‖p_{S_j}(p_{S_j}x) − p_{S_j}(Lx)‖ = ‖p_{S_j}(p_{S_j}x − Lx)‖ ≤ ‖p_{S_j}x − Lx‖ → 0 by Step 3. Thus p_{S_j}(p_{S_j}x) − p_{S_j}(Lx) → 0.
   (c) By Step 3 applied to the vector Lx, p_{S_j}(Lx) → L(Lx).
   (d) Adding (b) and (c), p_{S_j}(p_{S_j}x) → 0 + L(Lx) = L(Lx).
   (e) By (a) and (d), the same sequence converges both to Lx and to L(Lx). Limits in E are unique, so L(Lx) = Lx.
   Since x was arbitrary, L∘L = L.
5. L is symmetric. Fix x, y ∈ E. For every j, ⟨p_{S_j}x, y⟩ = ⟨x, p_{S_j}y⟩, since orthogonal projections are self-adjoint (Submodule.inner_starProjection_left_eq_right).
   The inner product is continuous (Filter.Tendsto.inner), so by Step 3 the left side tends to ⟨Lx, y⟩ and the right side tends to ⟨x, Ly⟩. These are the same real sequence, so uniqueness of limits gives ⟨Lx, y⟩ = ⟨x, Ly⟩.
6. Identification and the column identity.
   By Step 5, L is self-adjoint (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric). By Step 4, L is idempotent. So IsStarProjection L.
   E is a complete inner product space. On such a space, a self-adjoint idempotent continuous linear operator is the orthogonal projection onto its range (isStarProjection_iff_eq_starProjection_range). Put S' := range L; then L = p_{S'}.
   Consequently p_{S'}e_i = L e_i = w_i for every i < P (Step 2). This is the second conclusion.
7. Trace formula. For every linear A : E → E, trace A = Σ_i ⟨e_i, A e_i⟩ (LinearMap.trace_eq_sum_inner with the orthonormal basis b).
8. Trace of an orthogonal projection. Let K ⊆ E be a subspace.
   p_K maps E into K (Submodule.starProjection_apply_mem) and fixes K pointwise (Submodule.starProjection_eq_self_iff). So p_K is a projection onto K (LinearMap.IsProj K p_K).
   Hence trace p_K = dim K (LinearMap.IsProj.trace): in a basis adapted to E = K ⊕ ker p_K, the map p_K is diagonal with dim K ones and zeros elsewhere. The finiteness and freeness hypotheses of that lemma hold for K and ker p_K, which are subspaces of a finite-dimensional real vector space.
9. dim S' = n.
   For every j, Steps 7–8 and the hypothesis dim S_j = n give Σ_i ⟨e_i, p_{S_j}e_i⟩ = trace p_{S_j} = dim S_j = n, as real numbers.
   As j → ∞, Σ_i ⟨e_i, p_{S_j}e_i⟩ → Σ_i ⟨e_i, w_i⟩. This follows from the hypothesis p_{S_j}e_i → w_i, continuity of the inner product, and tendsto_finsetSum.
   By Steps 6, 7 and 8, Σ_i ⟨e_i, w_i⟩ = Σ_i ⟨e_i, p_{S'}e_i⟩ = trace p_{S'} = dim S'.
   So a sequence that is constantly n converges to dim S'. A constant sequence converges to its value, and limits are unique, so (dim S' : ℝ) = (n : ℝ). The cast ℕ → ℝ is injective, hence dim S' = n. This is the first conclusion. ∎

## Key steps

1. Column expansion: A x = Σ_i x_i·A e_i for every linear A : E → E.
2. L e_i := w_i (Basis.constr) satisfies p_{S_j}x → Lx for every x.
3. Idempotent: p_{S_j}(p_{S_j}x) = p_{S_j}x and projections are nonexpansive, so L(Lx) = Lx.
4. Symmetric: ⟨p_{S_j}x, y⟩ = ⟨x, p_{S_j}y⟩ passes to the limit ⟨Lx, y⟩ = ⟨x, Ly⟩.
5. IsStarProjection L gives L = p_{S'} with S' := range L, so p_{S'}e_i = w_i.
6. trace p_K = dim K and trace A = Σ_i⟨e_i, A e_i⟩; so dim S' = lim_j dim S_j = n.

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json  (mode local-project; project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean  (all identical)`
- `python3 -I: verifier gmt-compare.contract_scope(Contract.lean, 'GMT.Ch07.main_theorem')  → open Filter Function Set MeasureTheory Metric; open scoped ENNReal Topology; namespace GMT.Ch07; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt); noncomputable section; end`
- `rg -n "theorem isStarProjection_iff_eq_starProjection_range|theorem IsProj.trace|theorem trace_eq_sum_inner|theorem range_starProjection|theorem starProjection_eq_self_iff|theorem inner_starProjection_left_eq_right|theorem norm_starProjection_apply_le|theorem norm_sq_eq_of_L2|instance completeSpace|theorem continuous_apply|theorem cauchySeq_of_le_geometric |theorem dist_le_of_le_geometric_of_tendsto |starProjection_tendsto_closure_iSup" <snapshot>/mathlib/Mathlib`
- `rg -n "isSelfAdjoint_iff_isSymmetric"; rg -n "class HasOrthogonalProjection"; rg -n "starProjection_apply_mem|range_starProjection" Analysis/InnerProductSpace/Projection/*.lean; rg -n "structure IsStarProjection"; rg -n "theorem constr_basis"; rg -n "basisFun_apply|basisFun_repr|basisFun_toBasis" Analysis/InnerProductSpace/PiL2.lean`
- `rg -n "trace_eq_sum_inner" <snapshot>/mathlib/Mathlib; rg -n "trace_starProjection|starProjection.*trace|finrank.*starProjection" <snapshot>/mathlib/Mathlib lake-packages-25730c7c/simongmt/Poincare`
- `sed -n 785,806p / 535,545p Analysis/Normed/Lp/PiLp.lean (norm_sq_eq_of_L2, dist_sq_eq_of_L2, PiLp.continuous_apply); sed -n 500,560p Analysis/SpecificLimits/Basic.lean; sed -n 320,335p LinearAlgebra/Trace.lean; rg -n isProj_range -A8 LinearAlgebra/Projection.lean`
- `rg -n starProjection <snapshot>/project/GMT --glob '*.lean' | rg -i 'tendsto|limit|closed|finrank|trace'; rg -n -i 'le_geometric.*sq|geometric.*tail|isClosed.*starProjection|starProjection.*isClosed|IsStarProjection.*tendsto|tendsto.*IsStarProjection' <snapshot>/mathlib/Mathlib  (no reusable result)`
- `python3 -I lean_name scan of dag.json (279 nodes) for dorag_ted_pl_geometric_limit / dorag_ted_pl_proj_limit_rank; grep -l over workspaces/gmt-ch01..ch08/.humanize/github-theorem-prover/runs/*/dag.json and workspaces/*/GMT  (no match)`
- `python3 -I verifier/lean_contract.validate_lean_statement on both child types (pass, unchanged)`
- `lean (v4.35.0-rc3, LEAN_PATH = built workspace + lake-packages-25730c7c) on /tmp/pl-decomp-x91/v1/{Challenge,SolA,SolB,Assembly,EndToEnd}.lean with #print axioms`
- `sed -n 1055,1085p book/chapter-05.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Submodule.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Positive.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Projection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Basis/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Star/StarProjection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-f3853385c1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-f3853385c1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/tmp/pl-decomp-x91/v1/Challenge.lean`
- `/tmp/pl-decomp-x91/v1/SolA.lean`
- `/tmp/pl-decomp-x91/v1/SolB.lean`
- `/tmp/pl-decomp-x91/v1/Assembly.lean`
- `/tmp/pl-decomp-x91/v1/EndToEnd.lean`
- `/tmp/pl-decomp-x91/review/MyAssembly.lean`
- `/tmp/pl-decomp-x91/review/MyEndToEnd.lean`
- `/tmp/pl-decomp-x91/review/StrictEndToEnd.lean`

The snapshot pins project b4d606d and Mathlib 25730c7c. Its GMT/Ch07/Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, which form the compiler context. The comparator child scope is the Contract's opens plus namespace GMT.Ch07.

No snapshot result proves either child:
- The project mentions starProjection only in Ch05 tilt-excess definitions; there is no limit, closedness, finrank or trace result.
- Mathlib has only starProjection_tendsto_closure_iSup, which covers monotone families. It has no closedness of rank-n star projections and no squared geometric-tail lemma.
- SimonGMT Chapter04/FirstVariation.lean has trace_starProjection, but it is not needed.

The Mathlib API both child proofs need exists at the pin:
- cauchySeq_of_le_geometric and dist_le_of_le_geometric_of_tendsto (SpecificLimits/Basic.lean);
- cauchySeq_tendsto_of_complete;
- PiLp.dist_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2 and PiLp.continuous_apply (PiLp.lean);
- Basis.constr_basis;
- EuclideanSpace.basisFun_apply;
- Submodule.starProjection_apply_mem, starProjection_eq_self_iff, norm_starProjection_apply_le and inner_starProjection_left_eq_right (Projection/Basic.lean);
- ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric and isStarProjection_iff_eq_starProjection_range (Adjoint.lean);
- LinearMap.trace_eq_sum_inner (InnerProductSpace/Trace.lean:25);
- LinearMap.IsProj.trace (LinearAlgebra/Trace.lean:327).
Note: tendsto_finset_sum is deprecated in favour of tendsto_finsetSum.

Lean checks:
- Both child types and the frozen parent type elaborate in comparator scope; the only diagnostics are the expected sorry warnings.
- Both child types pass lean_contract.validate_lean_statement.
- Complete proofs compile as Submission.dorag_ted_pl_geometric_limit and Submission.dorag_ted_pl_proj_limit_rank, with axioms [propext, Classical.choice, Quot.sound].
- Assembly.lean proves the exact frozen parent type from the two exact child types, with the same axioms.
- EndToEnd.lean runs the comparator-style targets `exact Submission.X` for both children and for the parent. All pass.
- An independent reviewer recompiled everything, wrote its own assembly and a strict no-autoImplicit end-to-end file, and returned ACCEPT.
- Neither lean_name collides with any DAG or workspace declaration.
