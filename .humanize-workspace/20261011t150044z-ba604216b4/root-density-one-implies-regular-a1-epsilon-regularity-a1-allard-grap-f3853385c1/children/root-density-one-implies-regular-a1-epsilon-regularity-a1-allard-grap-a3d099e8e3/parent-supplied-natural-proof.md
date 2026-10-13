# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_decay-a1.planes_limit-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_decay-a1.planes_limit-a1.geometric_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 1, 2, 4 and 5 of the parent proof of dorag_ted_planes_limit (Simon Ch. 5, proof of Theorem 5.2: "(4) evidently implies that there is S(ξ) (= lim S_ℓ) such that (5)", book/chapter-05.txt lines 1068–1077). The convergence half of that step is stated here for an arbitrary complete metric space; the parent applies it to the Hilbert–Schmidt vectors v_j = (p_{S_j}e_i)_i in PiLp 2 (fun _ : Fin P => Euclid P). Notation as in the statement.
1. a ≥ 0. Put j = 0 in the hypothesis. Since q⁰ = 1, this gives 0 ≤ dist(v_0, v_1)² ≤ a·1 = a, a square being ≥ 0.
2. Put h := √q. Since q ≥ 0, h ≥ 0 and h² = q (Real.sq_sqrt).
   Since √ is monotone (Real.sqrt_le_sqrt) and √(1/4) = √((1/2)²) = 1/2, we get h ≤ 1/2. Hence h < 1 and 1 − h ≥ 1/2 > 0.
   For every j, (√a·h^j)² = (√a)²·(h²)^j = a·q^j, using (√a)² = a, which holds by Step 1.
   Also √a·h^j ≥ 0.
3. Geometric bound. Fix j. By the hypothesis and Step 2, dist(v_j, v_{j+1})² ≤ a·q^j = (√a·h^j)². Both dist(v_j, v_{j+1}) and √a·h^j are ≥ 0, and for reals s, t ≥ 0, s² ≤ t² implies s ≤ t (pow_le_pow_iff_left₀). Hence dist(v_j, v_{j+1}) ≤ √a·h^j for every j.
4. Convergence. Put C := √a. Step 3 says that consecutive distances satisfy dist(v_j, v_{j+1}) ≤ C·h^j with h < 1.
   For j ≤ m, the triangle inequality gives dist(v_j, v_m) ≤ Σ_{l=j}^{m−1} C·h^l ≤ C·h^j·Σ_{k≥0} h^k = C·h^j/(1 − h). This tends to 0 as j → ∞, because 0 ≤ h < 1. So (v_j) is a Cauchy sequence (Mathlib cauchySeq_of_le_geometric h C, which needs only h < 1).
   X is complete, so there is w ∈ X with v_j → w as j → ∞ (cauchySeq_tendsto_of_complete). This is the first conclusion.
5. Tail bound. Fix j. By Step 4, dist(v_j, v_m) ≤ C·h^j/(1 − h) for every m ≥ j. The function dist(v_j, ·) is continuous and v_m → w, so letting m → ∞ gives dist(v_j, w) ≤ C·h^j/(1 − h) (Mathlib dist_le_of_le_geometric_of_tendsto h C).
   Next, C·h^j/(1 − h) ≤ 2·C·h^j. Since 1 − h > 0, this is equivalent to C·h^j ≤ 2·C·h^j·(1 − h), i.e. 0 ≤ C·h^j·(1 − 2h). That holds because C·h^j ≥ 0 and h ≤ 1/2.
   Hence 0 ≤ dist(v_j, w) ≤ 2·√a·h^j.
6. Squaring. Both sides of the last inequality are ≥ 0, so squaring preserves it (pow_le_pow_left₀): dist(v_j, w)² ≤ (2·√a·h^j)² = 4·(√a·h^j)² = 4·a·q^j, by Step 2. This holds for every j ∈ ℕ and is the second conclusion. ∎

## Key steps

1. a ≥ 0 from the hypothesis at j = 0.
2. h := √q satisfies 0 ≤ h ≤ 1/2 and (√a·h^j)² = a·q^j.
3. Take square roots of nonnegative quantities: dist(v_j, v_{j+1}) ≤ √a·h^j.
4. Geometric bound with h < 1 makes (v_j) Cauchy; by completeness v_j → w.
5. Tail: dist(v_j, w) ≤ √a·h^j/(1 − h) ≤ 2√a·h^j, using 1 − h ≥ 1/2.
6. Square: dist(v_j, w)² ≤ 4·a·q^j.

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
