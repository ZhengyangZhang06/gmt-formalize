# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pieces-a1.regular_set_cover-a1`
- Child DAG node: `root.lipschitz_pieces-a1.regular_set_cover-a1.local_bound_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. |·| denotes the norms of ℝⁿ = EuclideanSpace ℝ (Fin n) and of F. On ℝⁿ, dist(x, y) = |x − y|, and B_ρ(q) := {x ∈ ℝⁿ : |x − q| ≤ ρ} is the closed ball. For k ∈ ℕ put r_k := 1/(k+1) ∈ (0, 1] and
   G_k := ⋂_{u ∈ ℝⁿ, |u| ≤ r_k} {w ∈ ℝⁿ : r_k·|u| ≤ |f(w + u) − f(w)|}.
Thus w ∈ G_k if and only if r_k·|u| ≤ |f(w + u) − f(w)| for every u ∈ ℝⁿ with |u| ≤ r_k. (These are the sets G_k of the parent proof; here R is an arbitrary Borel set with the stated pointwise property.)

1. (G_k is closed, hence Borel.) Fix k and u ∈ ℝⁿ. The map w ↦ |f(w + u) − f(w)| is continuous, because f is continuous and translation w ↦ w + u, subtraction and the norm are continuous. The map w ↦ r_k·|u| is constant. Hence {w : r_k·|u| ≤ |f(w + u) − f(w)|} is closed (Mathlib isClosed_le). An intersection of closed sets is closed (isClosed_biInter), so G_k is closed and therefore Borel (IsClosed.measurableSet).

2. (Every point of R lies in some G_k.) Let w ∈ R, and let c > 0 be given by the hypothesis for w. By the Archimedean property (Mathlib exists_nat_one_div_lt) there is k ∈ ℕ with r_k = 1/(k+1) < c. Let u ∈ ℝⁿ with |u| ≤ r_k. Then |u| ≤ c, so the hypothesis gives c·|u| ≤ |f(w + u) − f(w)|. Also r_k·|u| ≤ c·|u|, because r_k ≤ c and |u| ≥ 0. Hence r_k·|u| ≤ |f(w + u) − f(w)|, and since u was arbitrary, w ∈ G_k.

3. (Small balls.) ℝⁿ is separable and nonempty (it contains 0), so there is a sequence (q_m)_{m∈ℕ} in ℝⁿ with dense range (Mathlib TopologicalSpace.exists_dense_seq). Let w ∈ ℝⁿ and k ∈ ℕ. Density, applied with the radius r_k/2 > 0 (DenseRange.exists_dist_lt), gives m ∈ ℕ with dist(w, q_m) < r_k/2, so w ∈ B_{r_k/2}(q_m).

4. (The family.) For p ∈ ℕ, let (k(p), m(p)) := Nat.unpair p and define
   T_p := R ∩ G_{k(p)} ∩ B_{r_{k(p)}/2}(q_{m(p)}).

5. (Covering.) Let w ∈ R. By step 2 there is k with w ∈ G_k, and by step 3 there is m with w ∈ B_{r_k/2}(q_m). Put p := Nat.pair k m. Then Nat.unpair p = (k, m) (Nat.unpair_pair), so T_p = R ∩ G_k ∩ B_{r_k/2}(q_m) contains w. Hence R ⊆ ⋃_p T_p.

6. (Properties of each T_p.) Fix p and write k := k(p), m := m(p).
 (a) T_p is Borel. R is Borel by hypothesis, G_k is Borel by step 1, and the closed ball B_{r_k/2}(q_m) is Borel (measurableSet_closedBall). A finite intersection of Borel sets is Borel.
 (b) T_p is bounded. It is contained in the closed ball B_{r_k/2}(q_m), which is bounded (Metric.isBounded_closedBall, Bornology.IsBounded.subset).
 (c) T_p ⊆ R by definition.
 (d) Put c := r_k = 1/(k+1) > 0, and let v, w ∈ T_p. Both lie in B_{r_k/2}(q_m), so |v − w| = dist(v, w) ≤ dist(v, q_m) + dist(w, q_m) ≤ r_k/2 + r_k/2 = r_k (dist_triangle_right). Let u := v − w; then |u| ≤ r_k and w + u = v. Since w ∈ G_k, the defining inequality of G_k for this u gives r_k·|u| ≤ |f(w + u) − f(w)|, that is, c·|v − w| ≤ |f(v) − f(w)|.

Steps 5 and 6 are exactly the assertions. R ⊆ ⋃_p T_p, and each T_p is Borel, bounded and contained in R. Each T_p also satisfies the lower bound with the constant c = 1/(k(p)+1) > 0.

## Key steps

1. G_k := ⋂_{|u| ≤ r_k} {w : r_k|u| ≤ |f(w+u) − f(w)|} with r_k = 1/(k+1) is closed because f is continuous (isClosed_le, isClosed_biInter), hence Borel
2. For w ∈ R with pointwise constant c, choosing k with 1/(k+1) < c (exists_nat_one_div_lt) gives w ∈ G_k
3. A dense sequence (q_m) (TopologicalSpace.exists_dense_seq) gives, for each k, closed balls B_{r_k/2}(q_m) covering ℝⁿ (DenseRange.exists_dist_lt)
4. T_p := R ∩ G_k ∩ B_{r_k/2}(q_m), with (k, m) = Nat.unpair p, covers R (Nat.unpair_pair); each T_p is Borel, bounded and contained in R
5. For v, w ∈ T_p one has |v − w| ≤ r_k, so taking u := v − w in the definition of G_k gives r_k|v − w| ≤ |f(v) − f(w)|

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `rg -n "theorem LinearMap.exists_antilipschitzWith|theorem exists_antilipschitzWith" $S/mathlib/Mathlib; rg -n bound_of_antilipschitz; rg -n "theorem hasFDerivAt_iff_isLittleO_nhds_zero"; rg -n "theorem exists_dense_seq|theorem DenseRange.exists_dist_lt" (whole-snapshot rg timed out after 120 s on the network filesystem; replaced by the targeted greps below)`
- `grep -n antilipschitz $S/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `grep -rn bound_of_antilipschitz $S/mathlib/Mathlib/Analysis/Normed/Group/ $S/mathlib/Mathlib/Topology/EMetricSpace/`
- `grep -n "theorem hasFDerivAt_iff_isLittleO_nhds_zero" -A4 $S/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `grep -n "theorem exists_dense_seq" -A3 $S/mathlib/Mathlib/Topology/Bases.lean`
- `grep -rn "DenseRange.exists_dist_lt\|theorem exists_dist_lt\b" $S/mathlib/Mathlib/Topology/MetricSpace/ $S/mathlib/Mathlib/Topology/`
- `grep -n "theorem measurableSet_of_differentiableAt\b\|theorem measurable_fderiv\b" -A3 $S/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `grep exists_nat_one_div_lt (Algebra/Order/Archimedean/Basic.lean), unpair_pair (Data/Nat/Pairing.lean), isBounded_closedBall (Topology/MetricSpace/Bounded.lean), IsLittleO.def (Analysis/Asymptotics/Defs.lean), eventually_nhds_iff (Topology/MetricSpace/Pseudo/Defs.lean), isClosed_biInter (Topology/Basic.lean), isClosed_le (Topology/Order/OrderClosed.lean)`
- `sed -n 1,80p lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `grep -o "injective_fderiv_local_lower_bound\|lower_lipschitz_cover_of_local_bound" dag.json problem.json issue-workers.json; grep -rln (same names) nodes website; grep -rn (same names) lake-packages-25730c7c/simongmt/Poincare --include=*.lean`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/rsc-decomp-a1/olean/GMT/Ch04/Submission.olean`
- `LEAN_PATH=$(lake env printenv LEAN_PATH):/tmp/rsc-decomp-a1/olean lean /tmp/rsc-decomp-a1/src/ChildTypes.lean`
- `LEAN_PATH=... lean --root=/tmp/rsc-decomp-a1/src /tmp/rsc-decomp-a1/src/RscDecomp/Full.lean -o /tmp/rsc-decomp-a1/olean/RscDecomp/Full.olean (both children + parent assembly + #print axioms)`
- `LEAN_PATH=... lean /tmp/rsc-decomp-a1/src2/ChildOnly.lean (children with only import GMT.Ch04.Submission)`
- `python3 -I: verifier/lean_contract.py validate_lean_statement on both child types`
- `HUMANIZE_RUN_DIR=/tmp/rsc-decomp-a1/fakerun python3 verifier/gmt-compare.py --lean-target GMT/Ch04/Submission.lean --verifier-dir <abs>/verifier --packages <abs>/lake-packages-25730c7c --frozen-commit ff75f52a4c9deb3b3abbd91eb31d7b02e29a4cef --dry-run <child-node>`
- `LEAN_PATH=... lean /tmp/rsc-decomp-a1/gen/{NodeChallenge,NodeSolution}{A,B}.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Normed/Group/Uniform.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Algebra/Order/Archimedean/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Data/Nat/Pairing.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/DAG.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-lipschitz-pieces-a1-regular-set-cover-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-lipschitz-pieces-a1-regular-set-cover-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/rsc-decomp-a1/src/ChildTypes.lean`
- `/tmp/rsc-decomp-a1/src/RscDecomp/Full.lean`
- `/tmp/rsc-decomp-a1/src2/ChildOnly.lean`
- `/tmp/rsc-decomp-a1/gen/NodeChallengeA.lean`
- `/tmp/rsc-decomp-a1/gen/NodeSolutionA.lean`
- `/tmp/rsc-decomp-a1/gen/NodeChallengeB.lean`
- `/tmp/rsc-decomp-a1/gen/NodeSolutionB.lean`

The snapshot manifest pins project ff75f52a4c9d and Mathlib 25730c7c759d. SimonGMT is the pinned lake package at 2b3663083f3f.

Found, with exact signatures inspected:
- LinearMap.exists_antilipschitzWith [FiniteDimensional 𝕜 E] (f : E →ₗ[𝕜] F) (hf : ker f = ⊥) : ∃ K > 0, AntilipschitzWith K f (FiniteDimension.lean:231).
- ZeroHomClass.bound_of_antilipschitz, to_additive of OneHomClass.bound_of_antilipschitz : ‖x‖ ≤ K * ‖f x‖ (Normed/Group/Uniform.lean:170).
- hasFDerivAt_iff_isLittleO_nhds_zero (FDeriv/Basic.lean:815) and Asymptotics.IsLittleO.def (Asymptotics/Defs.lean:187).
- Metric.eventually_nhds_iff (Pseudo/Defs.lean:779) and DenseRange.exists_dist_lt (Pseudo/Defs.lean:930).
- TopologicalSpace.exists_dense_seq (Bases.lean:364).
- exists_nat_one_div_lt (Archimedean/Basic.lean:211) and Nat.unpair_pair (Pairing.lean:60).
- Metric.isBounded_closedBall (Bounded.lean:73), isClosed_biInter (Topology/Basic.lean:162), isClosed_le (OrderClosed.lean:447).
- measurableSet_of_differentiableAt and measurable_fderiv (FDeriv/Measurable.lean:372, 378).
- SimonGMT Chapter02.areaRegularSet f = {x | DifferentiableAt ℝ f x ∧ Injective (fderiv ℝ f x)} and measurableSet_areaRegularSet (AreaLipschitz.lean:31, 34). These are stated for finite-dimensional inner-product Borel spaces, so they apply to EuclideanSpace; this covers parent Step 1.

No match: neither proposed name (injective_fderiv_local_lower_bound, lower_lipschitz_cover_of_local_bound) occurs in dag.json, problem.json, issue-workers.json, the node or website directories, or SimonGMT. Mathlib has no ready-made lemma of either child's shape; the closest are the anti-Lipschitz and little-o lemmas above, which the children combine. A whole-snapshot rg timed out on the network filesystem and was replaced by targeted greps.

Lean checks:
- Both child types elaborate in the comparator contract scope and pass validate_lean_statement.
- Sorry-free proofs of both children compile with only import GMT.Ch04.Submission.
- The parent assembly, which also imports Poincare.SimonGMT.Chapter02.AreaLipschitz, proves the exact frozen parent type.
- #print axioms gives [propext, Classical.choice, Quot.sound] for both children, the assembly, and the comparator-style parent target.
- The gmt-compare.py dry runs accept both child contracts.
- The generated NodeChallenge and NodeSolution modules (exact Submission.X) compile.
