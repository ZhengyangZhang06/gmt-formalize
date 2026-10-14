# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.good_center-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, proof of 5.1, displays (1)–(7) (chapter-06.txt lines 1405–1928), as written out in step E1 of the parent proof, with μ_T and μ_{∂T} replaced by two arbitrary finite Borel measures μ, μ'.

Notation. n := m + 1, ℓ := P − n ≥ 1, so n + 1 ≤ P. 𝒥 := the set of J ⊆ {1,…,P} with |J| = n + 1, N := |𝒥| = binom(P, n + 1). For J ∈ 𝒥: S_J := {x : x_i = 0 (i ∉ J)} (dimension n + 1); p_J is the orthogonal projection onto S_J (p_J(x)_i = x_i for i ∈ J, 0 otherwise); S_J^⊥ = {x : x_i = 0 (i ∈ J)} (dimension ℓ − 1); Z_J := ℤ^P ∩ S_J; B^J_r(w) := {v ∈ S_J : |v − w| < r}. q := (1/2,…,1/2), x_J := p_J(q). L^d is Lebesgue measure, ω_d := L^d(unit ball of ℝ^d), ω_0 := 1. For a ∈ ℝ^P, L*(a) := {y : at least n + 1 = m + 2 coordinates satisfy y_i − a_i ∈ ℤ} and d_a := dist(·, L*(a)).

1. Tubes around the dual skeleton. For a ∈ ℝ^P and r > 0,
 {x : d_a(x) < r} = ⋃_{J∈𝒥} ⋃_{z∈Z_J} p_J^{-1}(B^J_r(p_J(a) + z)).
 Proof: L*(a) = ⋃_{J,z} A_{J,z} with A_{J,z} := p_J^{-1}(p_J(a) + z) = {y : y_i = a_i + z_i (i ∈ J)}. Indeed, if y ∈ L*(a), choose n + 1 indices J among those with y_i − a_i ∈ ℤ and put z_i := y_i − a_i (i ∈ J), z_i := 0 otherwise; the converse is immediate. For x ∈ ℝ^P, dist(x, A_{J,z}) = |p_J(x) − p_J(a) − z| (Pythagoras; the point x − p_J(x) + p_J(a) + z ∈ A_{J,z} attains it). The distance to a union is the infimum of the distances, so d_a(x) < r iff |p_J(x) − p_J(a) − z| < r for some (J, z).

2. Bad sets. Let ν be a finite Borel measure on ℝ^P and β > 0. For g ∈ S_J and r > 0 put O_r(g) := ⋃_{z∈Z_J} p_J^{-1}(B^J_r(g + z)) (open). Let G_J(ν) be the set of g ∈ S_J with |g − x_J| < 1/4 and ν(O_r(g)) ≤ β r^{n+1} ν(ℝ^P) for every r ∈ (0, 1/4], and B_J(ν) := {g ∈ S_J : |g − x_J| < 1/4} ∖ G_J(ν). If ν(ℝ^P) = 0 then B_J(ν) = ∅. Assume ν(ℝ^P) > 0.
 (2a) B_J(ν) is relatively open in S_J, hence Borel. Let g ∈ B_J(ν) with witness r and g_k → g in S_J. O_r(g_k) = O_r(g) + (g_k − g), and every point of the open set O_r(g) lies in O_r(g_k) for large k. So 1_{O_r(g)} ≤ liminf_k 1_{O_r(g_k)} pointwise and, by Fatou, ν(O_r(g)) ≤ liminf_k ν(O_r(g_k)). Hence ν(O_r(g_k)) > β r^{n+1} ν(ℝ^P) and |g_k − x_J| < 1/4 for large k, i.e. g_k ∈ B_J(ν).
 (2b) L^{n+1}(B_J(ν)) ≤ 5^{n+1} ω_{n+1}/β. For each b ∈ B_J(ν) choose r_b ∈ (0, 1/4] with ν(O_{r_b}(b)) > β r_b^{n+1} ν(ℝ^P). By the Vitali covering lemma (Simon Ch. 1, 3.4; Mathlib Vitali.exists_disjoint_subfamily_covering_enlargement) there is a pairwise disjoint subfamily of the balls B^J_{r_b}(b), countable because S_J is separable, say B^J_{r_l}(b_l), such that every B^J_{r_b}(b) meets some B^J_{r_l}(b_l) with r_b ≤ 2r_l. So B_J(ν) ⊆ ⋃_l B^J_{5r_l}(b_l). The open sets O_{r_l}(b_l) are pairwise disjoint, because the balls B^J_{r_l}(b_l + z) are pairwise disjoint over (l, z): for equal z they are translates of disjoint balls; for z ≠ z' they lie in B^J_{1/2}(x_J + z) and B^J_{1/2}(x_J + z') (|b_l − x_J| < 1/4, r_l ≤ 1/4), which are disjoint as |z − z'| ≥ 1. Preimages under p_J of disjoint sets are disjoint. Hence β ν(ℝ^P) Σ_l r_l^{n+1} ≤ Σ_l ν(O_{r_l}(b_l)) ≤ ν(ℝ^P), so Σ_l r_l^{n+1} ≤ 1/β and L^{n+1}(B_J(ν)) ≤ Σ_l ω_{n+1}(5r_l)^{n+1} ≤ 5^{n+1}ω_{n+1}/β.

3. Choice of β and a. Put β := 1 + 2N·5^{n+1}ω_{n+1}ω_{ℓ−1}4^{1−ℓ}·4^P/ω_P; it depends only on P and m. For J ∈ 𝒥 let Bad_J := {a ∈ B_{1/4}(q) : p_J(a) ∈ B_J(μ) ∪ B_J(μ')} (Borel). Write ℝ^P = S_J ⊕ S_J^⊥; the coordinate splitting x ↦ ((x_i)_{i∈J}, (x_i)_{i∉J}) is a measure-preserving equivalence of Lebesgue measure on Euclid P with the product of Lebesgue measures (Mathlib volume_preserving for coordinate permutations and products of PiLp/EuclideanSpace). Fubini gives
 L^P(Bad_J) = ∫_{B_J(μ)∪B_J(μ')} L^{ℓ−1}({w ∈ S_J^⊥ : g + w ∈ B_{1/4}(q)}) dL^{n+1}(g) ≤ (2·5^{n+1}ω_{n+1}/β)·ω_{ℓ−1}4^{1−ℓ},
because each fibre lies in a ball of radius 1/4 of the (ℓ − 1)-dimensional space S_J^⊥ (for ℓ = 1 the fibre has at most one point and L^0 is counting measure, ω_0 = 1). Summing over the N sets J, L^P(⋃_J Bad_J) ≤ 2N·5^{n+1}ω_{n+1}ω_{ℓ−1}4^{1−ℓ}/β < ω_P 4^{−P} = L^P(B_{1/4}(q)). Choose a ∈ B_{1/4}(q) ∖ ⋃_J Bad_J. Then |a_i − 1/2| ≤ |a − q| < 1/4 for every i. For every J, |p_J(a) − x_J| ≤ |a − q| < 1/4 and p_J(a) ∉ B_J(μ) ∪ B_J(μ'), so p_J(a) ∈ G_J(μ) if μ(ℝ^P) > 0 and p_J(a) ∈ G_J(μ') if μ'(ℝ^P) > 0.

4. Conclusion. Let r ∈ (0, 1/4]. By 1, {x : d_a(x) < r} = ⋃_J O_r(p_J(a)), hence μ({d_a < r}) ≤ Σ_J μ(O_r(p_J(a))) ≤ N β r^{n+1} μ(ℝ^P); if μ(ℝ^P) = 0 both sides vanish. The same holds for μ'. Thus C := Nβ (as an element of ℝ≥0, depending only on P and m) satisfies μ({x : d_a(x) < r}) ≤ C r^{m+2} μ(univ) and μ'({x : d_a(x) < r}) ≤ C r^{m+2} μ'(univ) for all r ∈ (0, 1/4], with r^{m+2} = r^{n+1}. ∎

## Key steps

1. {d_a < r} is the union over (n+1)-subsets J and z ∈ ℤ^P ∩ S_J of the cylinders p_J^{-1}(B_r(p_J(a) + z)).
2. For each J and each measure, the set of bad projections g (some r ≤ 1/4 with ν(O_r(g)) > βr^{n+1}ν(ℝ^P)) is relatively open (Fatou) and has L^{n+1}-measure ≤ 5^{n+1}ω_{n+1}/β by the Vitali 5r-covering lemma and disjointness of the periodic cylinders.
3. Fubini over S_J × S_J^⊥ bounds the measure of centres a ∈ B_{1/4}(q) with a bad projection by 2·5^{n+1}ω_{n+1}ω_{ℓ−1}4^{1−ℓ}/β; for β large the union over J misses a point a.
4. For this a, μ({d_a < r}) ≤ Σ_J μ(O_r(p_J(a))) ≤ Nβ r^{n+1}μ(ℝ^P), likewise for μ'; C := Nβ.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean workspaces/gmt-ch07/GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d, matches manifest)`
- `rg -n -i 'deformation theorem|federer|polyhedral|cubical|skeleton' project/GMT -g '*.lean'`
- `rg -n -i 'homotopy|lipschitz.*push|pushforward' project/GMT -g '*.lean'`
- `rg -n 'cmcdt_' project mathlib/Mathlib -g '*.lean' (no match)`
- `rg -n -i 'federer.?fleming|deformation theorem|flat norm|polyhedral chain' mathlib/Mathlib -g '*.lean' (no match)`
- `rg -n 'theorem (cthickening_smul|smul_cthickening|thickening_smul|infEDist_smul₀|infDist_smul₀)' mathlib/Mathlib`
- `rg -n 'theorem (exists_disjoint_subfamily_covering_enlargement|ae_differentiableAt|integral_divergence_of_hasFDerivAt_off_countable)' mathlib/Mathlib`
- `grep in lake-packages-25730c7c for the declarations cited by the child proofs: countablyRectifiable_iUnion, HasApproximateTangentSpaceAt.unique, countablyRectifiable_of_measure_zero, CountablyRectifiable.mono, area_image_criticalSet_eq_zero, injective_area_formula_lipschitzOn, weighted_area_formula_lipschitzOn_fiberSum, exteriorDerivativeOn_pullbackFormWithin, GeometricCurrentOn.boundary_affinePushforward, exteriorDerivative_affinePullbackForm, WeaklyConvergesOn.massOn_le_liminf, WeaklyConvergesOn.boundary, exteriorDerivative_apply, GeometricCurrentOn.boundary_boundary, euclideanHausdorffMeasure_smul₀, LipschitzOnWith.extend_real, exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, LinearMap.exists_antilipschitzWith, MeasurableSet.image_of_continuousOn_injOn, MonotoneOn.intervalIntegrable_deriv, MonotoneOn.intervalIntegral_deriv_mem_uIcc, Monotone.ae_differentiableAt, LipschitzWith.ae_differentiableAt, LipschitzOnWith.hausdorffMeasure_image_le, LipschitzWith.integral_lineDeriv_mul_eq, ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable, cthickening_cthickening_subset, cthickening_subset_thickening', IsCompact.cthickening, Isometry.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, measurable_deriv (all found)`
- `python3 scan of runs/20261011T150044Z-ba604216b4/dag.json (681 nodes): lean_name collisions for the eight proposed names (none), frozen types of the five resolved dependencies, statuses; verbatim antecedent check of the child types`
- `lake env lean /tmp/cmcdt2/lean/V1Types.lean (eight child types elaborate); lake env lean /tmp/cmcdt2/lean/AssemblySkeleton.lean; lake env lean /tmp/cmcdt2/lean/Assembly.lean (assembly proof, #print axioms: propext, Classical.choice, Quot.sound); lake env lean /tmp/cmcdt2/lean/InstCheck.lean (ContDiff ℝ (⊤ : ℕ∞) = C^∞ ≠ ω; pointwise Sub by rfl; trace coercion)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Ball/Pointwise.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1/decomposition-v1.json`
- `/tmp/cmcdt2/lean/V1Types.lean`
- `/tmp/cmcdt2/lean/Assembly.lean`
- `/tmp/cmcdt2/lean/InstCheck.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) has the same contract as the workspace Contract.lean and Submission.lean. The project holds only a separate, unsolved Ch06 specification of the deformation theorem and Lipschitz push-forward (project/GMT/Ch06/Contract.lean: DeformationTheorem, LipschitzPushforwardIntegerMultiplicity, IsLatticeChain; main_theorem := by sorry). It uses incompatible types (Eucl, IsLatticeChain) and cannot be imported into Ch07, so it is not reusable. Mathlib has no deformation, flat-norm or polyhedral-chain results (no match). It does provide every tool cited by the child proofs: Vitali covering, Rademacher, the divergence theorem, integrability of monotone derivatives, infEDist_smul₀, cthickening lemmas, and Hausdorff measure scaling and isometry. Every cited SimonGMT declaration exists. No declaration or DAG node uses the cmcdt_ prefix. All eight child types elaborate. The assembly from the five dependency types and three child types to the selected frozen type compiles with only propext, Classical.choice and Quot.sound.
