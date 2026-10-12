# Parent-supplied natural-language proof

- Parent DAG node: `root.submanifold_cover-a1.regular_ball_submanifold-a1`
- Child DAG node: `root.submanifold_cover-a1.regular_ball_submanifold-a1.local_lower_bounds-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon, Ch. 3, proof of Lemma 1.2, chapter-03.txt lines 61-64 (printed p. 70): “if the Jacobian [of] G_ij is non-zero at a point x, then there is a σ > 0 such that G_ij(B_σ(x)) is an n-dimensional C¹ submanifold”. This lemma is the analytic half of that remark: Steps 1-5 of the supplied proof of node root.submanifold_cover-a1.regular_ball_submanifold-a1, localized to an open set U on which G is C¹ (that node applies it with U = ℝⁿ). No printed erratum is involved.

Notation. ℝᵈ = EuclideanSpace ℝ (Fin d). |·| is the Euclidean norm and ‖·‖ the operator norm on L(ℝⁿ, ℝᵖ). B_ρ(x) = Metric.ball x ρ, B̄_ρ(x) = Metric.closedBall x ρ, DG(z) = fderiv ℝ G z, and L := DG(x).

Hypotheses. n, p ∈ ℕ; G : ℝⁿ → ℝᵖ; U ⊆ ℝⁿ open; G is C¹ on U (ContDiffOn ℝ 1 G U); x ∈ U; L = DG(x) is injective.
Goal. There are r > 0 with B̄_r(x) ⊆ U and c > 0 such that
(i) c|z − z'| ≤ |G(z) − G(z')| for all z, z' ∈ B̄_r(x), and
(ii) c|v| ≤ |DG(z)v| for all z ∈ B̄_r(x) and v ∈ ℝⁿ.

1. Regularity of G on U. G is C¹ on U and 1 ≠ 0, so G is differentiable within U at every point of U (ContDiffOn.differentiableOn). U is open, so it is a neighbourhood of each of its points (IsOpen.mem_nhds). Hence G is differentiable at every z ∈ U (DifferentiableWithinAt.differentiableAt) and has Fréchet derivative DG(z) there (DifferentiableAt.hasFDerivAt). Moreover z ↦ DG(z) is continuous on U as a map into L(ℝⁿ, ℝᵖ) with the operator norm (ContDiffOn.continuousOn_fderiv_of_isOpen, using 1 ≤ 1).

2. Lower bound for L. L is an injective linear map on the finite-dimensional space ℝⁿ. By LinearMap.injective_iff_antilipschitz there is K > 0 with |v − w| ≤ K|Lv − Lw| for all v, w ∈ ℝⁿ. Taking w = 0 (L0 = 0) gives |v| ≤ K|Lv|. Put c₀ := 1/K > 0. Then
 (2.1) c₀|v| ≤ |Lv| for every v ∈ ℝⁿ.
For n = 0 the lemma still supplies K > 0, and (2.1) holds trivially since v = 0.

3. Choice of r and c.
- U is open and x ∈ U, so there is δ₁ > 0 with B_{δ₁}(x) ⊆ U (Metric.isOpen_iff).
- DG is continuous on U at x (Step 1). So there is δ₂ > 0 such that ‖DG(z) − L‖ < c₀/2 for all z ∈ U with |z − x| < δ₂ (Metric.continuousOn_iff together with dist_eq_norm).
Put δ := min(δ₁, δ₂) > 0, r := δ/2 > 0 and c := c₀/2 > 0. Let z ∈ B̄_r(x). Then |z − x| ≤ δ/2 < δ ≤ δ₁, so z ∈ B_{δ₁}(x) ⊆ U; this proves B̄_r(x) ⊆ U. Also z ∈ U and |z − x| < δ ≤ δ₂, so
 (3.1) ‖DG(z) − L‖ ≤ c₀/2 for every z ∈ B̄_r(x).

4. Proof of (i). Let h(w) := G(w) − Lw.
- For w ∈ B̄_r(x) ⊆ U, Step 1 and the linearity of L show that h has Fréchet derivative DG(w) − L at w, hence also within the set B̄_r(x).
- By (3.1), ‖DG(w) − L‖ ≤ c₀/2 for all w ∈ B̄_r(x).
- B̄_r(x) is convex (convex_closedBall).
The mean value inequality (Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le) therefore gives, for all z, z' ∈ B̄_r(x),
 |h(z) − h(z')| ≤ (c₀/2)|z − z'|.
Its variant norm_image_sub_le_of_norm_hasFDerivWithin_le' with φ = L gives the same bound directly. Since L is linear, h(z) − h(z') = (G(z) − G(z')) − L(z − z'), so
 (4.1) |(G(z) − G(z')) − L(z − z')| ≤ (c₀/2)|z − z'|.
By the triangle inequality (norm_le_norm_add_norm_sub),
 |L(z − z')| ≤ |G(z) − G(z')| + |(G(z) − G(z')) − L(z − z')|.
Combining this with (2.1) for v = z − z' and with (4.1):
 c₀|z − z'| ≤ |G(z) − G(z')| + (c₀/2)|z − z'|.
Hence c|z − z'| = (c₀/2)|z − z'| ≤ |G(z) − G(z')|.

5. Proof of (ii). Let z ∈ B̄_r(x) and v ∈ ℝⁿ.
- By the operator-norm bound and (3.1): |(DG(z) − L)v| ≤ ‖DG(z) − L‖|v| ≤ (c₀/2)|v|, where (DG(z) − L)v = DG(z)v − Lv.
- By the triangle inequality: |Lv| ≤ |DG(z)v| + |DG(z)v − Lv|.
With (2.1): c₀|v| ≤ |Lv| ≤ |DG(z)v| + (c₀/2)|v|. Hence c|v| = (c₀/2)|v| ≤ |DG(z)v|.

6. Conclusion. r > 0 satisfies B̄_r(x) ⊆ U (Step 3), c > 0, (i) holds (Step 4) and (ii) holds (Step 5). ∎

## Key steps

1. Since U is open and G is C¹ on U, G is differentiable at every point of U with derivative DG, and DG is continuous on U.
2. LinearMap.injective_iff_antilipschitz applied to the injective L = DG(x) on finite-dimensional ℝⁿ gives c₀ = 1/K > 0 with c₀|v| ≤ |Lv|.
3. Take δ = min(δ₁, δ₂) with B_{δ₁}(x) ⊆ U and ‖DG(z) − L‖ < c₀/2 for z ∈ U ∩ B_{δ₂}(x), and set r := δ/2 and c := c₀/2. Then B̄_r(x) ⊆ U and ‖DG − L‖ ≤ c₀/2 on B̄_r(x).
4. The mean value inequality for w ↦ G(w) − Lw on the convex B̄_r(x) gives |G(z) − G(z') − L(z − z')| ≤ (c₀/2)|z − z'|. With the triangle inequality this yields c|z − z'| ≤ |G(z) − G(z')|.
5. The operator-norm perturbation |(DG(z) − L)v| ≤ (c₀/2)|v| and the triangle inequality give c|v| ≤ |DG(z)v| on B̄_r(x).

## Reference use

### local-project

Queries:
- `rg -n 'def IsC1Submanifold|abbrev Rn' project/GMT/Ch03/Contract.lean`
- `rg -n 'theorem injective_iff_antilipschitz|theorem norm_image_sub_le_of_norm_hasFDerivWithin_le|theorem continuous_fderiv|theorem ContDiff.continuous_fderiv' mathlib/Mathlib`
- `rg -n 'antilipschitz|injOn|injective' mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ApproximatesLinearOn.lean`
- `rg -n 'theorem approximates_deriv_on_nhds|theorem approximates_deriv_on_open_nhds' mathlib/Mathlib`
- `rg -n 'LocallyInjective|locallyInjective|eventually_injOn|injOn_of_injective|IsImmersion|isImmersion' mathlib/Mathlib/Analysis mathlib/Mathlib/Geometry/Manifold`
- `rg -n 'theorem add_lipschitzWith|theorem injective_iff_antilipschitz|theorem exists_antilipschitzWith|antilipschitz_of_injective|theorem AntilipschitzWith.add' mathlib/Mathlib`
- `grep -rn 'add_sub_lipschitzWith|theorem add_lipschitzWith|mul_lipschitzWith|mul_div_lipschitzWith' mathlib/Mathlib`
- `grep -n 'theorem ContDiffOn.continuousOn_fderiv_of_isOpen|theorem ContDiffOn.differentiableOn|theorem ContDiff.differentiable' mathlib/Mathlib/Analysis/Calculus/ContDiff/*.lean`
- `rg -n 'theorem IsCompact.diff|theorem IsCompact.of_isClosed_subset|theorem ContinuousOn.preimage_isClosed_of_isClosed|theorem IsCompact.isClosed|theorem isCompact_closedBall|theorem convex_closedBall|theorem ContDiffOn.continuousOn |theorem ContDiff.contDiffOn|theorem norm_le_norm_add_norm_sub |theorem isOpen_iff |theorem continuousOn_iff ' mathlib/Mathlib`
- `grep -n 'norm_image_sub_le_of_norm_hasFDerivWithin_le' mathlib/Mathlib/Analysis/Calculus/MeanValue.lean; grep -n 'isCompact_closedBall' mathlib/Mathlib/Topology/MetricSpace/ProperSpace.lean`
- `rg -n 'def IsSimonSubmanifold|def IsSimonLocalRepresentation|def IsProperOnInto' -A8 simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `rg -n 'theorem|lemma|def ' simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldTopology.lean`
- `rg -n -i 'immersion|injOn.*closedBall|closedBall.*injOn|local.*inject|isC1|regular point|regular_point' simongmt/Poincare/SimonGMT`
- `grep -rln 'c1_injective_fderiv_local_lower_bounds|isC1Submanifold_image_ball_of_injOn_closedBall' over simongmt/Poincare, mathlib/Mathlib, workspaces/*/GMT, workspaces/*/.humanize, cluster-state`
- `cmp of the cited snapshot Mathlib files and Contract.lean against lake-packages-25730c7c and the workspace`
- `lake env lean /tmp/rbs-scratch/Elab.lean, /tmp/rbs-scratch/Split2.lean (both child proofs + parent assembly + #print axioms), /tmp/rbs-scratch/Combined.lean (NodeChallenge/NodeSolution text generated by verifier/gmt-compare.py child_modules)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ApproximatesLinearOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Group/Uniform.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/ProperSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Separation/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/ContinuousOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Module/Convex.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Manifold/Immersion.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/ConstancyNormalCharts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-submanifold-cover-a1-regular-ball-submanifold-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-submanifold-cover-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-submanifold-cover-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-chart-tangent-differential-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/tmp/rbs-scratch/Elab.lean`
- `/tmp/rbs-scratch/Split2.lean`
- `/tmp/rbs-scratch/Combined.lean`
- `/tmp/rbs-scratch/gen_challenge.py`

Snapshot: project d09bc8a, Mathlib 25730c7c. Every cited snapshot file is byte-identical (cmp) to lake-packages-25730c7c, and Contract.lean is identical to the workspace copy. Contract.lean:56 defines Rn and :68 defines IsC1Submanifold, the target predicate of child 2.

Available ingredients (used in the child proofs):
- FiniteDimension.lean: LinearMap.exists_antilipschitzWith (:230), LinearMap.injective_iff_antilipschitz (:242), ContinuousLinearMap.isOpen_injective (:263).
- MeanValue.lean: Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (:422) and its variant with a fixed linear map φ (:526).
- ContDiff/Defs.lean: ContDiffOn.continuousOn (:557), ContDiffOn.differentiableOn (:578), ContDiffOn.continuousOn_fderiv_of_isOpen (:916), ContDiff.contDiffOn (:1121), ContDiff.continuous_fderiv (:1271).
- Pseudo/Defs.lean: Metric.isOpen_iff (:833), Metric.continuousOn_iff (:880).
- Normed/Group/Basic.lean: norm_le_norm_add_norm_sub (alias norm_le_insert, :202).
- ProperSpace.lean: ProperSpace.isCompact_closedBall (:39).
- Compact.lean: IsCompact.diff (:101), IsCompact.of_isClosed_subset (:105), IsCompact.image_of_continuousOn (:110).
- Hausdorff.lean: IsCompact.isClosed (:600).
- ContinuousOn.lean: ContinuousOn.preimage_isClosed_of_isClosed (:197).
- Normed/Module/Convex.lean: convex_closedBall (:70).

No match, so both children are new obligations:
- Mathlib's local injectivity results ApproximatesLinearOn.antilipschitzWith/injOn (ApproximatesLinearOn.lean:317,331) and HasStrictFDerivAt.approximates_deriv_on_open_nhds (InverseFunctionTheorem/FDeriv.lean:101) require a ContinuousLinearEquiv, not merely an injective derivative.
- Geometry/Manifold/Immersion.lean (IsImmersionAt) is the manifold notion and gives no Euclidean local lower bounds.
- SimonGMT IsSimonLocalRepresentation/IsSimonSubmanifold (Chapter02/Submanifold.lean:36,47) are the (4.1) analogues of IsC1Submanifold. SubmanifoldTopology.lean (isProperMap_chartMap :54, exists_open_image_eq_inter :100) assumes a chart is already given, so no lemma builds a chart from injectivity on a closed ball. The Chapter08 immersion lemmas are C² local left inverses.

Reuse evidence: root.chart_tangent_differential-a1 (handoff Step 2) re-derives exactly child 1's estimate for a chart ψ that is C¹ on an open V.

Names: neither proposed bare name occurs in Mathlib, SimonGMT, any chapter workspace, any .humanize run or cluster-state.

Lean checks: both lean_statements pass lean_contract.validate_lean_statement and elaborate in the exact NodeChallenge scope generated by gmt-compare.py child_modules. Complete scratch proofs of both children and of the frozen selected type assembled from them compile. `exact Submission.X` closes both generated NodeSolution goals. #print axioms reports only propext, Classical.choice and Quot.sound.
