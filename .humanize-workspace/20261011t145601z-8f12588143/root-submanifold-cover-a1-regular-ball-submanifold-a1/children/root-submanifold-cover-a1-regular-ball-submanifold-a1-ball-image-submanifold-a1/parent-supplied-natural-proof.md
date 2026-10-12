# Parent-supplied natural-language proof

- Parent DAG node: `root.submanifold_cover-a1.regular_ball_submanifold-a1`
- Child DAG node: `root.submanifold_cover-a1.regular_ball_submanifold-a1.ball_image_submanifold-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon, Ch. 3, proof of Lemma 1.2, chapter-03.txt lines 61-64 (printed p. 70): “G_ij(B_σ(x)) is an n-dimensional C¹ submanifold ... (with G_ij providing a local representation in a neighborhood of the point y = G_ij(x))”. The submanifold notion is Ch. 2 (4.1) (chapter-02.txt lines 849-860), transcribed as IsC1Submanifold. This lemma is the topological half of that remark: Steps 6-9 of the supplied proof of node root.submanifold_cover-a1.regular_ball_submanifold-a1. Two specializations apply. First, the closed ball B̄ there is B̄_r(x) itself. Erratum (v) of the parent asks for injectivity on a closed ball containing B̄_σ(x), and injectivity on B̄_σ(x) itself suffices, so the set A below is the sphere B̄_r(x) ∖ B_r(x). Second, G need only be C¹ on B̄_r(x).

Notation. ℝᵈ = EuclideanSpace ℝ (Fin d). B_r(x) = Metric.ball x r and B̄_r(x) = Metric.closedBall x r. DG(z) = fderiv ℝ G z.

Hypotheses. n, p ∈ ℕ; G : ℝⁿ → ℝᵖ; x ∈ ℝⁿ; r ∈ ℝ; G is C¹ on B̄_r(x) (ContDiffOn ℝ 1 G (B̄_r(x))); G is injective on B̄_r(x); DG(z) is injective for every z ∈ B_r(x).
Goal. IsC1Submanifold n S, where S := G(B_r(x)).

1. Regularity. Since G is C¹ on B̄_r(x), it is continuous on B̄_r(x) (ContDiffOn.continuousOn). Since B_r(x) ⊆ B̄_r(x) (Metric.ball_subset_closedBall), G is C¹ on B_r(x) (ContDiffOn.mono).

2. The chart data. Let V := B_r(x), A := B̄_r(x) ∖ B_r(x) and W := ℝᵖ ∖ G(A).
- V is open (Metric.isOpen_ball).
- ℝⁿ is a proper metric space, so B̄_r(x) is compact (isCompact_closedBall). A is a compact set minus an open set, hence compact (IsCompact.diff).
- A ⊆ B̄_r(x), so G is continuous on A (Step 1). Hence G(A) is compact (IsCompact.image_of_continuousOn) and so closed in the Hausdorff space ℝᵖ (IsCompact.isClosed). Therefore W is open.

3. S ⊆ W, hence W ∩ S = S. Let z ∈ V and suppose G(z) ∈ G(A), say G(z) = G(a) with a ∈ A. Then a ∈ A ⊆ B̄_r(x) and z ∈ B_r(x) ⊆ B̄_r(x). Injectivity of G on B̄_r(x) gives a = z. So z = a ∉ B_r(x), contradicting z ∈ V. Hence G(z) ∈ W for every z ∈ V, i.e. S ⊆ W, and therefore W ∩ S = S.

4. Properness. Let K ⊆ W be compact. Claim: V ∩ G⁻¹(K) = B̄_r(x) ∩ G⁻¹(K).
- ⊆: B_r(x) ⊆ B̄_r(x).
- ⊇: let z ∈ B̄_r(x) with G(z) ∈ K. If z ∉ B_r(x), then z ∈ A, so G(z) ∈ G(A) = ℝᵖ ∖ W. This contradicts G(z) ∈ K ⊆ W. Hence z ∈ B_r(x) = V.
K is compact in the Hausdorff space ℝᵖ, hence closed. G is continuous on the closed set B̄_r(x) (Metric.isClosed_closedBall). So B̄_r(x) ∩ G⁻¹(K) is closed (ContinuousOn.preimage_isClosed_of_isClosed). It is a closed subset of the compact set B̄_r(x), hence compact (IsCompact.of_isClosed_subset). By the claim, V ∩ G⁻¹(K) is compact.

5. Verification of IsC1Submanifold n S. Let y ∈ S. Take V and W from Step 2 and ψ := G. Then:
- V is open and W is open (Step 2);
- y ∈ S ⊆ W (Step 3);
- ψ is C¹ on V (Step 1);
- ψ is injective on V, because V ⊆ B̄_r(x) and G is injective there (Set.InjOn.mono);
- ψ(V) = S = W ∩ S (Step 3);
- V ∩ ψ⁻¹(K) is compact for every compact K ⊆ W (Step 4);
- fderiv ℝ ψ z = DG(z) is injective for every z ∈ V (hypothesis).
These are exactly the eight conditions of IsC1Submanifold n S at y.

6. Degenerate cases. If r ≤ 0, then B_r(x) = ∅ and S = ∅, so the statement holds vacuously; the argument above needs no change. The same argument covers n = 0. ∎

## Key steps

1. G is continuous on B̄_r(x) and C¹ on B_r(x), by restricting ContDiffOn on the closed ball.
2. A := B̄_r(x) ∖ B_r(x) is compact (closed ball minus open ball in a proper space). So G(A) is compact and closed, and W := ℝᵖ ∖ G(A) is open.
3. Injectivity of G on B̄_r(x) gives G(B_r(x)) ⊆ W, hence W ∩ G(B_r(x)) = G(B_r(x)).
4. For compact K ⊆ W, B_r(x) ∩ G⁻¹(K) = B̄_r(x) ∩ G⁻¹(K), which is a closed subset of the compact B̄_r(x) and hence compact.
5. The single chart (V, W, ψ) = (B_r(x), W, G) verifies all eight IsC1Submanifold n conditions at every y ∈ G(B_r(x)); fderiv injectivity on V is the hypothesis.

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
