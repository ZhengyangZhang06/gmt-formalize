# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.flat_limit-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.flat_limit-a1.isometric_transport-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps E1–E2 of the supplied proof of the parent node codim1_zsl_flat_graph_limit (Hausdorff measure is invariant under isometries, and μHE[m] is Lebesgue measure on ℝ^m), for an arbitrary linear isometry followed by a translation; Simon 7.5.5 (chapter-07.txt lines 862–901) regards the limit set F as an H^{n+1}-measurable subset of the plane T_xN in exactly this way.
1. G is an isometry: |G(x) − G(y)| = |ι(x − y)| = |x − y| (Isometry.of_dist_eq, add_sub_add_right_eq_sub, map_sub, LinearIsometry.norm_map). Since ℝ^m is complete, G is a closed embedding (Isometry.isClosedEmbedding), hence a measurable embedding (IsClosedEmbedding.measurableEmbedding). In particular G is injective and G(A) is measurable (MeasurableEmbedding.measurableSet_image').
2. Push-forward. For an isometry, the push-forward of μHE[m] is μHE[m] restricted to the range (Isometry.map_euclideanHausdorffMeasure), and on ℝ^m = EuclideanSpace ℝ (Fin m), μHE[m] = volume (EuclideanSpace.euclideanHausdorffMeasure_eq_volume). Hence G_#(volume on ℝ^m) = μHE[m]⌞range G.
3. Restriction. G(A) is measurable and G(A) ⊆ range G, so μHE[m]⌞G(A) = (μHE[m]⌞range G)⌞G(A) (Measure.restrict_restrict; G(A) ∩ range G = G(A)) = (G_#volume)⌞G(A) = G_#(volume⌞G⁻¹(G(A))) (MeasurableEmbedding.restrict_map) = G_#(volume⌞A), because G⁻¹(G(A)) = A by injectivity (preimage_image_eq).
4. Integral. For every f : ℝ^P → ℝ, ∫_{G(A)} f dμHE[m] = ∫ f d(G_#(volume⌞A)) = ∫_A f(G(w)) dw (MeasurableEmbedding.integral_map, which holds for every integrand because G is a measurable embedding). ∎
Formalization note: unless this child is split further it is a machine leaf (one theorem appended inside `namespace GMT.Ch07` of GMT/Ch07/Submission.lean; no helper declaration, no import, no set_option). The tactic proof below was compiled on the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c, simongmt 2b36630) in exactly that file context: the frozen Submission.lean, under default maxHeartbeats. It passes the workflow's leaf source-delta check (leaf_verification.check_source_delta), its frozen type passes lean_contract.validate_lean_statement and elaborates in the comparator's replayed contract scope, and #print axioms gives only propext, Classical.choice, Quot.sound. It may be used verbatim:
theorem Submission.codim1_zsl_fl_isometry_image_setIntegral : ∀ (m P : ℕ) (ι : Euclid m →ₗᵢ[ℝ] Euclid P) (c : Euclid P) (A : Set (Euclid m)), MeasurableSet A → MeasurableSet ((fun w => ι w + c) '' A) ∧ ∀ f : Euclid P → ℝ, ∫ y in (fun w => ι w + c) '' A, f y ∂μHE[m] = ∫ w in A, f (ι w + c) := by
  intro m P ι c A hA
  have hiso : Isometry (fun w => ι w + c) := by
    refine Isometry.of_dist_eq fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm, add_sub_add_right_eq_sub, ← map_sub, LinearIsometry.norm_map]
  have hemb : MeasurableEmbedding (fun w => ι w + c) :=
    hiso.isClosedEmbedding.measurableEmbedding
  have hAimg : MeasurableSet ((fun w => ι w + c) '' A) := hemb.measurableSet_image' hA
  refine ⟨hAimg, fun f => ?_⟩
  have hmap : (volume : Measure (Euclid m)).map (fun w => ι w + c) =
      (μHE[m] : Measure (Euclid P)).restrict (range (fun w => ι w + c)) := by
    rw [← hiso.map_euclideanHausdorffMeasure, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  have hres : (μHE[m] : Measure (Euclid P)).restrict ((fun w => ι w + c) '' A) =
      ((volume : Measure (Euclid m)).restrict A).map (fun w => ι w + c) := by
    rw [← preimage_image_eq A hemb.injective, ← hemb.restrict_map, hmap,
      Measure.restrict_restrict hAimg, inter_eq_left.mpr (image_subset_range _ _),
      preimage_image_eq A hemb.injective]
  rw [hres, hemb.integral_map]

## Key steps

1. w ↦ ιw + c is an isometry of the complete space ℝ^m, hence a closed and measurable embedding; images of measurable sets are measurable.
2. Isometry.map_euclideanHausdorffMeasure and μHE[m] = volume on ℝ^m give G_#L^m = μHE[m]⌞range G.
3. μHE[m]⌞G(A) = G_#(L^m⌞A) by restrict_restrict, MeasurableEmbedding.restrict_map and injectivity.
4. MeasurableEmbedding.integral_map gives ∫_{G(A)} f dμHE[m] = ∫_A f∘G for every f.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; sha256sum GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `python3 scans of dag.json: the selected node (status, message, children, descendants by id prefix); lean_name lookup of the 6 child names and of codim1_zsl_perimeter_compactness; byte equality of the 2 reused lean_statements and statements with decomposition-v1.json; raw count of 'codim1_zsl_fl_'; scan of nodes/*/*.json outside this node for 'codim1_zsl_fl_'`
- `python3 dump of this node's decomposition-v1.json, decomposition-audit-v1.json, decomposition-review-receipt-v1.json, decomposition-scope-v1.json and parent-child-handoff.json; issue-workers.json entries for issue 5038`
- `git log --all --oneline -S'codim1_zsl_fl_' -- 'GMT/*.lean' (0 commits); positive control git log --all --oneline -S'dgcr_bwd_graph_pullback_extDeriv' -- 'GMT/*.lean'`
- `git show dcc3f4b7fc0f6beb359e7585fbca8b266cc0f38f:GMT/Ch07/Submission.lean; git show 42e24164cfdc5445c7426ab7ee11003f8faee961:GMT/Ch07/Submission.lean (the accepted reused blocks)`
- `grep -n 'structure TestFormOn|def IsTestForm|theorem exteriorDerivative_isTestForm|theorem tsupport_exteriorDerivative_subset|def exteriorDerivative|def covectorEuclideanNorm|def affinePullbackForm|theorem exteriorDerivative_affinePullbackForm|theorem affinePullbackForm_isSmoothForm' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/*.lean`
- `grep -n 'theorem setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|Bornology.IsBounded.subset_ball_lt|theorem norm_add_sq_real' local-references/123e8435b4a2469b/mathlib/Mathlib; grep -rl 'map_euclideanHausdorffMeasure|euclideanHausdorffMeasure_eq_volume' local-references/123e8435b4a2469b/mathlib/Mathlib; diff of snapshot vs .lake/packages/mathlib Bochner/Set.lean (identical)`
- `lake env lean /tmp/fl-v2-decomp/lean/Check2.lean (frozen Submission.lean + accepted dcc3f4b7/42e24164 blocks + sorry placeholder for codim1_zsl_perimeter_compactness + verbatim code of the 4 new children + selected theorem; #print axioms of all 7)`
- `lake env lean /tmp/fl-v2-decomp/lean/Types.lean (import GMT.Ch07.Submission + gmt-compare.contract_scope replay; the 6 child types and the selected type as comparator-style challenges)`
- `lake env lean /tmp/fl-v2-decomp/lean/ContractAssembly2.lean (selected type proved from hypotheses with the frozen perimeter_bound, bv_compactness, graph_integral_limit and isometric_transport types; #print axioms)`
- `python3: lean_contract.validate_lean_statement on the 6 types; leaf_verification.check_source_delta on the 4 new children inserted into GMT/Ch07/Submission.lean; models.ScopedDecomposition validation of this response`
- `sed -n 840,860p book/chapter-07.txt (Simon 7.5.3: by (1) and 5.2 and the BV Compactness 2.6 of Ch. 2 a subsequence converges in L¹_loc)`
- `grep -l '"github_selected_issue": 5038,' .humanize/swarm-configs/* and their max_nodes/max_depth/max_children (cffb5a36…: max_nodes 1000, 08:33Z; 5261729…: max_nodes 5000, 11:17Z); mtime ranges of configs by max_nodes value`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-1637f3a8b4/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-1637f3a8b4/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-1637f3a8b4/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-1637f3a8b4/decomposition-scope-v1.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/lean_contract.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/models.py`
- `/runtime/flows/gmt-claude-d253855dab51/scripts/gmt-compare.py`
- `/tmp/fl-v2-decomp/lean/Check2.lean`
- `/tmp/fl-v2-decomp/lean/Types.lean`
- `/tmp/fl-v2-decomp/lean/ContractAssembly2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/cffb5a36c88f487d9fb784e09cf6981b.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/5261729094924bd1900f1bef36365ca3.json`

Pins match. The snapshot manifest records project b4d606db and Mathlib 25730c7c, equal to the workspace HEAD and .lake/packages/mathlib; simongmt is 2b366308. The snapshot Contract.lean and the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).
DAG state. The selected node is 'decomposing' at 'subproblem decomposition attempt 2' and has no children or descendants. Its v1 split passed the independent review (all six nodes acceptable, no required changes) but was never activated. The cause is not recorded. The first worker's config had max_nodes 1000 while the DAG approached 1000 nodes; the current worker's config has max_nodes 5000. The four codim1_zsl_fl_* names occur nowhere in dag.json (1083 nodes at 12:11Z), in other nodes' files, in GMT/, in simongmt or in git history. dgcr_bwd_coordinate_covector (dcc3f4b7) and dgcr_bwd_graph_pullback_extDeriv (42e24164) are accepted, and their DAG types and statements are byte-identical to the reused subproblems.
Library. The SimonGMT definitions used by the children check out: TestFormOn is the submodule of IsTestForm forms supported in U; exteriorDerivative is extDeriv; exteriorDerivative_isTestForm and tsupport_exteriorDerivative_subset hold; covectorEuclideanNorm is the root of the sum of squared strictly-increasing coordinate coefficients; and affinePullbackForm commutes with d. The snapshot Mathlib contains every lemma the assembly cites: setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (Bochner/Set.lean:466), Bornology.IsBounded.subset_ball_lt (Bounded.lean:105), norm_add_sq_real (InnerProductSpace/Basic.lean:411), and the Hausdorff isometry lemmas (Geometry/Euclidean/Volume/Measure.lean).
Lean (pinned toolchain v4.35.0-rc3). Check2.lean compiles: each of the six children depends only on propext, Classical.choice and Quot.sound, and the selected theorem adds sorryAx solely through the bv_compactness placeholder. ContractAssembly2.lean proves the selected type from the four frozen contract types alone, with only the three standard axioms. Types.lean elaborates all seven types in the comparator's replayed contract scope. validate_lean_statement and check_source_delta accept every child.
Source. Simon 7.5.3 (book/chapter-07.txt lines 852–856) obtains the L¹_loc subsequence from the BV Compactness 2.6 of Ch. 2, which is the sibling bv_compactness.
