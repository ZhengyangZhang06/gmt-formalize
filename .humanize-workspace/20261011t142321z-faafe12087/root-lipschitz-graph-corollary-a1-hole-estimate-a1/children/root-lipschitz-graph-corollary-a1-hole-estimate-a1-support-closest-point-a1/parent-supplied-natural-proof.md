# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_graph_corollary-a1.hole_estimate-a1`
- Child DAG node: `root.lipschitz_graph_corollary-a1.hole_estimate-a1.support_closest_point-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 2 (closest point), stated with exactly the hypotheses that step uses: 0 in spt V, B_rho(0) ⊆ U and |zeta| + d <= rho (in the parent, |zeta| + d <= 2 delta rho + delta rho = 3 delta rho <= rho). Neither openness of U nor d > 0 is needed.

Notation. mu := V.weight, S := spt mu = Measure.support mu, so V.support = U ∩ S by definition; d := infDist(zeta, V.support); B_rho(0) is the closed ball and ball(zeta, d) the open ball.

1. S is closed, because the support of a measure is closed. V.support = U ∩ S is a subset of S, and 0 ∈ V.support, so V.support and S are nonempty.
2. R^(n+l) is a proper metric space (closed bounded sets are compact), so the nonempty closed set S contains a point nearest to zeta: there is y ∈ S with dist(zeta, y) = infDist(zeta, S).
3. Since V.support ⊆ S and V.support is nonempty, infDist(zeta, S) <= infDist(zeta, V.support) = d. Hence dist(zeta, y) <= d.
4. By the triangle inequality, |y| = |zeta - (zeta - y)| <= |zeta| + |zeta - y| = |zeta| + dist(zeta, y) <= |zeta| + d <= rho. So y ∈ B_rho(0) ⊆ U, and therefore y ∈ U ∩ S = V.support.
5. As y ∈ V.support, d = infDist(zeta, V.support) <= dist(zeta, y). With step 3, dist(zeta, y) = d; by symmetry dist(y, zeta) = d. Moreover infDist(zeta, S) = dist(zeta, y) = d by step 2.
6. The open ball ball(zeta, d) does not meet S: if some x ∈ S had dist(x, zeta) < d, then infDist(zeta, S) <= dist(zeta, x) < d, contradicting step 5. Hence ball(zeta, d) is contained in the complement of S.
7. R^(n+l) is second countable, hence hereditarily Lindelöf, and in such a space the complement of the support of any measure is a null set: mu(complement of S) = 0. By monotonicity of mu, mu(ball(zeta, d)) <= mu(complement of S) = 0, so mu(ball(zeta, d)) = 0. (If d = 0 the open ball is empty, and the conclusion also holds.)
8. Steps 4, 5 and 7 give y ∈ V.support with dist(y, zeta) = infDist(zeta, V.support) and V.weight(ball(zeta, infDist(zeta, V.support))) = 0. QED

Lean notes (Mathlib names that worked under the pinned toolchain; for convenience only):
- MeasureTheory.Measure.isClosed_support and IsClosed.exists_infDist_eq_dist (proper space);
- Metric.infDist_le_infDist_of_subset and Metric.infDist_le_dist_of_mem;
- MeasureTheory.Measure.measure_compl_support (mu := V.weight) and measure_mono_null.
Membership x ∈ V.support unfolds to x ∈ U ∧ x ∈ V.weight.support, so hx.2 and the anonymous constructor work.

Remark (verified Lean realization; not part of the mathematical argument). The declaration below was compiled in this decomposition session (attempt 5, fresh scratch root; Lean v4.35.0-rc3, Mathlib 25730c7c, simongmt 2b366308) inside `namespace GMT.Ch05` / `namespace Submission`, in a module importing a freshly compiled copy of the frozen GMT/Ch05/Submission.lean, with the contract's `open MeasureTheory Metric Set Filter Topology`, `open scoped ENNReal NNReal` and `open RectifiableVarifold` in effect. The candidate module compiled with no errors. Its only `sorry`s were the two sibling contracts lgc_tangent_plane_ae and lgc_density_monotonicity, which this child does not use. In the contract scope, `theorem _root_.HumanizeNodeComparator.target_<name> : (<frozen type>) := by exact Submission.<name>` type-checks against the compiled module, and `#print axioms` lists only propext, Classical.choice and Quot.sound. The declaration can be pasted into GMT/Ch05/Submission.lean inside `namespace Submission`, before `main_theorem`.

theorem lgc_support_closest_point : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (ρ : ℝ) (ζ : Amb n ℓ), (0 : Amb n ℓ) ∈ V.support → closedBall (0 : Amb n ℓ) ρ ⊆ U → ‖ζ‖ + infDist ζ V.support ≤ ρ → ∃ y ∈ V.support, dist y ζ = infDist ζ V.support ∧ V.weight (ball ζ (infDist ζ V.support)) = 0 := by
  intro n ℓ U V ρ ζ h0 hB hsum
  set S := V.weight.support with hS
  have hSc : IsClosed S := Measure.isClosed_support
  have hVS : V.support ⊆ S := fun x hx => hx.2
  have hVne : V.support.Nonempty := ⟨0, h0⟩
  have hSne : S.Nonempty := hVne.mono hVS
  obtain ⟨y, hyS, hy⟩ := hSc.exists_infDist_eq_dist hSne ζ
  have hle : infDist ζ S ≤ infDist ζ V.support := infDist_le_infDist_of_subset hVS hVne
  have hyU : y ∈ U := by
    apply hB
    rw [mem_closedBall, dist_zero_right]
    have : ‖y‖ ≤ ‖ζ‖ + dist ζ y := by
      rw [dist_eq_norm]
      calc ‖y‖ = ‖ζ - (ζ - y)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖ζ‖ + ‖ζ - y‖ := norm_sub_le _ _
    linarith
  have hyV : y ∈ V.support := ⟨hyU, hyS⟩
  have hge : infDist ζ V.support ≤ dist ζ y := infDist_le_dist_of_mem hyV
  have heq : dist ζ y = infDist ζ V.support := le_antisymm (hy ▸ hle) hge
  refine ⟨y, hyV, by rw [dist_comm]; exact heq, ?_⟩
  apply measure_mono_null _ (Measure.measure_compl_support (μ := V.weight))
  intro x hx hxS
  rw [mem_ball] at hx
  have : infDist ζ S ≤ dist ζ x := infDist_le_dist_of_mem hxS
  rw [dist_comm] at hx
  linarith

## Key steps

1. S = spt mu is closed, nonempty and contains V.support
2. A nearest point y of S to zeta exists (proper space), and infDist(zeta, S) <= d gives dist(zeta, y) <= d
3. |y| <= |zeta| + d <= rho puts y in B_rho(0) ⊆ U, hence in V.support, forcing dist(y, zeta) = d = infDist(zeta, S)
4. ball(zeta, d) misses S, so mu(ball(zeta, d)) <= mu(complement of spt mu) = 0

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json (project ea5607598f3133b40a13241f2e51517a8c6423cd, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum GMT/Ch05/Submission.lean GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Contract.lean (all c966f51efddb5a68ce15ef2a2a322fd9df0ca69da4626c7acef05b05d1691e12)`
- `rg -n 'lgc_|hsNormSq_bounds|support_closest_point|rotated_graph_slope|hole_annulus_lower|hole_split_upper' <snapshot>/project (no match)`
- `rg -n 'hsNormSq' <snapshot>/project (only the contract definition, Submission.lean:47, and its uses)`
- `rg -n 'lemma isClosed_support|lemma measure_compl_support' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `rg -n 'exists_infDist_eq_dist|theorem infDist_le_infDist_of_subset|theorem infDist_le_dist_of_mem' <snapshot>/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `rg -n 'dist_starProjection_eq_infDist|theorem starProjection_norm_le|HasOrthogonalProjection.ofCompleteSpace' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `rg -n 'integrableOn_of_bounded' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean; rg -n 'integral_mono_of_nonneg' .../Integral/Bochner/Basic.lean; rg -n 'theorem setIntegral_mono_set|theorem integral_indicator|theorem setIntegral_const' .../Integral/Bochner/Set.lean`
- `rg -n 'isClosed_range' .../Topology/MetricSpace/Antilipschitz.lean; rg -n 'sum_mul_sq_le_sq_mul_sq' .../Algebra/Order/BigOperators/Ring/Finset.lean; rg -n 'comp_aestronglyMeasurable₂' .../MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `python3: lean_name collision scan of <run>/dag.json for the five names; grep of <run>/nodes/*/decomposition-v*.json (other nodes), .humanize/math-wiki and .swarm-worktrees/*/gmt-ch05/GMT/Ch05/Submission.lean (159 files): no match`
- `python3: max_nodes in .humanize/swarm-configs/e7e4b943ce8d47d69f960d0598137f28.json (200) and 11abe17eae34407eb92f02a80299a0ca.json (1000); len(dag.json nodes); grep -n 'remaining = self.config.max_nodes' /runtime/flows/gmt-claude-a2c7949d39d0/_recursive_lean/runtime.py`
- `grep -n '(9)|(10)' and sed -n 470,600p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt (printed proof of Simon 2.6, displays (9)-(10), pp. 112-113)`
- `lean -o /tmp/lgc-hole-v5-x104/olean/GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean (fresh byte copy of the frozen Submission)`
- `lean -o /tmp/lgc-hole-v5-x104/olean/Cand/Cand.olean Cand/Cand.lean (sibling contracts sorry + five children + assembly)`
- `lean Cand/Types.lean; lean Cand/Exact.lean; lean Cand/Comparator.lean; lean Cand/AsmOnly.lean; lean Cand/Inst.lean (all exit 0)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Antilipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-graph-corollary-a1-hole-estimate-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-graph-corollary-a1-hole-estimate-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-graph-corollary-a1-hole-estimate-a1/decomposition-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-graph-corollary-a1-hole-estimate-a1/decomposition-audit-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-approximation-a1-hole-estimate-a1/decomposition-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/swarm-configs/e7e4b943ce8d47d69f960d0598137f28.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/swarm-configs/11abe17eae34407eb92f02a80299a0ca.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/cluster-state/logs/gmt-ch05/e7e4b943ce8d47d69f960d0598137f28.log`
- `/runtime/flows/gmt-claude-a2c7949d39d0/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/tmp/lgc-hole-v5-x104/src/Cand/Cand.lean`
- `/tmp/lgc-hole-v5-x104/src/Cand/Types.lean`
- `/tmp/lgc-hole-v5-x104/src/Cand/Exact.lean`
- `/tmp/lgc-hole-v5-x104/src/Cand/Comparator.lean`
- `/tmp/lgc-hole-v5-x104/src/Cand/AsmOnly.lean`
- `/tmp/lgc-hole-v5-x104/src/Cand/Inst.lean`

Snapshot and contract. manifest.json pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace Submission.lean, the workspace Contract.lean and the snapshot Contract.lean are byte-identical (sha256 c966f51e…). The snapshot project contains none of the five proposed names; hsNormSq occurs only as the contract definition and its uses. No existing hsNormSq/operator-norm comparison for continuous linear maps exists to reuse. The accepted wiki theorem hsNorm_starProjection_trace_identities has a different type, so it cannot be reused by exact name.
Mathlib facts used by the child proofs, all present in the snapshot:
- isClosed_support and measure_compl_support (Measure/Support.lean:115, 202)
- IsClosed.exists_infDist_eq_dist, infDist_le_dist_of_mem and infDist_le_infDist_of_subset (HausdorffDistance.lean:615, 500, 505)
- HasOrthogonalProjection.ofCompleteSpace, dist_starProjection_eq_infDist and starProjection_norm_le (Projection/Basic.lean:53, 234, 386)
- Measure.integrableOn_of_bounded (IntegrableOn.lean:716) and integral_mono_of_nonneg (Bochner/Basic.lean:676)
- integral_indicator, setIntegral_const and setIntegral_mono_set (Bochner/Set.lean:185, 524, 737)
- AntilipschitzWith.isClosed_range (Antilipschitz.lean:175) and Finset.sum_mul_sq_le_sq_mul_sq (Ring/Finset.lean:171)
- Continuous.comp_aestronglyMeasurable₂ (AEStronglyMeasurable.lean:263)
The printed proof of Simon 2.6 (chapter-05.txt, displays (9)-(10), pp. 112-113) matches the supplied corrected steps.
Names and activation. None of the five names is reserved in dag.json, in other nodes' proposals, in the math wiki or in the 159 proof worktrees. The earlier accepted splits were blocked only by max_nodes = 200 in the previous worker's config. The current worker has max_nodes = 1000 and dag.json has fewer than 230 nodes.
Lean (this session). All six frozen types elaborate. The five child proofs compile with only standard axioms. The assembly proves the exact selected parent type from the five child types and the two sibling contracts.
