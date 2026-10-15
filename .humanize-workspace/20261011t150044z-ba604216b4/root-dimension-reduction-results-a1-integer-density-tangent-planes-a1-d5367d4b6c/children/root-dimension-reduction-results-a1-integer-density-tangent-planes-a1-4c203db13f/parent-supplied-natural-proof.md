# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.no_infinite_planar_pieces-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.no_infinite_planar_pieces-a1.disjoint_packing-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent proof of idtp_tdc_no_infinite_planar_pieces (the finite-mass count), stated for an arbitrary pairwise disjoint family D_i in place of the discs Q_i ∩ B_ρ(z_i), the ball B_r(0) in place of B_{R+ρ}(0), and an arbitrary c ≠ 0 in place of ω_2·ofReal(ρ²).
1. (The common ball has finite measure.) The closed ball closedBall(0, r) of ℝ^P is compact because ℝ^P is a proper metric space (isCompact_closedBall), so μ(closedBall(0, r)) ≠ ∞ by hypothesis. Every D_i satisfies D_i ⊆ B_r(0) ⊆ closedBall(0, r), hence ⋃_{i∈ℕ} D_i ⊆ closedBall(0, r) and, by monotonicity, μ(⋃_{i∈ℕ} D_i) ≤ μ(closedBall(0, r)).
2. (Countable additivity.) The sets D_i are Borel and pairwise disjoint (D_i ∩ D_j = ∅ for i ≠ j), so μ(⋃_{i∈ℕ} D_i) = Σ_{i∈ℕ} μ(D_i) (measure_iUnion).
3. (The series diverges.) Since c ≤ μ(D_i) for every i ∈ ℕ, Σ_{i∈ℕ} c ≤ Σ_{i∈ℕ} μ(D_i) (ENNReal.tsum_le_tsum). Since ℕ is infinite and c ≠ 0, Σ_{i∈ℕ} c = ∞ in [0, ∞] (ENNReal.tsum_const_eq_top_of_ne_zero).
4. (Contradiction.) Combining steps 1–3: ∞ = Σ_{i∈ℕ} c ≤ Σ_{i∈ℕ} μ(D_i) = μ(⋃_{i∈ℕ} D_i) ≤ μ(closedBall(0, r)), so μ(closedBall(0, r)) = ∞ (top_le_iff), contradicting step 1. Hence the assumptions are contradictory, i.e. False. ∎

## Key steps

1. All D_i lie in the compact closed ball closedBall(0, r), whose μ-measure is finite.
2. Countable additivity: μ(⋃_i D_i) = Σ_i μ(D_i).
3. Σ_{i∈ℕ} μ(D_i) ≥ Σ_{i∈ℕ} c = ∞ because c ≠ 0.
4. Monotonicity forces μ(closedBall(0, r)) = ∞, a contradiction.

## Reference use

### local-project

Queries:
- `cat nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-d5367d4b6c/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.md}`
- `python3 scan of dag.json: lean_statement and status for dimred_im_mass_measure, idtp_tdc_subspace_ball_measure, idtp_tdc_no_infinite_planar_pieces, rsd_massOn_eq_measure, codim1_subspace_ball_euclideanHausdorff, cone_current_imrep_measure_smul_image, and every child of two_dim_cone_density-a1`
- `python3 regex scan of dag.json lean_statements for 'IsFiniteMeasureOnCompacts|\.measure \(ball|\.measure K|OuterRegular|IsLocallyFiniteMeasure|\(μ ν : Measure|Measure \(Euclid P\)\)|R\.measure .* < ∞|R\.measure .* ≠ ∞'`
- `python3 print of exact statements: rsd_imrep_compact_measure_ne_top, cmc_ml_measure_eq_of_eq_on_open_subsets, lcmp_measure_le_add_of_open_nhds, cmr_null_of_compact_null, dorag_lip_vitali_two_measure_bound, cbr_imRep_measure_basic, rsd_mw_wlm_exists_open_measure_between`
- `grep -c / grep -rl / grep -rn 'idtp_tdc_nipp_local_comparison|idtp_tdc_nipp_disjoint_packing|idtp_tdc_nipp|nipp_' over dag.json, nodes/ and GMT/`
- `cat nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-edecc539dd/decomposition-scope-v1.json; python3 summary of decomposition-v1.json (parent split rationale, cross-branch black boxes)`
- `git show 01ae2c59e8d725f9f3839402fe6fe9bf93c32c3a:GMT/Ch07/Submission.lean | grep -n '^theorem' (accepted dimred_im_mass_measure candidate)`
- `grep -n 'unitBallVolume|def HasMassDensity' GMT/Ch07/Submission.lean`
- `grep -rn 'μHE\[' mathlib/Mathlib`
- `rg -n 'theorem _root_.Set.exists_isOpen_lt_of_lt|of_pseudoMetrizableSpace_of_isFiniteMeasure' Mathlib/MeasureTheory/Measure/Regular.lean`
- `rg -n 'theorem isOpen_iUnion_countable' Mathlib/Topology/Bases.lean; rg -n 'theorem Countable.exists_eq_range' Mathlib/Data/Set/Countable.lean`
- `rg -n 'disjoint_disjointed|iUnion_disjointed|disjointed_subset' Mathlib/Order/Disjointed.lean; rg -n 'MeasurableSet.disjointed' Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `rg -n 'theorem measure_iUnion' Mathlib/MeasureTheory/Measure/NullMeasurable.lean; rg -n 'tsum_const_eq_top_of_ne_zero|protected theorem tsum_le_tsum' Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `rg -n 'isCompact_closedBall' Mathlib/Topology/MetricSpace/ProperSpace.lean; rg -n 'theorem withDensity_apply' Mathlib/MeasureTheory/Measure/WithDensity.lean; rg -n 'theorem restrict_restrict' Mathlib/MeasureTheory/Measure/Restrict.lean`
- `rg -n 'theorem Submodule.closed_of_finiteDimensional' Mathlib/Topology/Algebra/Module/FiniteDimension.lean; rg -n 'theorem measure_ball_pos' Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `rg -n 'le_of_forall_lt|le_of_forall_gt|forall_gt' Mathlib/Order/Basic.lean`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; lake-manifest.json revs vs manifest.json`
- `lake env lean /tmp/nipp-decomp/Probe0.lean; lake env lean /tmp/nipp-decomp/Stmts.lean; lake env lean /tmp/nipp-decomp/Validate.lean (#print axioms nipp_check_disjoint_packing, nipp_check_local_comparison, nipp_assembly_check)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-d5367d4b6c/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-d5367d4b6c/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-d5367d4b6c/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-edecc539dd/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-edecc539dd/decomposition-scope-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Disjointed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/ProperSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/tmp/nipp-decomp/Probe0.lean`
- `/tmp/nipp-decomp/Stmts.lean`
- `/tmp/nipp-decomp/Validate.lean`
- `/tmp/nipp-decomp/draft.json`
- `/tmp/nipp-review/Elab.lean`
- `/tmp/nipp-review/Assembly.lean`
- `/tmp/nipp-review/Children.lean`
- `/tmp/nipp-review/NameFree.lean`
- `/tmp/nipp-review/Probe.lean`

Pins and contract:
- The pins match manifest.json: project HEAD b4d606db, mathlib 25730c7c, SimonGMT 2b366308.
- The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.
- The frozen selected type elaborates. unitBallVolume n is volume (ball (0 : Euclid n) 1) (Submission.lean:143). μHE[d] is Mathlib's euclideanHausdorffMeasure (Geometry/Euclidean/Volume/Measure.lean:72).

Mathlib facts used by the children, all present in the snapshot:
- Set.exists_isOpen_lt_of_lt (Regular.lean:359) and the WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure instance (Regular.lean:1072).
- TopologicalSpace.isOpen_iUnion_countable (Bases.lean:932) and Set.Countable.exists_eq_range (Countable.lean:149).
- disjoint_disjointed, disjointed_subset and iUnion_disjointed (Disjointed.lean:206, 316, 320), and MeasurableSet.disjointed (Constructions.lean:113).
- measure_iUnion (NullMeasurable.lean:241), ENNReal.tsum_le_tsum and ENNReal.tsum_const_eq_top_of_ne_zero (InfiniteSum/ENNReal.lean:116, 167).
- isCompact_closedBall, the exported ProperSpace field (ProperSpace.lean:39/41), and le_of_forall_gt, generated by to_dual from le_of_forall_lt (Order/Basic.lean:351).

Facts used only by the parent's glue: withDensity_apply, Measure.restrict_restrict, Submodule.closed_of_finiteDimensional (FiniteDimension.lean:531) and measure_ball_pos (OpenPos.lean:212).

Reuse:
- dimred_im_mass_measure is accepted with the exact frozen type the parent proof cites. idtp_tdc_subspace_ball_measure is the parent's existing sibling prerequisite (status decomposing).
- No DAG declaration has either child's type. cmc_ml_measure_eq_of_eq_on_open_subsets (accepted) is an equality version, and lcmp_measure_le_add_of_open_nhds (accepted) covers compact sets only. rsd_imrep_compact_measure_ne_top (accepted) covers only step 1's finiteness.
- The new names idtp_tdc_nipp_local_comparison and idtp_tdc_nipp_disjoint_packing have no match in dag.json, nodes/ or GMT/.

Lean checks:
- Both child lean_statements elaborate after import GMT.Ch07.Submission.
- Validate.lean proves both children at their exact types and derives the exact selected type from the two children plus the byte-identical frozen types of dimred_im_mass_measure and idtp_tdc_subspace_ball_measure. Every #print axioms reports [propext, Classical.choice, Quot.sound].
- The independent reviewer reproduced all of this in /tmp/nipp-review and approved.
