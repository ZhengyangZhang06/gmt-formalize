# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1.canonical_representation-a1.null_transfer-a1`
- Child DAG node: `root.integral_compactness-a1.canonical_representation-a1.null_transfer-a1.open_subset_measure_lt-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the supplied proof of intcpt_canon_hausdorff_null_of_weight_null (small open neighbourhoods). That step is the special case W = W_y, A = Z_{y,k}, μ(A) = 0 < ε. The argument below is the same, with the hypothesis μ(A) < ε in place of μ(A) = 0 < ε. For a non-measurable A, μ(A) is the outer measure.

1. Finite restriction. Let ν := μ.restrict W, the restriction of μ to W. For measurable S, ν(S) = μ(S ∩ W) (Measure.restrict_apply). In particular ν(ℝ^N) = μ(W) (Measure.restrict_apply_univ), which is finite by hypothesis. So ν is a finite measure (IsFiniteMeasure).

2. Outer regularity. ℝ^N is a metric space with its Borel σ-algebra. Every finite measure on a pseudo-metrizable space with Borel σ-algebra is weakly regular, and weakly regular measures are outer regular (Mathlib instance Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure; class WeaklyRegular extends OuterRegular). Hence ν is outer regular.

3. ν(A) < ε. The restriction is dominated by μ on every set, measurable or not: ν(A) ≤ μ(A) (Measure.restrict_apply_le). With the hypothesis μ(A) < ε this gives ν(A) < ε.

4. An open set for ν. Outer regularity applies to arbitrary sets (Set.exists_isOpen_lt_of_lt). Since ν(A) < ε, there is an open O' ⊇ A with ν(O') < ε.

5. Cutting down to W. Put O := O' ∩ W.
- O is open, as the intersection of two open sets.
- A ⊆ O' by step 4 and A ⊆ W by hypothesis, so A ⊆ O.
- O ⊆ W.

6. The measure of O. O' is open, hence Borel measurable. So by step 1, ν(O') = μ(O' ∩ W) = μ(O), and therefore μ(O) = ν(O') < ε.

7. O is open with A ⊆ O, O ⊆ W and μ(O) < ε, as required. If ε = 0 the hypothesis μ(A) < 0 is impossible and the statement holds vacuously; if ε = ∞ the argument above applies unchanged. ∎

Lean route (verified without sorry in scratch; import GMT.Ch08.Submission only, inside namespace GMT.Ch08 after the contract opens):
  intro N μ W A ε hW hWfin hAW hAε
  have : IsFiniteMeasure (μ.restrict W) := ⟨by rw [Measure.restrict_apply_univ]; exact hWfin.lt_top⟩
  obtain ⟨O', hAO', hO', hO'ε⟩ := Set.exists_isOpen_lt_of_lt A ε ((Measure.restrict_apply_le W A).trans_lt hAε)
  refine ⟨O' ∩ W, hO'.inter hW, subset_inter hAO' hAW, inter_subset_right, ?_⟩
  rwa [Measure.restrict_apply hO'.measurableSet] at hO'ε

## Key steps

1. ν := μ.restrict W is a finite measure, since ν(ℝ^N) = μ(W) < ∞.
2. Finite Borel measures on metric spaces are outer regular (WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure).
3. ν(A) ≤ μ(A) < ε, so Set.exists_isOpen_lt_of_lt gives an open O' ⊇ A with ν(O') < ε.
4. O := O' ∩ W is open with A ⊆ O ⊆ W, and μ(O) = ν(O') < ε by Measure.restrict_apply.

## Reference use

### local-project

Queries:
- `cat local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum GMT/Ch08/Submission.lean GMT/Ch08/Contract.lean; git show ed693c4c6c3c8d593f8b77746808c8d33ea692bb:GMT/Ch08/Submission.lean | sha256sum (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `python3 -I /tmp/nt-decomp-scripts/closure.py GMT.Ch08.Contract (recursive import scan: SimonGMT Chapter01 modules in closure = Basic, Hausdorff, MetricCriterion only)`
- `grep -n 'theorem mul_simonHausdorff_le_of_le_dimensionalUpperDensity' -A 25 Chapter01/DensityComparison.lean; grep -n 'def dimensionalDensityQuotient|def dimensionalUpperDensity' Chapter01/Densities.lean`
- `grep -n 'def realUnitBallVolume|realUnitBallVolume_zero|simonHausdorffMeasureReal_toOuterMeasure|def simonHausdorffOuterMeasureReal|def simonHausdorffMeasureReal' Chapter01/Hausdorff.lean; grep -n 'realUnitBallVolume_nat_eq|volume_euclidean_ball_eq' Chapter01/EuclideanHausdorffUpper.lean`
- `sed -n 1,47p Chapter02/AreaLiteral.lean; grep -rn 'simonAreaNormalization_eq_one|simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure|def simonAreaNormalization' Poincare/SimonGMT (normalization rests on Chapter01.EuclideanNormalization)`
- `sed -n 1,120p mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (μHE[d] := addHaarScalarFactor volume μH[d] • μH[d])`
- `grep Mathlib: 'theorem _root_.Set.exists_isOpen_lt_of_lt' / 'of_pseudoMetrizableSpace_of_isFiniteMeasure' / 'class WeaklyRegular ... extends OuterRegular' (MeasureTheory/Measure/Regular.lean:359,1072,324); 'theorem isOpen_iUnion_countable' (Topology/Bases.lean:932); 'theorem restrict_apply |restrict_apply_univ|restrict_apply_le' (MeasureTheory/Measure/Restrict.lean:75,168,176); 'theorem exists_surjective_nat' (Basic/Countable/Defs.lean:60); 'theorem isOpen_iff' (Topology/MetricSpace/Pseudo/Defs.lean:833)`
- `python3 -I dag.json scans: related types/statuses (frt_hausdorff_null_of_weight_null same proposition speculative-ready split; frt_hnw_exists_open_superset_measure_lt decomposing; frt_hnw_unitBallVolume_eq_gamma rlcr-lean; frt_weq_mul_hausdorff_le_of_upper_density decomposing; intcpt_vdb_open_thickening_exhaustion accepted with different type; allard_tc_tpr_hausdorff_null_of_weight_null rlcr-lean leaf); lean_name scan for intcpt_canon_nt_* (none); grep -rlo intcpt_canon_nt_ run dir (none)`
- `read nodes/root-first-rectifiability-a1-hausdorff-null-of-weight-null-a1/decomposition-v1.json and speculative-process-v1.log; nodes/root-allard-tangent-cones-a1-tangent-point-representation-a1-hausdorf-45afb42a40/{decomposition-v1.json,rlcr-plan-v1.md,rlcr-config-v1.json}`
- `git show c8f015c (allard leaf candidate: no import added, Vitali re-derivation); git show 33060dbe (frt speculative draft adds DensityComparison + AreaLiteral imports); git show 8a562da5 and fb766d9 (accepted leaves dropped draft imports)`
- `read controller /runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/leaf_verification.py (check_source_delta, check_git_delta), parent_verification.py (check_parent_git_delta), runtime.py (_leaf_author_task, _parent_author_task, _install_speculative_assumptions, _existing_lean_name_problem, _solve_children), docs/workflow-requirements.md; swarm config .humanize/swarm-configs/d5e67afb7c444987a44032dd98704644.json (leaf_lean_agent_review=False, nonleaf_lean_agent_review=False, speculative_parent_formalization=True)`
- `read verifier/gmt-compare.py (frozen_inputs deletes Submission.lean from byte check; candidate_inputs; contract_scope; child_modules)`
- `ch04 dag.json scan of non-leaf candidate imports (root.lipschitz_pieces-a1.regular_set_cover-a1 accepted at 17dc1f6803 with extra import Poincare.SimonGMT.Chapter02.AreaLipschitz)`
- `lake env lean /tmp/nt-decomp-lean/Children.lean (import GMT.Ch08.Submission only; both children proved, no messages); lake env lean /tmp/nt-decomp-lean/Parent.lean (+3 imports; parent proved; #print axioms propext, Classical.choice, Quot.sound)`
- `python3 -I /tmp/nt-decomp-scripts/gen.py (verifier gmt-compare.child_modules contract mode + lean_contract.validate_lean_statement on both child statements: OK); lake env lean gen/*__NodeChallenge.lean (elaborate, sorry warning only) and Sol_*.lean NodeSolution mimics (pass)`
- `python3 -I /tmp/nt-decomp-scripts/stub.py + lake env lean Stub.lean (fails only on copied '  open Classical in' line) and StubNoQuirk.lean (elaborates with both child axioms)`
- `independent reviewer subagent (/tmp/nt-review-adv): leaf check_source_delta simulation per child with negative import controls, composed-parent olean simulation, 41/41 GMT.Ch08 constant type/value hashes identical with the 3 imports; verdict ACCEPT`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/mathlib/Mathlib/Basic/Countable/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/EuclideanHausdorffUpper.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaNormalization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-canonical-representation-a1-null-transfer-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-canonical-representation-a1-null-transfer-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-hausdorff-null-of-weight-null-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-hausdorff-null-of-weight-null-a1/speculative-process-v1.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-tangent-point-representation-a1-hausdorf-45afb42a40/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-tangent-point-representation-a1-hausdorf-45afb42a40/rlcr-plan-v1.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-radon-compactness-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/swarm-configs/d5e67afb7c444987a44032dd98704644.json`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/parent_verification.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/docs/workflow-requirements.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/tmp/nt-decomp-scripts/closure.py`
- `/tmp/nt-decomp-scripts/gen.py`
- `/tmp/nt-decomp-scripts/stub.py`
- `/tmp/nt-decomp-lean/Children.lean`
- `/tmp/nt-decomp-lean/Parent.lean`
- `/tmp/nt-decomp-lean/gen/intcpt_canon_nt_open_cover_finite_measure__NodeChallenge.lean`
- `/tmp/nt-decomp-lean/gen/intcpt_canon_nt_exists_open_subset_measure_lt__NodeChallenge.lean`
- `/tmp/nt-decomp-lean/Sol_intcpt_canon_nt_open_cover_finite_measure.lean`
- `/tmp/nt-decomp-lean/Sol_intcpt_canon_nt_exists_open_subset_measure_lt.lean`
- `/tmp/nt-decomp-lean/Stub.lean`
- `/tmp/nt-decomp-lean/StubNoQuirk.lean`

The snapshot pins project 63436ae6 and Mathlib 25730c7c. Contract.lean, the workspace Submission.lean and this node's base ed693c4c Submission.lean are byte-identical.

Why the split:
- The supplied proof's key lemmas are outside GMT.Ch08.Submission's import closure: SimonGMT Chapter01.mul_simonHausdorff_le_of_le_dimensionalUpperDensity (DensityComparison), dimensionalUpperDensity (Densities), volume_euclidean_ball_eq (EuclideanHausdorffUpper) and Chapter02.simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure (AreaLiteral, resting on the isodiametric EuclideanNormalization).
- The controller forbids imports in leaf candidates but allows them for non-leaf parents; ch04 accepted such a parent at 17dc1f6803.
- So the import-dependent comparison stays in this node. Supplied steps 2 and 4 become import-free children built only on Mathlib: TopologicalSpace.isOpen_iUnion_countable, isCompact_closedBall and exists_surjective_nat for the first; Measure.restrict_apply_univ/restrict_apply_le/restrict_apply, the WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure outer-regularity instance and Set.exists_isOpen_lt_of_lt (valid for arbitrary sets) for the second.

Reuse: no existing DAG declaration has an identical type. The intcpt_canon_nt_* names are unused.

Lean checks:
- Both children compile with only `import GMT.Ch08.Submission`.
- Their comparator NodeChallenge and NodeSolution forms pass, and both statements pass validate_lean_statement.
- The parent assembly with the three imports proves the exact frozen type, with axioms propext, Classical.choice and Quot.sound only.
- An independent reviewer reproduced all checks, confirmed all 41 frozen GMT.Ch08 constants are unchanged by the imports, and returned ACCEPT.
