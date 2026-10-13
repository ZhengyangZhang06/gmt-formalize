# Parent-supplied natural-language proof

- Parent DAG node: `root.tangent_graph_cover-a1`
- Child DAG node: `root.tangent_graph_cover-a1.cone_linear_algebra-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3, (3.1) and (3.2), of the parent proof with c = L/4 and γ = L/8. The first conclusion is the inequality |q_T w| ≥ (c/4)|w| = (L/16)|w| established inside (3.2); by Pythagoras it says w ∈ K_α(T) = {|p_T w| ≤ α|w|} with α = (1 − L²/256)^{1/2}. Notation: for S ∈ G(N,n), p_S := Grassmannian.project S and q_S(u) := u − p_S u; p := p_P, q := q_P.

0. Projection facts. For S ∈ G(N,n), p_S is linear, symmetric (Grassmannian.projectionLinearMap_isSymmetric: ⟨p_S a, b⟩ = ⟨a, p_S b⟩) and idempotent (Grassmannian.project_project). Hence for every u: ⟨p_S u, u − p_S u⟩ = ⟨p_S u, u⟩ − ⟨p_S u, p_S u⟩ = ⟨p_S u, u⟩ − ⟨u, p_S(p_S u)⟩ = ⟨p_S u, u⟩ − ⟨u, p_S u⟩ = 0, so Pythagoras (norm_add_sq_eq_norm_sq_add_norm_sq_real for p_S u + (u − p_S u) = u) gives ‖u‖² = ‖p_S u‖² + ‖q_S u‖². In particular ‖q_S u‖ ≤ ‖u‖. Also q_S is linear: q_S(a + b) = q_S a + q_S b. (These are proved inline; no extra named lemma is needed.)

1. |q v| > (L/2)|v|. Put a := ‖q v‖ and b := ‖p v‖, so ‖v‖² = b² + a², and by hypothesis a > L b ≥ 0. Squaring nonnegative quantities, a² > L²b² = L²(‖v‖² − a²). Since L ≤ 1, L²a² ≤ a², hence L²‖v‖² = L²b² + L²a² < a² + a² = 2a². Then (2a)² = 4a² > 2L²‖v‖² ≥ (L‖v‖)², and as 2a ≥ 0 and L‖v‖ ≥ 0 we get 2a > L‖v‖, i.e. a > (L/2)‖v‖.

2. |q_T v| > (L/4)|v|. q_T v − q v = p v − p_T v, so ‖q_T v − q v‖ = ‖p_T v − p v‖ ≤ (L/4)‖v‖ (tilt hypothesis with u = v). By the reverse triangle inequality (norm_sub_norm_le), ‖q_T v‖ ≥ ‖q v‖ − ‖q v − q_T v‖ > (L/2)‖v‖ − (L/4)‖v‖ = (L/4)‖v‖.

3. ‖w‖ ≤ 2‖v‖. ‖w‖ ≤ ‖v‖ + ‖w − v‖ ≤ (1 + L/8)‖v‖ ≤ 2‖v‖, using L ≤ 1 and ‖v‖ ≥ 0. This is the second conclusion.

4. (L/16)‖w‖ ≤ ‖q_T w‖. By linearity, q_T w = q_T v + q_T(w − v), and by step 0, ‖q_T(w − v)‖ ≤ ‖w − v‖ ≤ (L/8)‖v‖. Hence ‖q_T w‖ ≥ ‖q_T v‖ − ‖q_T(w − v)‖ > (L/4)‖v‖ − (L/8)‖v‖ = (L/8)‖v‖ ≥ (L/16)‖w‖, the last step by step 3 and L > 0. As q_T w = w − p_T w, this is the first conclusion. ∎

## Key steps

1. Symmetric idempotent projections satisfy Pythagoras ‖u‖² = ‖p_S u‖² + ‖u − p_S u‖², so ‖u − p_S u‖ ≤ ‖u‖.
2. L‖p v‖ < ‖q v‖ and L ≤ 1 give ‖q v‖ > (L/2)‖v‖.
3. The tilt bound ‖p_T − p‖ ≤ L/4 gives ‖q_T v‖ > (L/4)‖v‖.
4. ‖w‖ ≤ (1 + L/8)‖v‖ ≤ 2‖v‖.
5. ‖q_T w‖ ≥ ‖q_T v‖ − ‖w − v‖ > (L/8)‖v‖ ≥ (L/16)‖w‖.

## Reference use

### local-project

Queries:
- `cat local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum project/GMT/Ch08/Contract.lean and workspace GMT/Ch08/Submission.lean (both 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `rg -n 'notation.*μHE|def euclideanHausdorffMeasure|theorem Isometry.euclideanHausdorffMeasure_image|euclideanHausdorffMeasure_eq_volume' mathlib/Mathlib`
- `rg -n 'theorem addHaar_closedBall' mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `rg -n 'countable_meas_pos_of_disjoint_iUnion|countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top' mathlib/Mathlib`
- `rg -n 'theorem tendsto_measure_cthickening' mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean`
- `rg -n 'theorem cthickening_closedBall|theorem mem_cthickening_of_dist_le|theorem cthickening_subset_of_subset|theorem mem_cthickening_iff' mathlib/Mathlib`
- `rg -n 'theorem exists_dense_seq|def denseSeq|theorem denseRange_denseSeq' mathlib/Mathlib/Topology`
- `rg -n 'theorem countable_iff_exists_subset_range' mathlib/Mathlib`
- `grep -n 'structure Varifold|def weight|instSigmaFinite|finite_on_compact|def project|def plane|finrank_plane|instCompactSpace' simongmt Poincare/SimonGMT/Chapter08/Varifold.lean`
- `rg -n 'theorem (norm_project|project_|inner_project)' simongmt Chapter08/*.lean; rg -n 'planeMeasure|locallyFinite_planeMeasure|unitBallVolume' simongmt`
- `#check after import GMT.Ch08.Submission for 35 cited lemmas (Scratch/Avail.lean)`
- `sed -n 100,280p book/sources/chapter-03-source.txt (printed proof of Ch. 3, Thm 1.6 ⇐)`
- `python3 validate_lean_statement (verifier/lean_contract.py) on the 7 statements; dag.json lean_name collision check`
- `lake env lean Scratch/Challenge_<key>.lean (7 files) and Scratch/Assembly.lean in a /tmp copy importing GMT.Ch08.Submission with the comparator's replayed scope`
- `lake env lean Scratch/Full2.lean and Scratch/FullCheck.lean (proofs of all 7 children with exact frozen types and of the parent; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Normed/Module/Ball/Pointwise.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Data/Set/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/RadialFirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/EuclideanHausdorffUpper.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-03-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-tangent-graph-cover-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`

The snapshot is project 63436ae6 plus Mathlib 25730c7c, and its Contract is byte-identical to the workspace Submission. Mathlib has no varifold theory, so no existing declaration matches any child. Mathlib does supply every tool the children use: Isometry.euclideanHausdorffMeasure_image and EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean:131,187), Measure.addHaar_closedBall (EqHaar.lean:500), Measure.countable_meas_pos_of_disjoint_iUnion (SFinite.lean:305), tendsto_measure_cthickening_of_isClosed (BorelSpace/Metric.lean:143), cthickening_closedBall (Normed/Module/Ball/Pointwise.lean:318), mem_cthickening_of_dist_le (Thickening.lean:201), denseSeq/denseRange_denseSeq (Topology/Bases.lean:373,378) and countable_iff_exists_subset_range (Data/Set/Countable.lean:119). The SimonGMT Varifold API is in the import closure of GMT.Ch08.Submission (Grassmannian.project/plane/finrank_plane/projectionLinearMap_isSymmetric/project_project/projectionLinearMap_apply_of_mem/instCompactSpace, Varifold.weight/weight_finite_on_compact/weight.instSigmaFinite). The SimonGMT lemmas norm_project_sq_add_norm_normalProject_sq (Chapter08/RadialFirstVariation.lean) and planeMeasure_unit_closedBall/locallyFinite_planeMeasure (Chapter04/TangentDensity.lean) are NOT in that closure (#check fails), so the child proofs derive Pythagoras and the plane-ball formula directly. All seven statements elaborate in the comparator scope and pass the validator. Scratch proofs of all seven with their exact frozen types, and of the parent from them, use only propext, Classical.choice and Quot.sound.
