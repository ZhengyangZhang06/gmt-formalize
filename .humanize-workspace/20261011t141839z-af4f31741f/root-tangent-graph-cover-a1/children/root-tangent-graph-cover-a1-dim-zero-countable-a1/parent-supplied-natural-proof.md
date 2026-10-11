# Parent-supplied natural-language proof

- Parent DAG node: `root.tangent_graph_cover-a1`
- Child DAG node: `root.tangent_graph_cover-a1.dim_zero_countable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof (degenerate dimension n = 0): every tangent point is an atom of the σ-finite weight measure, and a σ-finite measure has at most countably many atoms. Uses the sibling lower_mass_bound (Submission.tgc_tangent_weight_lower_bound) with n = 0. Notation: μ := V.weight.

1. Atoms are countable. μ is σ-finite (instance Varifold.weight.instSigmaFinite), hence s-finite. The singletons {y}, y ∈ ℝ^N, are measurable (measurableSet_singleton) and pairwise disjoint (Set.disjoint_singleton), so by Measure.countable_meas_pos_of_disjoint_iUnion the set A₀ := {y : 0 < μ({y})} is countable. It suffices to prove that every x in the set of the statement satisfies μ({x}) > 0: then that set is contained in A₀ and is countable (Set.Countable.mono).

2. A positive lower bound near x. Let HasTangentPlane V x T θ. Then x ∈ U and θ > 0. ω_0 := unitBallVolume 0 = volume(ball(0,1)) in EuclideanSpace ℝ (Fin 0) is positive (Metric.measure_ball_pos: volume is an additive Haar measure, so it charges nonempty open sets). So a := ofReal θ · ω_0 > 0 (ENNReal.mul_pos), and there is c with 0 < c < a (exists_between in [0,∞]). By lower_mass_bound with n = 0: eventually as t → 0 in 𝓝[>] 0, c · ofReal(t)^0 ≤ μ(closedBall(x,t)); since ofReal(t)^0 = 1, this says c ≤ μ(closedBall(x,t)).

3. Finite mass near x. U is open (V.isOpen_domain) and x ∈ U, so there is R > 0 with ball(x,R) ⊆ U (Metric.isOpen_iff). closedBall(x,R/2) ⊆ ball(x,R) is compact and contained in U, so μ(closedBall(x,R/2)) < ∞ (Varifold.weight_finite_on_compact).

4. Continuity from above. Let s_j := closedBall(x, (R/2)/(j+1)) for j ∈ ℕ. The s_j are closed (so measurable), decreasing in j, μ(s_0) < ∞ by step 3, and ⋂_j s_j = {x} (x lies in every s_j; if y ≠ x choose j with (R/2)/(j+1) < dist(y,x), possible since (R/2)/(j+1) → 0). By tendsto_measure_iInter_atTop, μ(s_j) → μ(⋂_j s_j) = μ({x}). The radii (R/2)/(j+1) are positive and tend to 0 (tendsto_one_div_add_atTop_nhds_zero_nat), so they tend to 0 within (0,∞), i.e. in 𝓝[>] 0 (tendsto_nhdsWithin_iff); by step 2, c ≤ μ(s_j) for all sufficiently large j. Passing to the limit (ge_of_tendsto), c ≤ μ({x}), so μ({x}) ≥ c > 0.

5. By steps 1 and 4 the set of tangent points is contained in the countable set A₀, hence is countable. ∎

## Key steps

1. The atoms {y : 0 < μ_V{y}} of the σ-finite weight are countable (countable_meas_pos_of_disjoint_iUnion).
2. lower_mass_bound with n = 0 and 0 < c < θ ω_0 gives c ≤ μ_V(B_t(x)) for small t > 0.
3. x ∈ U gives finite mass of a small closed ball; continuity from above along B_{R/(2(j+1))}(x) ↓ {x} yields μ_V({x}) ≥ c > 0.
4. So every tangent point is an atom; the set of tangent points is countable.

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
