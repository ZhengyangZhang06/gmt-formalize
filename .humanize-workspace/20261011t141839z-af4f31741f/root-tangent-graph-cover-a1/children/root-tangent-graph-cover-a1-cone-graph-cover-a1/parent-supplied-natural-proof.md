# Parent-supplied natural-language proof

- Parent DAG node: `root.tangent_graph_cover-a1`
- Child DAG node: `root.tangent_graph_cover-a1.cone_graph_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 4–6 of the parent proof — uniform classes replacing Egoroff (printed (7)–(9)), the graph claim (printed (10)) and the closed graph pieces — for an abstract measure. The varifold enters the parent proof only through the lower mass bound (1.3) and the cone decay (1.4); here these are hypotheses (i) and (ii), and the parent's constant (2m)^{−1}ω_n is replaced by a_m := 1/m (ω_n is absorbed into c). Uses the sibling cone_linear_algebra (Submission.tgc_tilted_cone_inclusion). Notation: p := Grassmannian.project P, q(v) := v − p v; for T ∈ G(N,n), p_T := Grassmannian.project T; Tilt(T) :⟺ ∀ v, ‖p_T v − p v‖ ≤ (L/4)‖v‖; for x ∈ ℝ^N and t > 0, K(T,x,t) := {y : y ∈ closedBall(x,t) ∧ (L/16)‖y − x‖ ≤ ‖(y − x) − p_T(y − x)‖}; 'the graph inequality for (y,z)' means ‖q(y − z)‖ ≤ L‖p(y − z)‖. Only monotonicity of μ is used (no finiteness or measurability).

1. Constants. γ := L/8 ∈ (0, 1/8]. For integers m ≥ 1: a_m := 1/m > 0 and ε_m := a_m (γ/2)^n / 2 > 0. For every s ≥ 0, ε_m (2s)^n = a_m (γ/2)^n 2^n s^n / 2 = a_m (γs)^n / 2.

2. Uniform classes. For integers m, k ≥ 1 let E_{m,k} be the set of x ∈ ℝ^N for which there is T ∈ G(N,n) with Tilt(T) such that for every t ∈ (0, 1/k]:
 (i') ofReal(a_m t^n) ≤ μ(closedBall(x,t)), and (ii') μ(K(T,x,t)) ≤ ofReal(ε_m t^n).

3. The classes cover A. Let x ∈ A and take T, c from the hypothesis. As c ≠ 0, ENNReal.exists_inv_nat_lt gives m ∈ ℕ with (m : [0,∞])^{−1} < c; necessarily m ≥ 1 (for m = 0 the left side is ∞), and ofReal(a_m) = m^{−1} < c. Apply (ii) with ε := ofReal(ε_m) > 0. Both (i) and this instance of (ii) hold eventually in 𝓝[>] 0, so by Metric.mem_nhdsWithin_iff there is δ > 0 such that for all t ∈ (0,δ): c · ofReal(t)^n ≤ μ(closedBall(x,t)) and μ(K(T,x,t)) ≤ ofReal(ε_m) · ofReal(t)^n. Choose an integer k ≥ 1 with 1/k < δ (exists_nat_gt applied to 1/δ). For t ∈ (0, 1/k] we have t < δ, so ofReal(a_m t^n) = ofReal(a_m) · ofReal(t)^n ≤ c · ofReal(t)^n ≤ μ(closedBall(x,t)) and μ(K(T,x,t)) ≤ ofReal(ε_m) · ofReal(t)^n = ofReal(ε_m t^n) (ENNReal.ofReal_mul, ENNReal.ofReal_pow, t ≥ 0). Hence x ∈ E_{m,k} with witness T.

4. Graph property inside a class (printed (10)). CLAIM: if x, x' ∈ E_{m,k} and ‖x' − x‖ ≤ 1/(2k), then ‖q(x' − x)‖ ≤ L‖p(x' − x)‖. Suppose not, and put v := x' − x, so L‖p v‖ < ‖q v‖. Then v ≠ 0 (for v = 0 both sides vanish since p 0 = 0), so s := ‖v‖ satisfies 0 < s ≤ 1/(2k). Let T witness x ∈ E_{m,k}; at x' only (i') is used, so the witness for x' plays no role.
 (a) closedBall(x', γs) ⊆ K(T, x, 2s): for y with ‖y − x'‖ ≤ γs put w := y − x. Then w − v = y − x', so ‖w − v‖ ≤ (L/8)‖v‖, and cone_linear_algebra (applied to L, P, T, v, w with Tilt(T) and L‖p v‖ < ‖v − p v‖) gives (L/16)‖w‖ ≤ ‖w − p_T w‖ and ‖w‖ ≤ 2‖v‖ = 2s; that is, y ∈ closedBall(x, 2s) and y satisfies the cone inequality, so y ∈ K(T, x, 2s).
 (b) Since 0 < γs ≤ 2s ≤ 1/k (γ ≤ 1/8 < 2 and s ≤ 1/(2k)), (i') at x' with t = γs, monotonicity of μ with (a), and (ii') at x with t = 2s give
  ofReal(a_m (γs)^n) ≤ μ(closedBall(x', γs)) ≤ μ(K(T, x, 2s)) ≤ ofReal(ε_m (2s)^n).
 (c) As ε_m (2s)^n ≥ 0, ENNReal.ofReal_le_ofReal_iff turns (b) into a_m (γs)^n ≤ ε_m (2s)^n = a_m (γs)^n / 2 (step 1), contradicting a_m (γs)^n > 0. This proves the claim.

5. Closed pieces. Let (d_j)_{j∈ℕ} be a dense sequence in ℝ^N (ℝ^N is separable and nonempty: TopologicalSpace.denseSeq with denseRange_denseSeq). For m, k ≥ 1 and j ∈ ℕ put S_{m,k,j} := E_{m,k} ∩ closedBall(d_j, 1/(4k)) and Γ_{m,k,j} := closure(S_{m,k,j}).
 (a) Γ_{m,k,j} is closed (isClosed_closure).
 (b) Graph inequality on Γ_{m,k,j}: for y, z ∈ S_{m,k,j}, ‖y − z‖ ≤ ‖y − d_j‖ + ‖z − d_j‖ ≤ 1/(4k) + 1/(4k) = 1/(2k), so step 4 with x := z, x' := y gives ‖q(y − z)‖ ≤ L‖p(y − z)‖. The set F := {(y,z) ∈ ℝ^N × ℝ^N : ‖q(y − z)‖ ≤ L‖p(y − z)‖} is closed (isClosed_le of two continuous functions; p is continuous as a linear map on a finite-dimensional space), and S × S ⊆ F for S := S_{m,k,j}. Hence closure(S) × closure(S) = closure(S × S) ⊆ F (closure_prod_eq, closure_minimal): the graph inequality holds for all y, z ∈ Γ_{m,k,j}.
 (c) Covering: if x ∈ E_{m,k}, density gives j with dist(x, d_j) < 1/(4k) (DenseRange.exists_dist_lt), so x ∈ S_{m,k,j} ⊆ Γ_{m,k,j} (subset_closure).

6. Enumeration. Let π : ℕ → ℕ × ℕ × ℕ, π(i) := (i.unpair.1, i.unpair.2.unpair.1, i.unpair.2.unpair.2); π(Nat.pair a (Nat.pair b c)) = (a, b, c) (Nat.unpair_pair), so π is surjective. Define Γ_i := Γ_{a+1, b+1, c} where π(i) = (a, b, c). Each Γ_i is closed and satisfies the graph inequality for all its pairs of points (step 5(a),(b)). If x ∈ A, step 3 gives m, k ≥ 1 with x ∈ E_{m,k}, step 5(c) gives j with x ∈ Γ_{m,k,j}, and i := Nat.pair (m − 1) (Nat.pair (k − 1) j) satisfies Γ_i = Γ_{m,k,j} ∋ x. This proves the statement. ∎ (Lean note: it is convenient to index the classes directly by m, k ∈ ℕ with a := 1/(m+1) and radii 1/(k+1); the argument is unchanged.)

## Key steps

1. Constants γ = L/8, a_m = 1/m, ε_m = a_m(γ/2)^n/2, so that ε_m(2s)^n = a_m(γs)^n/2.
2. Uniform classes E_{m,k} (lower bound a_m t^n and cone bound ε_m t^n for all t ∈ (0,1/k]) cover A, using hypotheses (i), (ii) and 𝓝[>] 0.
3. Printed (10): if x, x' ∈ E_{m,k}, ‖x' − x‖ ≤ 1/(2k) and the graph inequality fails, cone_linear_algebra puts closedBall(x', γs) inside the cone region at x of radius 2s, so a_m(γs)^n ≤ a_m(γs)^n/2 — contradiction.
4. Closures of E_{m,k} ∩ closedBall(d_j, 1/(4k)), d_j dense, are closed L-graphs over P (closed condition) covering E_{m,k}.
5. Enumerate the triples (m,k,j) by Nat.unpair.

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
