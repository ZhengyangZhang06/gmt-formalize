# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.isodiametric_bound-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.isodiametric_bound-a1.symmetric_replacement-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent step 1g, first part (Simon Ch. 1, proof of 2.10, book/chapter-01.txt lines 523–531: applying Steiner symmetrization successively with respect to the coordinate planes x¹ = 0, …, xⁿ = 0 gives a compact set Ã with diameter ≤ diam A, the same Lebesgue measure as A, and invariant under x ↦ −x), with the properties of one symmetrization (parent steps 1c–1f) supplied by the sibling results listed below.
Notation. For i ∈ Fin d, y ∈ ℝ^d and t ∈ ℝ let y[i↦t] := WithLp.toLp 2 (Function.update y.ofLp i t), and let R_i(y) := y[i↦−y_i] = WithLp.toLp 2 (Function.update y.ofLp i (−y i)) be the reflection in the coordinate plane x_i = 0. For B ⊆ ℝ^d, S_i(B) is the coordinate Steiner symmetrization of the sibling statements, the set {y | {t | y[i↦t] ∈ B}.Nonempty ∧ |y i| ≤ (volume {t | y[i↦t] ∈ B}).toReal / 2}. (The sibling steiner_slice_length writes the same set with the bound variables x, s in place of y, t.)
Sibling results used, for a compact set B ⊆ ℝ^d and i ∈ Fin d:
(U) the slice length y ↦ (volume {t | y[i↦t] ∈ B}).toReal is upper semicontinuous [Submission.cbr_ci_iso_slice_length_usc];
(C) if this slice length is upper semicontinuous, then S_i(B) is compact [Submission.cbr_ci_iso_steiner_isCompact]; together with (U), S_i(B) is compact;
(L) for every y ∈ ℝ^d, volume {t | y[i↦t] ∈ S_i(B)} = volume {t | y[i↦t] ∈ B} [Submission.cbr_ci_iso_svol_steiner_slice_volume_eq];
(F) if S, B ⊆ ℝ^d are measurable and volume {t | y[i↦t] ∈ S} = volume {t | y[i↦t] ∈ B} for every y ∈ ℝ^d, then L^d(S) = L^d(B) [Submission.cbr_ci_iso_svol_volume_eq_of_slice_volume_eq];
(D) ediam S_i(B) ≤ ediam B [Submission.cbr_ci_iso_steiner_ediam_le];
(R) R_i(y) ∈ S_i(B) for every y ∈ S_i(B), and, for k ≠ i, if R_k(x) ∈ B for every x ∈ B, then R_k(y) ∈ S_i(B) for every y ∈ S_i(B) [Submission.cbr_ci_iso_steiner_reflection].
0. Volume preservation (parent step 1d). Let B ⊆ ℝ^d be compact and i ∈ Fin d. By (U) and (C), S_i(B) is compact, hence closed and measurable (IsCompact.measurableSet); B is compact, hence measurable. By (L), the slice hypothesis of (F) holds for S := S_i(B) and B. So (F) gives L^d(S_i(B)) = L^d(B).
1. Claim: for every finite set F ⊆ Fin d there is a compact K_F ⊆ ℝ^d with L^d(K_F) = L^d(A), ediam K_F ≤ ediam A, and R_k(x) ∈ K_F for all k ∈ F and x ∈ K_F. The proof is by induction on F (Finset.induction_on).
2. F = ∅: take K_∅ := A, which is compact by hypothesis. The measure and diameter conditions hold with equality, and the symmetry condition is vacuous.
3. Step from F' to F = insert i F' with i ∉ F'. Let K' := K_{F'} be given by the induction hypothesis and put K := S_i(K'). By (U) and (C), K is compact. By step 0 applied to B = K', L^d(K) = L^d(K') = L^d(A). By (D), ediam K ≤ ediam K' ≤ ediam A. Now let k ∈ F and x ∈ K. If k = i, then R_i(x) ∈ K by the first part of (R). If k ∈ F', then k ≠ i (because i ∉ F'), and R_k(z) ∈ K' for all z ∈ K' by the induction hypothesis, so R_k(x) ∈ K by the second part of (R).
4. Apply step 1 to F = Fin d (Finset.univ). Then K := K_univ is compact, L^d(K) = L^d(A), ediam K ≤ ediam A, and R_i(x) ∈ K for every i ∈ Fin d and every x ∈ K.
5. Central symmetry. Fix x ∈ K. For a finite set G ⊆ Fin d let x^G ∈ ℝ^d be the point with coordinates (x^G)_k = −x_k if k ∈ G and (x^G)_k = x_k otherwise (Lean: WithLp.toLp 2 (fun k => if k ∈ G then −x k else x k)). We show x^G ∈ K by induction on G. First, x^∅ = x ∈ K. Next, let i ∉ G. Then x^{insert i G} = R_i(x^G): coordinate i of both points is −x_i = −(x^G)_i, because i ∉ G, and every coordinate k ≠ i of both points equals (x^G)_k. This point lies in K because x^G ∈ K and R_i maps K into itself (step 4). For G = Fin d every coordinate of x^G is −x_k, so x^G = −x, and hence −x ∈ K.
6. Hence K is compact, L^d(K) = L^d(A), ediam K ≤ ediam A, and −x ∈ K for every x ∈ K. ∎

## Key steps

1. Volume preservation for compact B: S_i(B) is compact by (U) and (C), hence measurable; the slice equality (L) and the coordinate Cavalieri principle (F) give L^d(S_i(B)) = L^d(B).
2. Finset induction over the processed coordinates, replacing K by S_i(K).
3. Each step preserves compactness, Lebesgue measure and the ediam bound (D), keeps the old reflection symmetries and adds R_i-symmetry (R).
4. After all coordinates, K is invariant under every R_i.
5. Flipping the coordinates of x ∈ K one at a time gives −x ∈ K.

## Reference use

### local-project

Queries:
- `cat RUN/local-references/123e8435b4a2469b/manifest.json -> mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d; git rev-parse HEAD (b4d606db1), git -C .lake/packages/mathlib rev-parse HEAD (25730c7c), git -C .lake/packages/simongmt rev-parse HEAD (2b366308); cmp SNAPSHOT/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean and GMT/Ch07/Contract.lean -> identical`
- `rg -il 'isodiametric|steiner' SNAPSHOT/mathlib/Mathlib -> no match (exit 1); rg -il 'isodiametric|steiner' SNAPSHOT/project -> only GMT/Ch01/{Contract,Submission,README} (outside the Ch07 import closure)`
- `python3 -I scans of RUN/dag.json (2092 nodes): selected node depth 5 and status decomposing; byte-identical lean_statement search -> root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.isodiametric_bound-a1 (cbr_ci_euclideanHausdorff_le_isodiametric, speculative-ready); statuses/candidate commits of its subtree (steiner_reflect, steiner_diam, slice_usc, steiner_compact, symmetric_bound, steiner_volume.cavalieri_coordinate, steiner_volume.steiner_slice_length accepted; steiner_volume queued; symmetric_replacement, isodiametric, volume_le_hausdorff speculative-ready); lean_name search for dmcbr_ci_iso_* -> none`
- `python3 -I diff of subproblem.natural_proof in RUN/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-3684511996/parent-child-handoff.json and this node's parent-child-handoff.json -> identical; read decomposition-v1.json and decomposition-audit-v1.json of nodes ...-3684511996 and ...-b1e99d8ae2 (acceptable=true, every child acceptable and natural_proof_acceptable)`
- `sed -n 6557,6600p, 1810,1960p, 1660,1740p, 1388,1397p /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py and grep -n 'def ensure' -A 35 store.py (accepted cross-branch declarations with identical type are reused by node id; unaccepted ones are reserved; depth >= max_depth never splits); grep max_depth/max_nodes swarm-project.json -> 6 / 5000`
- `git diff <proof_base_commit> <candidate_commit> -- GMT/Ch07/Submission.lean for the 7 accepted candidates (e06e9f22, d1066449, 5ea5286a, c7b07ef2, 710131ae, 1eb2ee70, 5af3533e) and git show of the speculative drafts 663584c2, f6a9702d, 263676f0, 36bd0b8d, 3f96a865`
- `rg -n over SNAPSHOT/mathlib/Mathlib: le_hausdorffMeasure (MeasureTheory/Measure/Hausdorff.lean:541), isAddHaarMeasure_hausdorffMeasure (Hausdorff.lean:978), Measure.le_iff' (MeasureTheory/Measure/CompleteLattice.lean:46), Measure.euclideanHausdorffMeasure_def (Geometry/Euclidean/Volume/Measure.lean:74), EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Measure.lean:187), OrthonormalBasis.volume_parallelepiped (MeasureTheory/Measure/Haar/InnerProductSpace.lean:82), Measure.coe_nnreal_smul_apply (MeasureTheory/Measure/Module.lean:182), ENNReal.mul_le_mul_iff_left (Basic/ENNReal/Operations.lean:79), ENNReal.mul_top (:187), ENNReal.top_pow (:230), ENNReal.top_div_of_ne_top (Basic/ENNReal/Inv.lean:343), ENNReal.mul_inv_cancel (:103), ENNReal.inv_mul_cancel (:108), ENNReal.div_ne_top (:218), ENNReal.div_ne_zero (:550), ENNReal.rpow_natCast (Analysis/SpecialFunctions/Pow/NNReal.lean:686), IsCompact.measurableSet (MeasureTheory/Constructions/BorelSpace/Basic.lean:262), isBounded_iff_ediam_ne_top (Topology/MetricSpace/Bounded.lean:469), Bornology.IsBounded.isCompact_closure (Bounded.lean:328), Metric.ediam_closure (Topology/Instances/ENNReal/Lemmas.lean:649), ediam_subsingleton (Topology/EMetricSpace/Diam.lean:57), measure_ball_pos (MeasureTheory/Measure/OpenPos.lean:212), measure_ball_lt_top (MeasureTheory/Measure/Typeclasses/Finite.lean:373), Measure.addHaar_closedBall (MeasureTheory/Measure/Lebesgue/EqHaar.lean:500), finrank_euclideanSpace_fin (Analysis/InnerProductSpace/PiL2.lean:205), Finset.induction_on (Data/Finset/Insert.lean:491), Function.update_comm / Function.update_idem (Logic/Function/Basic.lean:787, :792) -> all found`
- `rg -l dmcbr_ci_iso SNAPSHOT .lake/packages/simongmt GMT -> no match (exit 1)`
- `sed -n 495,560p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt (Theorem 2.10 lines 502-506, proof lines 511-536, note lines 537-545, completion of 2.9 lines 547-559)`
- `lake env lean /tmp/dmcbr_iso/out/Types.lean (10 child types + parent type as challenge theorems in the scope replayed by gmt-compare.contract_scope: only sorry warnings)`
- `lake env lean /tmp/dmcbr_iso/out/Integrated.lean (7 accepted proofs verbatim + 3 fresh children + exact parent type + exact Submission.X targets: exit 0, no errors; #print axioms: propext, Classical.choice, Quot.sound for all 11 declarations)`
- `python3 -I /tmp/dmcbr_iso/scripts/validate.py /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py -> all 10 statements valid and unchanged; recomputed decomposition_scope digest 485d3abe47d0ba0f96aff51ba355022a075f574112ff539330772a36bbb1c23a`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch01/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-bf84361bcd/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-bf84361bcd/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-3684511996/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-3684511996/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-3684511996/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-b1e99d8ae2/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-b1e99d8ae2/decomposition-audit-v1.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/models.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/decomposition_scope.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/scripts/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/CompleteLattice.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Module.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/EMetricSpace/Diam.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Finset/Insert.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Logic/Function/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/tmp/dmcbr_iso/out/Types.lean`
- `/tmp/dmcbr_iso/out/Integrated.lean`
- `/tmp/dmcbr_iso/out/Integrated.log`

The snapshot is compatible: its pins match the workspace, and its Ch07 contract is byte-identical to Submission.lean and Contract.lean. Mathlib at 25730c7c has no isodiametric inequality and no Steiner symmetrization, and the Ch01 versions lie outside the Ch07 import closure. The proof is therefore rebuilt from Mathlib API, which exists at the cited locations. The selected node's frozen type and supplied proof are byte-identical to those of the other branch's audited node cbr_ci_euclideanHausdorff_le_isodiametric. Its seven accepted descendants have byte-identical types and are reused by name. The three unaccepted ones get fresh dmcbr_ci_iso_* names, which occur nowhere in the DAG, the snapshot, SimonGMT or GMT. All 10 child types elaborate in the contract scope and pass validate_lean_statement. A complete development with no sorry proves every child and the exact frozen parent type using only propext, Classical.choice and Quot.sound.
