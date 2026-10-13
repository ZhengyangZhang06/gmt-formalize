# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.isodiametric_bound-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.isodiametric_bound-a1.symmetric_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: final step of Simon's proof of 2.10 / parent step 1g (the symmetrized set lies in the closed ball of radius ½ diam about 0, whence the bound). No measurability, compactness or boundedness of K is assumed.
1. ω_d ∈ (0, ∞): the open unit ball is a nonempty open set, so its volume is positive (Metric.measure_ball_pos for the additive Haar measure volume); it is bounded, so its volume is finite (measure_ball_lt_top).
2. Case ediam K = ∞. Then d ≥ 1: for d = 0, ℝ⁰ has exactly one point, so K is subsingleton and ediam K = 0 (ediam_subsingleton). For d ≥ 1, (∞/2)^d = ∞ (ENNReal.top_div_of_ne_top, ENNReal.top_pow) and ω_d·∞ = ∞ (ENNReal.mul_top, ω_d ≠ 0), so the inequality holds trivially.
3. Case ediam K < ∞. Then K is bounded (isBounded_iff_ediam_ne_top). For x ∈ K also −x ∈ K, so 2‖x‖ = ‖x − (−x)‖ = dist(x, −x) ≤ diam K (dist_le_diam_of_mem). Hence K ⊆ closedBall(0, r) with r := diam K/2 ≥ 0.
4. L^d(closedBall(0, r)) = ofReal(r^d)·ω_d. By Measure.addHaar_closedBall for the additive Haar measure volume, L^d(closedBall(0, r)) = ofReal(r^{finrank})·L^d(ball(0, 1)), and finrank ℝ (EuclideanSpace ℝ (Fin d)) = d (finrank_euclideanSpace_fin). This holds for every d, including 0.
5. ofReal(r^d) = ofReal(r)^d = (ofReal(diam K)/2)^d = (ediam K/2)^d. This uses r ≥ 0 (ENNReal.ofReal_pow), ofReal(a/2) = ofReal(a)/2 (ENNReal.ofReal_div_of_pos), and ofReal(diam K) = ofReal((ediam K).toReal) = ediam K because ediam K ≠ ∞ (ENNReal.ofReal_toReal).
6. By monotonicity of measure, L^d(K) ≤ L^d(closedBall(0, r)) = ω_d·(ediam K/2)^d. ∎

## Key steps

1. ω_d = unitBallVolume d is positive and finite.
2. ediam K = ∞ forces d ≥ 1 and an infinite right-hand side.
3. Central symmetry gives K ⊆ closedBall(0, diam K/2).
4. L^d(closedBall(0, r)) = ofReal(r^d)·ω_d and ofReal(diam K/2)^d = (ediam K/2)^d.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp snapshot project/GMT/Ch07/Contract.lean with workspace GMT/Ch07/Contract.lean (identical) and Contract.lean with Submission.lean (identical)`
- `rg -il 'isodiametric|steiner' over the snapshot project and mathlib/Mathlib: matches only project/GMT/Ch01/{Contract,Submission,README} (Ch01 IsodiametricInequality, stated with realUnitBallVolume; not in the Ch07 import closure); no match anywhere in Mathlib`
- `sed -n 1,140p mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean: μHE[d] := addHaarScalarFactor (volume on EuclideanSpace ℝ (Fin d)) μH[d] • μH[d]; IsAddHaarMeasure instance for μH[d]; the value of the constant is an open TODO`
- `rg -n for the cited lemmas: le_hausdorffMeasure (Measure/Hausdorff.lean:541), addHaar_closedBall (Measure/Lebesgue/EqHaar.lean:500), isMulLeftInvariant_eq_smul (Measure/Haar/Unique.lean:922, to_additive), OrthonormalBasis.volume_parallelepiped and PiLp.volume_preserving_toLp (Measure/Haar/InnerProductSpace.lean:82,139), volume_preserving_piFinSuccAbove (Constructions/Pi.lean:818), Measure.prod_apply_symm (Measure/Prod.lean:706), Set.exists_isOpen_lt_of_lt (Measure/Regular.lean:359), UpperSemicontinuous.isClosed_preimage (Topology/Semicontinuity/Basic.lean:816), ediam_le / edist_le_ediam_of_mem / ediam_subsingleton (Topology/EMetricSpace/Diam.lean), Metric.ediam_closure (Topology/Instances/ENNReal/Lemmas.lean:649), Fin.update_insertNth (Data/Fin/Tuple/Basic.lean:1050), finrank_euclideanSpace_fin (Analysis/InnerProductSpace/PiL2.lean:205)`
- `lake env lean scratch importing GMT.Ch07.Submission: #check Poincare.SimonGMT.Chapter01.simon_theorem_2_10, exists_centrally_symmetric_compact_replacement, simonCenteredSlice, ediam_simonSteinerSymmetrization_le, volume_le_volume_simonSteinerSymmetrization, volume_euclidean_closedBall_eq are unknown identifiers (outside the import closure); only realUnitBallVolume is reachable`
- `read lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/{SteinerSliceBounds,SteinerDiameter,SteinerVolume,SteinerSymmetry,IsodiametricBounds,EuclideanNormalization}.lean (compiled against the same Mathlib; template for the Lean encodings WithLp.toLp 2 (Function.update y.ofLp j t) and the piFinSuccAbove/Tonelli step; their closure-based route was not used, the parent's compactness route is followed)`
- `python3 -I scan of dag.json lean_name values (1345 names; none starts with cbr_ci_iso_, so all 9 proposed names are fresh); sed of verifier/gmt-compare.py (contract_scope, child_modules) and leaf_verification.check_source_delta (one appended theorem, no helpers or set_option)`
- `lake env lean /tmp/iso-decomp/final/Integrated.lean (all 9 children proved as Submission.* in dependency order plus the frozen parent type from Submission.cbr_ci_iso_volume_le_smul_hausdorff; #print axioms: propext, Classical.choice, Quot.sound) and /tmp/iso-decomp/final/Comparator.lean (exact Submission.X targets for every child and the parent, no errors); validate_lean_statement from /runtime flow and verifier on all 9 statements (unchanged, pass)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch01/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/Unique.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/EMetricSpace/Diam.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-3684511996/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/SteinerSliceBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/SteinerDiameter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/SteinerVolume.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/SteinerSymmetry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/IsodiametricBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/EuclideanNormalization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/tmp/iso-decomp/final/Integrated.lean`
- `/tmp/iso-decomp/final/Comparator.lean`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean (project b4d606db, Mathlib 25730c7c). Mathlib has no isodiametric inequality and no Steiner symmetrization, and leaves cannot add imports. The SimonGMT Chapter01 Steiner/isodiametric modules and the Ch01 contract's IsodiametricInequality are outside the import closure of GMT.Ch07.Submission, so nothing is reusable as a declaration and the proof must be rebuilt from Mathlib. Every Mathlib lemma cited in the child proofs exists at the listed locations and is reachable. All nine child types elaborate in the frozen contract scope and pass validate_lean_statement. A complete Lean development proves all nine children (each using only its declared siblings) and then the frozen parent type, with axioms propext, Classical.choice, Quot.sound only. The names cbr_ci_iso_* are fresh in the DAG.
