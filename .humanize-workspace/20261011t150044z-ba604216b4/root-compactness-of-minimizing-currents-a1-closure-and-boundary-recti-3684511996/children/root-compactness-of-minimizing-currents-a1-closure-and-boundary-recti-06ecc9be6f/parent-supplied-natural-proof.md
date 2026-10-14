# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.isodiametric_bound-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.isodiametric_bound-a1.steiner_reflect-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent step 1f (Simon, proof of 2.10: if i ≠ j and A is invariant under reflection in the i-th coordinate plane, then S_j(A) is invariant under reflection in both the i-th and the j-th coordinate planes). Notation as in the statement; y_i is y.ofLp i (written y i in Lean) and (WithLp.toLp 2 f)_i = f i (PiLp.toLp_apply, simp). For y ∈ ℝ^d the point ξ := y[j↦0] lies in H_j = {x_j = 0}, A^j_y is the parent's A_ξ, and y ∈ S_j(A) iff A_ξ ≠ ∅ and |y_j| ≤ λ(ξ)/2, so S_j(A) is the parent's set of step 1b. No compactness or measurability is used.
1. Coordinate rules. For z ∈ ℝ^d, indices i, k and reals s, t: (z[i↦t])_i = t; (z[i↦t])_k = z_k for k ≠ i (Function.update_self, Function.update_of_ne); (z[i↦s])[i↦t] = z[i↦t] (Function.update_idem). Two points of ℝ^d are equal iff all their coordinates agree (ext).
2. Proof of (a). Let y ∈ S_j(A) and y' := R_j(y) = y[j↦−y_j]. By step 1, y'[j↦t] = y[j↦t] for every t ∈ ℝ, so A^j_{y'} = A^j_y and λ(y') = λ(y). Also y'_j = −y_j, so |y'_j| = |y_j|. Hence A^j_{y'} = A^j_y ≠ ∅ and |y'_j| = |y_j| ≤ λ(y)/2 = λ(y')/2, i.e. R_j(y) ∈ S_j(A).
3. Proof of (b): commutation. Fix i ≠ j such that R_i(x) ∈ A for all x ∈ A. Let y ∈ S_j(A) and y' := R_i(y) = y[i↦−y_i]. For every t ∈ ℝ, y'[j↦t] = R_i(y[j↦t]). Compare k-th coordinates: for k = j both sides equal t (R_i leaves coordinate j ≠ i unchanged, and (y[j↦t])_j = t); for k = i the left side is y'_i = −y_i and the right side is −(y[j↦t])_i = −y_i because i ≠ j; for k ∉ {i, j} both sides equal y_k.
4. R_i is an involution: R_i(R_i(z)) = z for every z ∈ ℝ^d (coordinate i: −(−z_i) = z_i; all other coordinates are unchanged).
5. Equal slices. A^j_{y'} = A^j_y. If t ∈ A^j_{y'}, then R_i(y[j↦t]) = y'[j↦t] ∈ A by step 3, so by the invariance of A and step 4, y[j↦t] = R_i(R_i(y[j↦t])) ∈ A, i.e. t ∈ A^j_y. Conversely, if y[j↦t] ∈ A, then y'[j↦t] = R_i(y[j↦t]) ∈ A by invariance. Consequently λ(y') = λ(y).
6. Conclusion of (b). Since i ≠ j, y'_j = y_j. Therefore A^j_{y'} = A^j_y ≠ ∅ and |y'_j| = |y_j| ≤ λ(y)/2 = λ(y')/2, i.e. R_i(y) ∈ S_j(A). ∎

## Key steps

1. Coordinate rules for y[i↦t]: update_self, update_of_ne, update_idem; points are equal iff coordinates agree.
2. (a) R_j(y)[j↦t] = y[j↦t], so the j-slice and λ are unchanged, and |(R_j y)_j| = |y_j|.
3. (b) For i ≠ j: R_i(y)[j↦t] = R_i(y[j↦t]) and R_i is an involution, so an R_i-invariant A has A^j_{R_i y} = A^j_y.
4. (R_i y)_j = y_j for i ≠ j, hence R_i(y) ∈ S_j(A).

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
