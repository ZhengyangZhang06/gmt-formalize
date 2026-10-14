# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.isodiametric_bound-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.isodiametric_bound-a1.steiner_diam-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent step 1e (Simon, proof of 2.10: S_j(A) has diameter not larger than that of A). Notation: y[j↦t] = WithLp.toLp 2 (Function.update y.ofLp j t), y_j = y j; with ξ = y[j↦0], A^j_y is the parent's A_ξ and λ(y) = λ(ξ), so S_j(A) is the parent's set.
1. Slices are compact and uniformly bounded. A is bounded, so A ⊆ closedBall(0, R) for some R (IsBounded.subset_closedBall). For y ∈ ℝ^d and t ∈ A^j_y: |t| = |(y[j↦t])_j| ≤ ‖y[j↦t]‖ ≤ R (PiLp.norm_apply_le), so A^j_y ⊆ [−R, R]. A^j_y is the preimage of the closed set A under the continuous map t ↦ y[j↦t] (PiLp.continuous_toLp composed with Continuous.update), hence closed; being closed and bounded in ℝ, it is compact.
2. Length versus spread. Let P ⊆ ℝ be compact and nonempty, a := inf P, b := sup P. Then a, b ∈ P (IsCompact.sInf_mem, IsCompact.sSup_mem), a ≤ b and P ⊆ [a, b] (csInf_le, le_csSup), so L¹(P) ≤ L¹([a, b]) = ofReal(b − a) (Real.volume_Icc), hence (L¹(P)).toReal ≤ b − a.
3. Replacing one coordinate. For x, y ∈ ℝ^d and a, b ∈ ℝ: |x[j↦a] − y[j↦b]|² = |x − y|² − (x_j − y_j)² + (a − b)². Indeed |u − v|² = Σ_i (u_i − v_i)² (EuclideanSpace.dist_sq_eq); after splitting off the index j (Finset.sum_erase_add), the terms with i ≠ j coincide for (x, y) and (x[j↦a], y[j↦b]), while the j-th terms are (x_j − y_j)² and (a − b)².
4. Two-point estimate. If x[j↦a] ∈ A, y[j↦b] ∈ A and |x_j − y_j| ≤ |a − b|, then (x_j − y_j)² ≤ (a − b)², so by step 3 |x − y|² ≤ |x[j↦a] − y[j↦b]|², and since distances are nonnegative, |x − y| ≤ |x[j↦a] − y[j↦b]|. Hence edist(x, y) = ofReal|x − y| ≤ edist(x[j↦a], y[j↦b]) ≤ ediam A (edist_dist, ENNReal.ofReal_le_ofReal, edist_le_ediam_of_mem).
5. Let x, y ∈ S_j(A). Then P := A^j_x and Q := A^j_y are nonempty and compact (step 1). Put a_x := inf P, b_x := sup P, a_y := inf Q, b_y := sup Q. By step 2 the four points x[j↦a_x], x[j↦b_x], y[j↦a_y], y[j↦b_y] lie in A, and λ(x) ≤ b_x − a_x, λ(y) ≤ b_y − a_y. Since |x_j| ≤ λ(x)/2 and |y_j| ≤ λ(y)/2: |x_j − y_j| ≤ |x_j| + |y_j| ≤ (λ(x) + λ(y))/2 ≤ ((b_x − a_x) + (b_y − a_y))/2 = ((b_y − a_x) + (b_x − a_y))/2.
6. If b_x − a_y ≤ b_y − a_x, step 5 gives |x_j − y_j| ≤ b_y − a_x; in particular b_y − a_x ≥ 0, so b_y − a_x = |a_x − b_y|, and step 4 with (a, b) = (a_x, b_y) gives edist(x, y) ≤ ediam A. If b_y − a_x ≤ b_x − a_y, then likewise |x_j − y_j| ≤ b_x − a_y = |b_x − a_y|, and step 4 with (a, b) = (b_x, a_y) gives edist(x, y) ≤ ediam A.
7. As edist(x, y) ≤ ediam A for all x, y ∈ S_j(A), ediam S_j(A) ≤ ediam A (ediam_le). ∎

## Key steps

1. Slices A^j_y are compact subsets of [−R, R].
2. For a nonempty compact P ⊆ ℝ: inf P, sup P ∈ P and (L¹ P).toReal ≤ sup P − inf P.
3. |x[j↦a] − y[j↦b]|² = |x − y|² − (x_j − y_j)² + (a − b)².
4. |x_j − y_j| ≤ (λ(x)+λ(y))/2 ≤ max(b_y − a_x, b_x − a_y), realised by a pair of points of A whose distance is ≥ |x − y|.
5. Hence edist(x, y) ≤ ediam A for all x, y ∈ S_j(A).

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
