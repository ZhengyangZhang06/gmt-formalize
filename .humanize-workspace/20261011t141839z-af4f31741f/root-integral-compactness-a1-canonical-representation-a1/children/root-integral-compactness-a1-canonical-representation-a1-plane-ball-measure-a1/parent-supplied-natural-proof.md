# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1.canonical_representation-a1`
- Child DAG node: `root.integral_compactness-a1.canonical_representation-a1.plane_ball_measure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the parent proof, which states H^n(T.plane ∩ B_s(0)) = ω_n s^n because T.plane is an n-dimensional subspace, isometric to ℝ^n, on which μHE[n] is Lebesgue measure. Here it is extended from s > 0 to all r ≥ 0. Let P := T.plane, viewed as a subspace of ℝ^N with the restricted inner product and the subspace (Borel) σ-algebra.

1. dim P = n (SimonGMT Grassmannian.finrank_plane: Module.finrank ℝ T.plane = n). So P is a finite-dimensional real inner product space. The inclusion ι : P → ℝ^N (Subtype.val) is an isometry (isometry_subtype_coe).

2. T.plane ∩ closedBall 0 r = ι(closedBall (0 : P) r). Indeed, z is in the left side iff z ∈ P and ‖z‖ ≤ r, iff z = ι(w) for some w ∈ P with ‖w‖ = ‖z‖ ≤ r.

3. Isometries preserve the Euclidean Hausdorff measure of images (Isometry.euclideanHausdorffMeasure_image). So μHE[n](ι(closedBall (0:P) r)) = μHE[n]_P(closedBall (0:P) r), where μHE[n]_P is μHE[n] on the metric space P.

4. On every finite-dimensional real inner product space E, μHE[finrank E] = volume (InnerProductSpace.euclideanHausdorffMeasure_eq_volume). Taking E = P with finrank P = n gives μHE[n]_P = volume_P. In Lean, obtain the equation with d = finrank ℝ P and rewrite finrank ℝ P = n inside that hypothesis. Do not rewrite n in the goal: T's type depends on n.

5. volume_P is an additive Haar measure on P. So for r ≥ 0, volume_P(closedBall (0:P) r) = ofReal(r^n) · volume_P(ball (0:P) 1) (Measure.addHaar_closedBall with finrank P = n). This also holds when n = 0.

6. Choose a linear isometry equivalence e : P ≃ₗᵢ EuclideanSpace ℝ (Fin n). For example, take the coordinate map of an orthonormal basis of P indexed by Fin n: ((stdOrthonormalBasis ℝ P).reindex (finCongr hP)).repr, where hP : finrank P = n. A linear isometry equivalence between finite-dimensional inner product spaces preserves volume (LinearIsometryEquiv.measurePreserving). Also e⁻¹(ball 0 1) = ball (0:P) 1, because ‖e w‖ = ‖w‖. Therefore volume_P(ball (0:P) 1) = volume(ball (0 : EuclideanSpace ℝ (Fin n)) 1) = unitBallVolume n.

7. Combine steps 2–6 with ofReal(r^n) = ofReal(r)^n for r ≥ 0 (ENNReal.ofReal_pow): μHE[n](T.plane ∩ closedBall 0 r) = ofReal(r)^n · unitBallVolume n = unitBallVolume n · ofReal(r)^n. ∎ (For n = 0, P = {0} and both sides equal 1, consistent with the general argument.)

Lean route (verified in a scratch copy, about 30 lines, no extra imports, axioms propext/Classical.choice/Quot.sound):
- prove the set identity of step 2 by ext;
- rw [himage, isometry_subtype_coe.euclideanHausdorffMeasure_image];
- get hvol from InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := T.plane) via rwa [hP];
- rw [hvol, Measure.addHaar_closedBall volume (0 : T.plane) hr, hP];
- prove the unit-ball volume with (e.measurePreserving).measure_preimage measurableSet_ball.nullMeasurableSet, then ext and simp;
- finish with ENNReal.ofReal_pow hr and mul_comm.

## Key steps

1. T.plane ∩ B_r(0) is the image of the closed r-ball of the n-dimensional inner product space P = T.plane under the isometric inclusion.
2. Isometry invariance of μHE[n] together with μHE[finrank P] = volume_P.
3. Haar scaling: volume_P(B_r(0)) = ofReal(r^n) · volume_P(ball 0 1).
4. A linear isometry P ≃ ℝ^n carries volume_P(ball 0 1) to ω_n = unitBallVolume n; ofReal(r^n) = ofReal(r)^n.

## Reference use

### local-project

Queries:
- `cat local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum snapshot project/GMT/Ch08/Contract.lean, workspace GMT/Ch08/Contract.lean, GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `rg -n 'HasTangentPlane|densityRatio|planeVarifoldMeasure' project/GMT/Ch08/Contract.lean`
- `rg -n 'μHE\[|Isometry.euclideanHausdorffMeasure_image|InnerProductSpace.euclideanHausdorffMeasure_eq_volume|euclideanHausdorffMeasure_zero' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n 'theorem _root_.Set.exists_isOpen_lt_of_lt|of_pseudoMetrizableSpace_of_isFiniteMeasure' mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `rg -n 'theorem le_toOuterMeasure_caratheodory' mathlib/Mathlib/MeasureTheory/Measure/OuterMeasure.lean; rg -n 'theorem limsup_congr' mathlib/Mathlib/Order/LiminfLimsup.lean; rg -n 'measure_biUnion_null_iff|measure_iUnion_null_iff' mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `rg -n 'theorem addHaar_closedBall' mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean; rg -n 'theorem isOpen_iUnion_countable' mathlib/Mathlib/Topology/Bases.lean; rg -n 'volume_euclideanSpace_eq_dirac|theorem measurePreserving' mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `grep -n 'structure Varifold|isOpen_domain|def weight|weight_finite_on_compact|instCompactSpace|finrank_plane' simongmt Chapter08/Varifold.lean`
- `grep -n 'theorem mul_simonHausdorff_le_of_le_dimensionalUpperDensity|theorem simon_theorem_3_3|^variable' simongmt Chapter01/DensityComparison.lean; grep -n 'def dimensionalDensityQuotient|def dimensionalUpperDensity' Chapter01/Densities.lean; grep -n 'def realUnitBallVolume|simonHausdorffMeasureReal_toOuterMeasure|realUnitBallVolume_zero|def simonHausdorffOuterMeasureReal' Chapter01/Hausdorff.lean; grep -n 'realUnitBallVolume_nat_eq|volume_euclidean_ball_eq' Chapter01/EuclideanHausdorffUpper.lean; grep -n 'simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure' Chapter02/AreaLiteral.lean`
- `python3 dag.json scan for related frozen types and statuses (frt_weight_blowup_tendsto comparing; tgc_plane_closedBall_hausdorff, frt_tangent_plane_hasDensity, allard_tc_tangent_plane_density, frt_hausdorff_null_of_weight_null not accepted); grep -rho 'intcpt_[A-Za-z0-9_]*' run dir (no intcpt_canon_* except intcpt_canonical_tangent_representation)`
- `git show b951e87c:GMT/Ch08/Submission.lean (existing proof of the identical weight-blowup type)`
- `grep -n contract_scope/child_modules/candidate_inputs verifier/gmt-compare.py; read verifier/comparator/Comparator/Compare.lean (recursive constant equality) and Main.lean (safeExport via lean4export)`
- `lake env lean Test/Assembly.lean (comparator scope replay: 4 child stubs, NodeChallenge-form checks, parent assembly without own sorry)`
- `lake env lean Test/Imports.lean (Chapter01.DensityComparison, EuclideanHausdorffUpper, Chapter02.AreaLiteral lemmas absent from Submission's import closure)`
- `lake env lean Test/C2.lean, Test/B.lean, Test/C1.lean, Test/Full.lean (sorry-free chain; #print axioms: propext, Classical.choice, Quot.sound)`
- `python3 -I validate_lean_statement (verifier/lean_contract.py) on the 4 lean_statements`
- `lake env lean GMT/Ch08/{Contract,Submission+3 imports}.lean -o …; lake env lean4export GMT.Ch08.Contract / GMT.Ch08.Submission -- GMT.Ch08.main_theorem; diff (only the sorry tag of main_theorem differs)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/OuterMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/EuclideanHausdorffUpper.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/comparator/Comparator/Compare.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/comparator/Main.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-canonical-representation-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-canonical-representation-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-tangent-plane-density-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-weight-blowup-a1/comparison-identity-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-08.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/tmp/canon-decomp-UcXiqH/Test/Assembly.lean`
- `/tmp/canon-decomp-UcXiqH/Test/Imports.lean`
- `/tmp/canon-decomp-UcXiqH/Test/C2.lean`
- `/tmp/canon-decomp-UcXiqH/Test/B.lean`
- `/tmp/canon-decomp-UcXiqH/Test/C1.lean`
- `/tmp/canon-decomp-UcXiqH/Test/Full.lean`
- `/tmp/canon-imports-zUDhY3/GMT/Ch08/Submission.lean`
- `/tmp/canon-exports/contract.ndjson`
- `/tmp/canon-exports/submission_extra_imports.ndjson`

The snapshot pins project 63436ae6 and Mathlib 25730c7c. Its Contract is byte-identical to the workspace Contract and Submission.
All cited lemmas exist with suitable hypotheses:
- Mathlib: Isometry.euclideanHausdorffMeasure_image, InnerProductSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_closedBall, LinearIsometryEquiv.measurePreserving, volume_euclideanSpace_eq_dirac, Set.exists_isOpen_lt_of_lt (arbitrary sets), the outer-regularity instance for finite measures on pseudo-metrizable spaces, TopologicalSpace.isOpen_iUnion_countable, le_toOuterMeasure_caratheodory, limsup_congr, measure_biUnion_null_iff and measure_iUnion_null_iff.
- SimonGMT: Varifold.isOpen_domain, Varifold.weight_finite_on_compact, Grassmannian.finrank_plane, Chapter01.mul_simonHausdorff_le_of_le_dimensionalUpperDensity (Simon 1.3.3 for arbitrary sets), Chapter01.simonHausdorffMeasureReal_toOuterMeasure, realUnitBallVolume_zero, volume_euclidean_ball_eq and Chapter02.simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure.
- Three of these modules are outside Submission's import closure: DensityComparison, EuclideanHausdorffUpper and AreaLiteral. Adding them to Submission.lean is allowed by gmt-compare.py. A lean4export diff of main_theorem's dependency closure shows they leave every Contract definition byte-identical.
In the comparator's replayed Contract scope, the four child lean_statements elaborate in NodeChallenge form and pass validate_lean_statement. Each child was proved without sorry. The parent's frozen type then follows by a short assembly. #print axioms gives only propext, Classical.choice and Quot.sound.
Identical types exist in other DAG branches but none is accepted, so fresh intcpt_canon_* names are used. They do not occur anywhere in the run directory.
