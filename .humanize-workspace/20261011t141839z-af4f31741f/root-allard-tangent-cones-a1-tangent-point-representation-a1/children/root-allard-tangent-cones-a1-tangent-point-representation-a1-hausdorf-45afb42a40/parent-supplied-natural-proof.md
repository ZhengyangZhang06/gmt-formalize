# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_tangent_cones-a1.tangent_point_representation-a1`
- Child DAG node: `root.allard_tangent_cones-a1.tangent_point_representation-a1.hausdorff_null_of_weight_null-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Imports needed in Submission: Poincare.SimonGMT.Chapter01.DensityComparison (simon_theorem_3_3), Poincare.SimonGMT.Chapter01.EuclideanHausdorffUpper (volume_euclidean_ball_eq), Poincare.SimonGMT.Chapter02.AreaLiteral (simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure). Write H := μHE[n] on ℝ^N.

1. The unit-ball constants agree: Chapter01.realUnitBallVolume (n:ℝ) = unitBallVolume n, where unitBallVolume n is the volume of the open unit ball of EuclideanSpace ℝ (Fin n).
 - If n ≥ 1: Chapter01.volume_euclidean_ball_eq (with 0 < n) at centre 0 and radius 1 gives volume(ball 0 1) = realUnitBallVolume n · ofReal(1)^n = realUnitBallVolume n.
 - If n = 0: realUnitBallVolume 0 = 1 (Chapter01.realUnitBallVolume_zero). EuclideanSpace ℝ (Fin 0) is a single point, so ball 0 1 = univ. The map PiLp.volume_preserving_toLp (Fin 0) is volume preserving, so volume(univ) equals the volume of univ in Fin 0 → ℝ. That volume is Measure.pi over the empty index set (MeasureTheory.volume_pi), and Measure.pi_univ gives the empty product 1.

2. Regularity. Since μ(K) < ∞ for all compact K, μ is finite on compacts. Hence it is locally finite on the locally compact space ℝ^N, and therefore regular (ℝ^N is σ-compact and metrizable); in particular it is outer regular. So for every set A ⊆ ℝ^N and every r > μ(A) there is an open O ⊇ A with μ(O) < r (Set.exists_isOpen_lt_of_lt, valid for arbitrary A).

3. Normalisation. For every A ⊆ ℝ^N, Chapter01.simonHausdorffOuterMeasureReal (n:ℝ) A = H(A). Indeed, simonHausdorffOuterMeasureReal (n:ℝ) = (simonHausdorffMeasureReal (n:ℝ)).toOuterMeasure by Chapter01.simonHausdorffMeasureReal_toOuterMeasure (as 0 ≤ n), and simonHausdorffMeasureReal (n:ℝ) = μHE[n] by Chapter02.simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure.

4. Reduction. For k ∈ ℕ let t_k := 1/(k+1) > 0 and Z_k := {x ∈ Z : t_k ≤ θ(x)}. (Index by k+1, since 1/0 = 0.) If x ∈ Z then θ(x) > 0, so some k has 1/(k+1) < θ(x) (exists_nat_one_div_lt). Hence Z ⊆ ⋃_k Z_k. By countable subadditivity (measure_iUnion_null, measure_mono_null) it suffices to show H(Z_k) = 0 for each k. Fix k and write t := t_k. Then μ(Z_k) ≤ μ(Z) = 0.

5. Fix ε > 0 in ℝ≥0∞. By step 2 with A = Z_k (μ(Z_k) = 0 < ε) there is an open O ⊇ Z_k with μ(O) < ε.

6. Density at points of Z_k relative to O. Let y ∈ Z_k. Since O is open and y ∈ O, there is δ > 0 with ball(y,δ) ⊆ O (Metric.isOpen_iff). For 0 < r < δ we have closedBall(y,r) ⊆ ball(y,δ) ⊆ O, so μ(O ∩ closedBall(y,r)) = μ(closedBall(y,r)). Hence SimonGMT's quotient Chapter01.dimensionalDensityQuotient μ.toOuterMeasure (n:ℝ) O y r = μ(O ∩ closedBall(y,r)) / (realUnitBallVolume (n:ℝ) · ofReal(r)^(n:ℝ)) equals densityRatio n μ y r = μ(closedBall(y,r)) / (unitBallVolume n · ofReal(r)^n). This uses step 1 and ofReal(r)^(n:ℝ) = ofReal(r)^n (ENNReal.rpow_natCast). Since (0,δ) ∈ 𝓝[>] 0 (Ioo_mem_nhdsGT), the two functions are eventually equal along 𝓝[>] 0, so their limsups agree (Filter.limsup_congr). By hypothesis densityRatio n μ y → ofReal θ(y) along 𝓝[>] 0 (HasDensity), so its limsup is ofReal θ(y) (Tendsto.limsup_eq). Therefore Chapter01.dimensionalUpperDensity μ.toOuterMeasure (n:ℝ) O y = ofReal θ(y) ≥ ofReal t, because t ≤ θ(y).

7. Apply Simon Ch. 1, Theorem 3.3 (Chapter01.simon_theorem_3_3) to the outer measure μ.toOuterMeasure. It is Borel regular by Chapter01.measure_toOuterMeasure_isBorelRegular. Take dimension (n:ℝ) ≥ 0, A₁ := Z_k ⊆ A₂ := O and threshold t ≥ 0. Step 6 is exactly its hypothesis ofReal t ≤ dimensionalUpperDensity μ.toOuterMeasure n O y for all y ∈ Z_k. The theorem yields ofReal t · simonHausdorffOuterMeasureReal (n:ℝ) Z_k ≤ μ.toOuterMeasure O = μ(O). By steps 3 and 5, ofReal t · H(Z_k) ≤ μ(O) < ε.

8. Since ε > 0 was arbitrary, ofReal t · H(Z_k) = 0 (e.g. by ENNReal.le_of_forall_pos_le_add). As t > 0, ofReal t ≠ 0, so H(Z_k) = 0. By step 4, H(Z) = 0. ∎

## Key steps

1. ω_n agreement: realUnitBallVolume (n:ℝ) = unitBallVolume n (volume_euclidean_ball_eq for n ≥ 1; n = 0 directly via PiLp.volume_preserving_toLp and Measure.pi over an empty index).
2. μ is finite on compacts, hence outer regular; H^n is SimonGMT's simonHausdorffOuterMeasureReal n via simonHausdorffMeasureReal_toOuterMeasure and simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure.
3. Split Z = ⋃_k Z_k with Z_k = {x ∈ Z : θ(x) ≥ 1/(k+1)}; μ(Z_k) = 0; choose open O ⊇ Z_k with μ(O) < ε.
4. For y ∈ Z_k, small closed balls lie in O, so dimensionalUpperDensity μ n O y = lim densityRatio = ofReal θ(y) ≥ ofReal(1/(k+1)).
5. simon_theorem_3_3 gives ofReal(1/(k+1))·H^n(Z_k) ≤ μ(O) < ε for all ε, so H^n(Z_k) = 0 and H^n(Z) = 0.

## Reference use

### local-project

Queries:
- `cat local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum project/GMT/Ch08/Contract.lean GMT/Ch08/Contract.lean GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487); git -C .lake/packages/simongmt rev-parse HEAD (2b3663083f3fe399b6296fb8eaee52169170e197)`
- `python3 dump of dag.json nodes: ids, statuses, lean_names, lean_statements of root.allard_tangent_cones-a1.* and root.first_rectifiability-a1.*; exact-type comparison of candidate children against all 77 node lean_statements`
- `grep -rl allard_tc_tpr over run dir, dag.json, GMT/ and .swarm-worktrees/*/gmt-ch08/GMT (no matches)`
- `grep -n 'def HasWeightedApproximateTangentSpaceAt|def CountablyRectifiable|def blowUpMap|HasWeightedApproximateTangentSpaceAt.unique' Chapter03/Rectifiable.lean`
- `grep -n '^theorem|^def|^structure|instCompactSpace|weight_apply|weight_finite_on_compact|finrank_plane' Chapter08/Varifold.lean; grep eq_of_plane_eq Chapter08/ConstancyTangent.lean`
- `grep simon_theorem_3_3|dimensionalUpperDensity|dimensionalDensityQuotient|realUnitBallVolume_zero|volume_euclidean_ball_eq|measure_toOuterMeasure_isBorelRegular|simonHausdorffMeasureReal_toOuterMeasure|simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure in SimonGMT Chapter01/Chapter02`
- `grep euclideanHausdorffMeasure_def|euclideanHausdorffMeasure_smul0|Isometry.euclideanHausdorffMeasure_image|euclideanHausdorffMeasure_eq_volume mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `grep measure_toMeasurable_inter_of_sFinite|sigmaFinite_of_countable|sigmaFinite_of_le|restrict_eq_self|restrict_congr_set|restrict_apply0'|exists_isOpen_lt_of_lt|aemeasurable_iUnion_iff|integral_withDensity_eq_integral_toReal_smul0|MeasurableEmbedding.integral_map|integral_smul_measure|LipschitzWith.hausdorffMeasure_image_le|isProperMap_fst_of_compactSpace in the Mathlib snapshot`
- `grep volume_ball (EuclideanSpace/InnerProductSpace; both need Nonempty/Nontrivial, so n = 0 handled via PiLp.volume_preserving_toLp) Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `sed contract_scope/child_modules from verifier/gmt-compare.py; validate_lean_statement from verifier/lean_contract.py on all child statements`
- `read accepted proof of Submission.frt_weight_blowup_tendsto in .swarm-worktrees/5b11dac1c034c03f70d2/gmt-ch08/GMT/Ch08/Submission.lean (identical type; folded into child weighted_approx_tangent)`
- `lake env lean /tmp/tpr-decomp/scratch/Challenge.lean (comparator-form statements elaborate)`
- `lake env lean /tmp/tpr-decomp/scratch/Assembly.lean (autoImplicit false; parent assembled from stubbed children and siblings, no sorry of its own)`
- `lake env lean /tmp/tpr-decomp/scratch/{A1,B1,C1,DE1,E1,E,E2}.lean (individual child proofs)`
- `lake env lean /tmp/tpr-decomp/scratch/Full6.lean (six child proofs plus parent assembly plus extra imports; #print axioms: propext, Classical.choice, Quot.sound for every child)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-tangent-point-representation-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-tangent-point-representation-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/ConstancyTangent.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/EuclideanHausdorffUpper.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/AEMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/ContinuousMap/CompactlySupported.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Maps/Proper/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/.swarm-worktrees/5b11dac1c034c03f70d2/gmt-ch08/GMT/Ch08/Submission.lean`
- `/tmp/tpr-decomp/scratch/Challenge.lean`
- `/tmp/tpr-decomp/scratch/Assembly.lean`
- `/tmp/tpr-decomp/scratch/Full6.lean`

The snapshot is project 63436ae6 with Mathlib 25730c7c. Its Contract.lean is byte-identical to the workspace Contract and Submission (sha256 2e5cd5b3…), and the pinned SimonGMT is 2b366308. Mathlib and SimonGMT supply everything the six children need: Chapter03.CountablyRectifiable, blowUpMap, HasWeightedApproximateTangentSpaceAt and .unique; Grassmannian.finrank_plane, instCompactSpace and eq_of_plane_eq (in Chapter08.ConstancyTangent); Chapter01.simon_theorem_3_3 together with measure_toOuterMeasure_isBorelRegular, dimensionalUpperDensity, realUnitBallVolume_zero and volume_euclidean_ball_eq; simonHausdorffMeasureReal_toOuterMeasure and Chapter02.simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure; and from Mathlib, euclideanHausdorffMeasure_def/_smul₀/_eq_volume, Isometry.euclideanHausdorffMeasure_image, LipschitzWith.hausdorffMeasure_image_le, Measure.sigmaFinite_of_countable, Measure.measure_toMeasurable_inter_of_sFinite, Measure.restrict_eq_self (arbitrary sets), Set.exists_isOpen_lt_of_lt, aemeasurable_iUnion_iff, integral_withDensity_eq_integral_toReal_smul₀, MeasurableEmbedding.integral_map and integral_smul_measure. The Mathlib ball-volume formulas need a nonempty index, so ω_0 = 1 is proved separately via PiLp.volume_preserving_toLp. All six child statements elaborate in the comparator's replayed scope, also with autoImplicit false and with the four extra imports. Each child was fully proved in scratch Lean along its natural_proof, using only propext, Classical.choice and Quot.sound. The parent is assembled from the children and the sibling allard_tc_tangent_plane_density with no sorry of its own. The one exact-type overlap with another node (frt_weight_blowup_tendsto, accepted) is folded into child 6, and the allard_tc_tpr_* names are unused elsewhere.
