# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_tangent_cones-a1.tangent_point_representation-a1`
- Child DAG node: `root.allard_tangent_cones-a1.tangent_point_representation-a1.rectifiable_sigma_finite-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation: H := μHE[n] on ℝ^N = Euclidean N. On ℝ^n = EuclideanSpace ℝ (Fin n) we also use μHE[n]. Put ν := H.restrict M.

1. Unfold the hypothesis (Chapter03.CountablyRectifiable). There are M₀ ⊆ ℝ^N with H(M₀) = 0 and maps F_j : ℝ^n → ℝ^N (j ∈ ℕ), each K_j-Lipschitz for some K_j ∈ ℝ≥0 (choose K_j for every j), with M ⊆ M₀ ∪ ⋃_j range F_j.

2. For j, k ∈ ℕ put C_{j,k} := F_j '' closedBall(0, k) ⊆ ℝ^N. The closed ball is compact (ℝ^n is proper) and F_j is continuous, being Lipschitz. So C_{j,k} is compact, hence closed and measurable.

3. H(C_{j,k}) < ∞. By definition (Measure.euclideanHausdorffMeasure_def), μHE[n] = c • μH[n] on every metric space, with the same scalar c := addHaarScalarFactor(volume on ℝ^n, μH[n]) ∈ ℝ≥0, which depends only on n. The Lipschitz bound LipschitzWith.hausdorffMeasure_image_le (dimension (n:ℝ) ≥ 0) gives μH[n](F_j '' s) ≤ K_j^n · μH[n](s) for every s ⊆ ℝ^n. Multiplying by c and regrouping gives H(C_{j,k}) ≤ K_j^n · μHE[n](closedBall(0,k)), where the last measure is taken in ℝ^n. In ℝ^n, μHE[n] = volume (EuclideanSpace.euclideanHausdorffMeasure_eq_volume), and volume(closedBall(0,k)) < ∞ (measure_closedBall_lt_top). Since (K_j : ℝ≥0∞)^n < ∞, H(C_{j,k}) < ∞.

4. Let S := toMeasurable H M₀ ∪ ⋃_{(j,k)∈ℕ×ℕ} C_{j,k}. S is measurable. We show M ⊆ S. Let x ∈ M. Either x ∈ M₀ ⊆ toMeasurable H M₀ (subset_toMeasurable), or x = F_j(y) for some j and some y ∈ ℝ^n. In the second case choose k ∈ ℕ with ‖y‖ ≤ k (exists_nat_ge). Then y ∈ closedBall(0,k), so x ∈ C_{j,k}.

5. Consider the countable family 𝒮 := {Sᶜ, toMeasurable H M₀} ∪ {C_{j,k} : (j,k) ∈ ℕ×ℕ}. Its union is ℝ^N: a point of S lies in toMeasurable H M₀ or in some C_{j,k}, and any other point lies in Sᶜ.

6. Every member of 𝒮 has finite ν-measure. All members are measurable, so ν(A) = H(A ∩ M) for each of them (Measure.restrict_apply).
 (a) ν(Sᶜ) = H(Sᶜ ∩ M) = H(∅) = 0, because M ⊆ S by step 4.
 (b) ν(toMeasurable H M₀) ≤ H(toMeasurable H M₀) = H(M₀) = 0 (measure_toMeasurable).
 (c) ν(C_{j,k}) ≤ H(C_{j,k}) < ∞ by step 3.

7. A measure is σ-finite when a countable family of sets of finite measure covers the whole space (Measure.sigmaFinite_of_countable). By steps 5–6, ν = μHE[n].restrict M is σ-finite. ∎

## Key steps

1. Unfold CountablyRectifiable: M ⊆ M₀ ∪ ⋃_j range F_j with H^n(M₀) = 0 and F_j K_j-Lipschitz.
2. H^n(F_j(closedBall 0 k)) ≤ K_j^n·vol_n(closedBall 0 k) < ∞, from LipschitzWith.hausdorffMeasure_image_le, μHE[n] = c•μH[n], and μHE[n] = volume on ℝ^n.
3. S := toMeasurable H M₀ ∪ ⋃_{j,k} F_j(closedBall 0 k) contains M; the countable family {Sᶜ, toMeasurable H M₀, F_j(closedBall 0 k)} covers ℝ^N.
4. Each member has finite (H⌞M)-measure (0, 0, or ≤ H^n(F_j(B_k)) < ∞), so Measure.sigmaFinite_of_countable gives σ-finiteness.

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
