# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_tangent_cones-a1.tangent_point_representation-a1`
- Child DAG node: `root.allard_tangent_cones-a1.tangent_point_representation-a1.weight_eq_restrict-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation: H := μHE[n]; ν := H.restrict M, which is s-finite by hypothesis; f(x) := ofReal(θ(x)).

1. Measurable hull of E for ν. Let B* := toMeasurable ν E. Then B* is measurable and E ⊆ B* (subset_toMeasurable). Since ν is s-finite, ν(B* ∩ D) = ν(E ∩ D) for every measurable D (Measure.measure_toMeasurable_inter_of_sFinite).

2. μ(M ∖ B*) = 0. Apply the hypothesis to the Borel set B*ᶜ: μ(B*ᶜ) = ∫⁻_{E ∩ B*ᶜ} f dH. Since E ⊆ B*, E ∩ B*ᶜ = ∅. The restriction of H to ∅ is the zero measure, so the integral is 0 and μ(B*ᶜ) = 0. As M ∖ B* ⊆ B*ᶜ, μ(M ∖ B*) = 0.

3. H(M ∖ B*) = 0. Apply the sibling child hausdorff_null_of_weight_null (Submission.allard_tc_tpr_hausdorff_null_of_weight_null) to this μ, Z := M ∖ B* and θ. Its hypotheses hold: μ is finite on compact sets; μ(Z) = 0 by step 2; and every x ∈ Z lies in M, so θ(x) > 0 and HasDensity n μ x (ofReal θ(x)).

4. Fix a Borel set B. Claim: H.restrict(E ∩ B) = H.restrict(M ∩ B). By Measure.ext it suffices to compare the two measures on a measurable set D. By Measure.restrict_apply, we must show H(D ∩ (E ∩ B)) = H(D ∩ (M ∩ B)).
 (≤) D ∩ (E ∩ B) ⊆ D ∩ (M ∩ B) because E ⊆ M; use monotonicity.
 (≥) Each x ∈ D ∩ (M ∩ B) lies in (B* ∩ (D ∩ B)) ∩ M if x ∈ B*, and in M ∖ B* otherwise. By subadditivity and step 3,
 H(D ∩ (M ∩ B)) ≤ H((B* ∩ (D ∩ B)) ∩ M) + H(M ∖ B*) = H((B* ∩ (D ∩ B)) ∩ M).
 The set B* ∩ (D ∩ B) is measurable, so H((B* ∩ (D ∩ B)) ∩ M) = ν(B* ∩ (D ∩ B)) (Measure.restrict_apply). By step 1 (D ∩ B is measurable) this equals ν(E ∩ (D ∩ B)). Since E ∩ (D ∩ B) ⊆ M, ν(E ∩ (D ∩ B)) = H(E ∩ (D ∩ B)) (Measure.restrict_eq_self; no measurability of E or M is needed). Finally E ∩ (D ∩ B) = D ∩ (E ∩ B), which proves (≥).

5. The set integrals ∫⁻_{E∩B} f dH and ∫⁻_{M∩B} f dH are lintegrals against the two measures of step 4, so they are equal. By hypothesis μ(B) = ∫⁻_{E∩B} f dH, hence μ(B) = ∫⁻_{M∩B} f dH. ∎

## Key steps

1. Take the measurable hull B* := toMeasurable (H⌞M) E; s-finiteness gives (H⌞M)(B* ∩ D) = (H⌞M)(E ∩ D) for measurable D.
2. μ(B*ᶜ) = ∫⁻ over E ∩ B*ᶜ = ∅, so it is 0; hence μ(M ∖ B*) = 0.
3. Sibling hausdorff_null_of_weight_null with positive density on M gives H^n(M ∖ B*) = 0.
4. For Borel B and measurable D: H(D∩M∩B) ≤ H(B*∩D∩B∩M) + H(M∖B*) = (H⌞M)(B*∩D∩B) = (H⌞M)(E∩D∩B) = H(D∩E∩B); so H⌞(E∩B) = H⌞(M∩B).
5. Therefore μ(B) = ∫⁻_{E∩B} θ dH^n = ∫⁻_{M∩B} θ dH^n.

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
