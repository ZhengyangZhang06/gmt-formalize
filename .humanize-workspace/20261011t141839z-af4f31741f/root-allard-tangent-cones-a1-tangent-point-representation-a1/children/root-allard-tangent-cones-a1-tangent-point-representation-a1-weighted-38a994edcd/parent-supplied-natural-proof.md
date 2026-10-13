# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_tangent_cones-a1.tangent_point_representation-a1`
- Child DAG node: `root.allard_tangent_cones-a1.tangent_point_representation-a1.weighted_approx_tangent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Import needed in Submission: Poincare.SimonGMT.Chapter08.ConstancyTangent (Grassmannian.eq_of_plane_eq). Notation: H := μHE[n]; η_r := Chapter03.blowUpMap x r, so η_r(z) = r⁻¹•(z − x); G := Grassmannian N n.

1. What must be shown for T. HasWAT n M θ x T.plane consists of (i) finrank T.plane = n, which is Grassmannian.finrank_plane, and (ii) for every g ∈ C_c(ℝ^N, ℝ), ∫_{η_r(M)} g(y)·θ(x + r•y) dH(y) → θ(x)·∫_{T.plane} g dH as r ↓ 0. Fix g.

2. A test function on ℝ^N × G. Let f(z,S) := g(z). It is continuous, and it vanishes outside tsupport g × G. That set is compact, because tsupport g is compact and G is compact (Grassmannian.instCompactSpace). Hence f ∈ C_c(ℝ^N × G, ℝ).

3. Apply the convergence clause of HasTangentPlane V x T (θ(x)) to f: ∫ f d(rescaledMeasure V x r) → θ(x)·∫ f d(planeVarifoldMeasure T) as r ↓ 0. On the plane side, planeVarifoldMeasure T = (H.restrict T.plane).map (y ↦ (y,T)). By integral_map (the map is continuous and f is continuous), ∫ f d(planeVarifoldMeasure T) = ∫_{T.plane} f(y,T) dH(y) = ∫_{T.plane} g dH.

4. Fix r > 0; we compute the rescaled side. By definition, rescaledMeasure V x r = ofReal(r⁻¹^n) • V.measure.map ψ_r with ψ_r(z) = (r⁻¹•(z.1 − x), z.2). By integral_smul_measure and ENNReal.toReal_ofReal (r⁻¹^n ≥ 0), and then integral_map (ψ_r continuous, f continuous):
 ∫ f d(rescaledMeasure V x r) = r⁻¹^n · ∫ g(r⁻¹•(z.1 − x)) dV.measure(z).
 Since V.weight = V.measure.map Prod.fst and y ↦ g(r⁻¹•(y − x)) is continuous, integral_map gives
 ∫ g(r⁻¹•(z.1 − x)) dV.measure(z) = ∫ g(r⁻¹•(y − x)) dV.weight(y).

5. Still with r > 0. Apply the sibling child integral_eq_weighted (Submission.allard_tc_tpr_integral_eq_weighted) to μ := V.weight, M and θ; its hypotheses are exactly ours. With the function z ↦ g(r⁻¹•(z − x)) it gives
 ∫ g(r⁻¹•(z − x)) dV.weight(z) = ∫_M g(r⁻¹•(z − x))·θ(z) dH(z).
 Apply the sibling child blowup_set_integral (Submission.allard_tc_tpr_blowup_setIntegral) with φ(y) := g(y)·θ(x + r•y):
 ∫_{η_r(M)} g(y)·θ(x + r•y) dH(y) = r⁻¹^n · ∫_M g(η_r z)·θ(x + r•η_r z) dH(z).
 Since η_r z = r⁻¹•(z − x) and x + r•(r⁻¹•(z − x)) = z (smul_smul, r·r⁻¹ = 1, one_smul, add_sub_cancel), the last integrand is g(r⁻¹•(z − x))·θ(z). Combining with step 4:
 ∫ f d(rescaledMeasure V x r) = ∫_{η_r(M)} g(y)·θ(x + r•y) dH(y) for every r > 0.

6. The interval (0,∞) belongs to 𝓝[>] 0 (self_mem_nhdsWithin). So the two functions of r in step 5 are eventually equal along 𝓝[>] 0. By Tendsto.congr' and step 3, the weighted blow-up integrals ∫_{η_r(M)} g(y)·θ(x + r•y) dH(y) converge to θ(x)·∫_{T.plane} g dH. With step 1(i), HasWAT n M θ x T.plane holds.

7. The equivalence.
 (⇐) If S = T, this is step 6.
 (⇒) Suppose HasWAT n M θ x S.plane. HasTangentPlane V x T (θ x) includes 0 < θ(x), so θ(x) ≠ 0. The uniqueness theorem Chapter03.HasWeightedApproximateTangentSpaceAt.unique, applied to S.plane and T.plane (step 6), gives S.plane = T.plane. Points of G are determined by their planes (Grassmannian.eq_of_plane_eq), so S = T. ∎

## Key steps

1. Test Def. 1.1 with f(z,S) = g(z) ∈ C_c(ℝ^N × G) (G compact); the plane side gives θ(x)∫_{T.plane} g dH^n.
2. For r > 0: ∫ f d(rescaledMeasure V x r) = r^{-n} ∫ g(r⁻¹(z − x)) dμ_V(z) (integral_smul_measure, integral_map, μ_V = V.measure.map fst).
3. Sibling integral_eq_weighted: ∫ g(r⁻¹(z−x)) dμ_V = ∫_M g(r⁻¹(z−x))θ(z) dH^n.
4. Sibling blowup_set_integral with φ(y) = g(y)θ(x + r y): this equals r^n ∫_{η_r(M)} g(y)θ(x + r y) dH^n, so Tendsto.congr' gives HasWAT n M θ x T.plane.
5. Uniqueness: θ(x) > 0, HasWeightedApproximateTangentSpaceAt.unique and Grassmannian.eq_of_plane_eq give HasWAT S.plane ⟺ S = T.

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
