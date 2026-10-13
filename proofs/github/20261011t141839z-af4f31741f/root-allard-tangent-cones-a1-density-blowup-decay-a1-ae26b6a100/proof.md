# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_tangent_cones-a1`
- Child DAG node: `root.allard_tangent_cones-a1.density_blowup_decay-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Remark 5.6(iii) and printed (3)–(4) in the proof of Simon 8.5.5, i.e. Step A1(iii) and the first half of Step A4 of the supplied proof. The book's set G of (3)–(4) is {Θ ≥ θ0 − ε}, with the corrected inequality "≥" in the printed (5). Below, G denotes the Grassmannian instead. The book's "approximate continuity of Θ" is used only through Lebesgue density points of the countably many Borel sets {Θ̃ < p}, p ∈ ℚ.

Notation. μ := V.weight. G := Grassmannian N n. ω := unitBallVolume n ∈ (0,∞). E_τ := {y : ¬ ∃ θ, HasDensity n μ y θ ∧ ofReal τ ≤ θ}. Note that {y | y ∈ closedBall x ρ ∧ y ∈ E_τ} = E_τ ∩ B_ρ(x).

1. Borel density. DensityExistsAE(N, n, U, V, hV) gives a Borel Θ̃ : ℝ^N → [0,∞] and a μ-null set Z such that y ∉ Z ⇒ Θ̃(y) ≠ ∞ ∧ HasDensity n μ y (Θ̃ y).

2. μ(Uᶜ) = 0. Uᶜ is closed, and μ(Uᶜ) = V.measure(Uᶜ × G) = 0 (Varifold.weight_apply, V.supported).

3. Countably many balls. Let D ⊆ ℝ^N be countable and dense (TopologicalSpace.exists_countable_dense). Let 𝔅 := {closedBall q r : q ∈ D, r ∈ ℚ, r > 0, closedBall q (2r) ⊆ U}, a countable family.
 Each K ∈ 𝔅 is compact and contained in U. So μ(K) < ∞ (Varifold.weight_finite_on_compact), and μ_K := μ.restrict K is a finite, hence locally finite, measure.
 Every x ∈ U lies in the open ball B°_r(q) of some closedBall q r ∈ 𝔅: choose rational r > 0 with B_{4r}(x) ⊆ U, and q ∈ D with |q − x| < r. Then x ∈ B°_r(q) and B_{2r}(q) ⊆ B_{3r}(x) ⊆ U.

4. Lebesgue differentiation. For p ∈ ℚ let A_p := {y : Θ̃(y) < ofReal p}, a Borel set.
 For K ∈ 𝔅 and p ∈ ℚ, apply Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet to μ_K and A_p (ℝ^N is finite dimensional and second countable, so it has the Besicovitch covering property). It gives a μ_K-null set Z_{K,p} outside of which
 μ_K(A_p ∩ B_ρ(x))/μ_K(B_ρ(x)) → 1_{A_p}(x) as ρ ↓ 0.
 Since Z_{K,p} is μ_K-null, μ(Z_{K,p} ∩ K) = 0 (use a measurable null superset and Measure.restrict_apply).
 Let Z' := Uᶜ ∪ Z ∪ ⋃_{K ∈ 𝔅, p ∈ ℚ} (Z_{K,p} ∩ K). This is a countable union of μ-null sets, so μ(Z') = 0.

5. Fix x ∉ Z', and real θ0, τ with HasDensity n μ x (ofReal θ0) and τ < θ0. Since x ∉ Z, also HasDensity n μ x (Θ̃ x). Limits along 𝓝[>]0 are unique, so Θ̃(x) = ofReal θ0.
 Choose p ∈ ℚ with τ < p < θ0. Then ofReal p ≤ ofReal θ0 = Θ̃(x), so x ∉ A_p.

6. E_τ ⊆ Z ∪ A_p. Let y ∉ Z and y ∉ A_p. Then HasDensity n μ y (Θ̃ y), and ofReal τ ≤ ofReal p ≤ Θ̃(y) because τ < p. So y ∉ E_τ.

7. Density zero at x. Since x ∉ Uᶜ, pick K = closedBall q r ∈ 𝔅 with x ∈ B°_r(q) (step 3). As x ∈ K and x ∉ Z_{K,p} ∩ K, the convergence of step 4 holds at x.
 For 0 < ρ < r − |x − q| we have B_ρ(x) ⊆ K. So μ_K(A_p ∩ B_ρ(x)) = μ(A_p ∩ B_ρ(x)) and μ_K(B_ρ(x)) = μ(B_ρ(x)).
 Since 1_{A_p}(x) = 0: κ(ρ) := μ(A_p ∩ B_ρ(x))/μ(B_ρ(x)) → 0 as ρ ↓ 0.

8. Bounded ratio. HasDensity n μ x (ofReal θ0) says μ(B_ρ(x))/(ω·ofReal(ρ)^n) → ofReal θ0 < ∞. Since ω ∈ (0,∞), μ(B_ρ(x))/ofReal(ρ)^n = ω·(μ(B_ρ(x))/(ω·ofReal(ρ)^n)) → ω·ofReal θ0 < ∞.
 So there is ρ1 > 0 such that for 0 < ρ < ρ1:
 - μ(B_ρ(x))/ofReal(ρ)^n ≤ K0 := ω·(ofReal θ0 + 1) < ∞;
 - B_ρ(x) ⊆ U, so μ(B_ρ(x)) < ∞.

9. Conclusion. Let 0 < ρ < min(ρ1, r − |x − q|). By step 6 and subadditivity of the outer measure,
 μ(E_τ ∩ B_ρ(x)) ≤ μ(Z) + μ(A_p ∩ B_ρ(x)) = μ(A_p ∩ B_ρ(x)).
 - If μ(B_ρ(x)) = 0, then μ(A_p ∩ B_ρ(x)) = 0.
 - Otherwise 0 < μ(B_ρ(x)) < ∞ and μ(A_p ∩ B_ρ(x)) = κ(ρ)·μ(B_ρ(x)).
 In both cases μ(E_τ ∩ B_ρ(x))/ofReal(ρ)^n ≤ κ(ρ)·K0. Since K0 < ∞, κ(ρ)·K0 → 0·K0 = 0 (ENNReal.Tendsto.mul_const). The squeeze between 0 and κ(ρ)·K0 (tendsto_of_tendsto_of_tendsto_of_le_of_le') gives
 μ({y | y ∈ B_ρ(x) ∧ y ∈ E_τ})/ofReal(ρ)^n → 0 as ρ ↓ 0.
 This holds for every x ∉ Z', i.e. for μ-a.e. x. ∎

## Key steps

1. DensityExistsAE gives a Borel Θ̃ equal (and finite) to the density off a μ-null set Z; μ(Uᶜ) = 0.
2. Lebesgue differentiation (Besicovitch) for the finite measures μ⌞K on countably many rational balls K ⊂⊂ U, applied to the Borel sets {Θ̃ < p}, p ∈ ℚ.
3. At a good x with Θ(x) = θ0 > τ choose rational p ∈ (τ, θ0): x ∉ {Θ̃ < p} and {density ≥ τ fails} ⊆ Z ∪ {Θ̃ < p}.
4. μ({Θ̃ < p} ∩ B_ρ(x)) = o(μ(B_ρ(x))) and μ(B_ρ(x)) = O(ρ^n) by finite density, giving the o(ρ^n) decay.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum project/GMT/Ch08/Contract.lean GMT/Ch08/Contract.lean GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487); git rev-parse HEAD in .lake/packages/simongmt (2b3663083f3fe399b6296fb8eaee52169170e197)`
- `sed -n 480,700p book/chapter-08.txt (printed 5.1-5.9, proofs of 5.5 and 5.7)`
- `python3 dag.json dump of node ids, lean_names, lean_statements (siblings varifold_tangent_theorems, plane_disintegration, first_rectifiability_theorem, monotonicity_and_density_theorems, constancy_theorem, first_variation_theorems)`
- `contract_scope(Contract.lean, 'GMT.Ch08.main_theorem') and validate_lean_statement from verifier/gmt-compare.py and verifier/lean_contract.py`
- `grep -n '^def|^structure|^theorem' Chapter08/Varifold.lean; grep 'def Stationary|Stationary.hasLocallyBoundedFirstVariation|instCompactSpace'`
- `grep 'def HasWeightedApproximateTangentSpaceAt|def CountablyRectifiable|HasWeightedApproximateTangentSpaceAt.unique|support_euclideanHausdorffMeasure_restrict_submodule|regular_euclideanHausdorffMeasure_restrict_submodule' Chapter03/Rectifiable.lean`
- `grep '^theorem' Chapter08/TangentRadialRigidity.lean Chapter08/TangentRescaling.lean Chapter08/ConstancyTangentGraph.lean Chapter08/TangentScalingCounterexample.lean`
- `grep 'simon_theorem_3_3|simon_theorem_3_6|dimensionalUpperDensity|realUnitBallVolume_nat_eq|volume_euclidean_ball_eq|measure_toOuterMeasure_isBorelRegular|simonHausdorffMeasureReal_toOuterMeasure|simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure|eq_of_plane_eq|continuous_normalProject|ae_exists_ballFirstVariationBound_inside|IsSimonSubmanifold' (SimonGMT Chapter01/02/08)`
- `grep 'theorem ae_tendsto_measure_inter_div_of_measurableSet|theorem ae_tendsto_measure_inter_div' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `grep 'theorem' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (Isometry.euclideanHausdorffMeasure_image, euclideanHausdorffMeasure_smul0, EuclideanSpace.euclideanHausdorffMeasure_eq_volume)`
- `grep 'restrict_congr_set|restrict_apply0'|restrict_restrict_of_subset|MeasurableEquiv.restrict_map|lintegral_map_equiv|ext_of_integral_eq_on_compactlySupported|addHaar_closedBall|measure_toMeasurable_inter_of_sFinite|hausdorffMeasure_image_le|smul_closedBall|ofReal_div_of_pos|tendsto_measure_iInter_atTop' mathlib/Mathlib`
- `grep -rl allard_tc_ over the run directory, GMT/ and .swarm-worktrees (no matches); dag.json lean_name collision check (45 nodes, none)`
- `lake env lean GMT/Ch08/Submission.lean -o /tmp/allard-a1-decomp/olean/GMT/Ch08/Submission.olean`
- `lean /tmp/allard-a1-decomp/scratch/Final.lean (import GMT.Ch08.Submission + replayed contract scope, autoImplicit false: 10 child statements, 6 verbatim sibling statements, parent assembly, comparator target)`
- `lean /tmp/allard-a1-decomp/scratch/Skel2.lean (sorry-free Part B glue from children 8-9; Part A glue skeleton; s = 1 uniqueness and dilation interface checks)`
- `lean /tmp/allard-a1-decomp/scratch/Axioms2.lean (#print axioms for 13 cited SimonGMT lemmas)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-08.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/TangentRadialRigidity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/TangentRescaling.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/ConstancyTangentGraph.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/ConstancyTangent.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/RadialFirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/BallVariationBound.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/EuclideanHausdorffUpper.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/tmp/allard-a1-decomp/scratch/Final.lean`
- `/tmp/allard-a1-decomp/scratch/Skel2.lean`
- `/tmp/allard-a1-decomp/scratch/Axioms2.lean`

The snapshot is project 63436ae6 with Mathlib 25730c7c. Its project/GMT/Ch08/Contract.lean is byte-identical to the workspace Contract and Submission, and the pinned SimonGMT is 2b366308. Mathlib has no varifold theory, so the Ch. 8 facts enter the children only as explicit hypotheses copied verbatim from the frozen sibling statements in dag.json, or as the contract's named Props. SimonGMT supplies the needed library lemmas: Varifold.weight_support_eq_fst_image_support, Stationary.hasLocallyBoundedFirstVariation, Grassmannian.eq_of_plane_eq, Grassmannian.continuous_normalProject, Chapter03.HasWeightedApproximateTangentSpaceAt (no r^{-n} factor) with .unique, support/regular_euclideanHausdorffMeasure_restrict_submodule, Chapter01.simon_theorem_3_3, measure_toOuterMeasure_isBorelRegular, realUnitBallVolume_nat_eq, volume_euclidean_ball_eq, simonHausdorffMeasureReal_toOuterMeasure, Chapter02.simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure and ae_exists_ballFirstVariationBound_inside. #print axioms for all 13 shows only propext, Classical.choice and Quot.sound. Several of them need extra imports in Submission: Chapter08.{RadialFirstVariation,ConstancyTangent,ConstancyTangentGraph}, Chapter01.{DensityComparison,EuclideanHausdorffUpper} and Chapter02.AreaLiteral. Mathlib supplies Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet, Isometry.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.euclideanHausdorffMeasure_smul₀, Measure.ext_of_integral_eq_on_compactlySupported, Measure.restrict_congr_set and restrict_apply₀' (both for arbitrary sets), MeasurableEquiv.restrict_map, lintegral_map_equiv, Measure.measure_toMeasurable_inter_of_sFinite and LipschitzWith.hausdorffMeasure_image_le. Grassmannian N n has a CompactSpace instance but no MetricSpace instance, so plane uniqueness uses matrix-entry test functions. All 10 child lean_statements pass validate_lean_statement and elaborate after import GMT.Ch08.Submission in the comparator's replayed scope, also with autoImplicit false. The parent term, built from the 6 verbatim sibling interfaces and the 10 children, checks against AllardRectifiabilityTheorem ∧ TangentConesAreRectifiableCones and adds no sorry of its own. The names allard_tc_* occur nowhere else in the run, GMT/ or dag.json (45 nodes).
