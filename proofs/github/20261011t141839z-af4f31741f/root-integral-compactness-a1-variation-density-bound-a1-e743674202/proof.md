# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1`
- Child DAG node: `root.integral_compactness-a1.variation_density_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the printed estimates (1)–(2) in the proof of Simon 8.5.9 (step B3 of the parent proof), stated for general measures; in the application μ = μ_V (the limit varifold's weight) and ν_i = ‖δV_{φ(i)}‖. Notation: B_ρ(x) := closedBall x ρ; ω_n := unitBallVolume n ∈ (0,∞); W ⊂⊂ U means IsRelCompactOpenIn W U; all quantities are in [0,∞]; HasDensity n μ x θ means μ(B_ρ(x))/(ω_nρ^n) → θ as ρ ↓ 0.

1. Localisation. Fix an open W ⊂⊂ U. If W = ∅ put A_W := ∅ below (nothing to prove). Otherwise, since closure W is compact and U is open, choose r_W ∈ (0,1] with cthickening r_W (closure W) ⊆ U (Mathlib IsCompact.exists_cthickening_subset_open), and let W̃ := thickening r_W W = {y : infDist y W < r_W}. W̃ is open and bounded, and closure W̃ ⊆ cthickening r_W (closure W), a compact subset of U (closed and bounded); so W̃ ⊂⊂ U and S_W := sup_i ν_i(W̃) < ∞ by hypothesis. For ξ ∈ W and 0 < ρ < r_W, B_ρ(ξ) ⊆ W̃ (every point of B_ρ(ξ) has distance ≤ ρ < r_W from ξ ∈ W).

2. Relative bound on W. Let A_W := {ξ ∈ W : there is no c ∈ ℝ with liminf_i ν_i(B_ρ(ξ)) ≤ ofReal(c)·μ(B_ρ(ξ)) for all ρ ∈ (0, r_W)}. Claim: μ(A_W) = 0 (outer measure). Fix an integer j ≥ 1. For ξ ∈ A_W the constant c = j fails, so there is ρ_ξ ∈ (0, r_W) with liminf_i ν_i(B_{ρ_ξ}(ξ)) > j·μ(B_{ρ_ξ}(ξ)); since a liminf strictly exceeds a value only if the sequence eventually exceeds it (Mathlib Filter.eventually_lt_of_lt_liminf; [0,∞] is a complete lattice), there is i_ξ ∈ ℕ with ν_i(B_{ρ_ξ}(ξ)) > j·μ(B_{ρ_ξ}(ξ)) for all i ≥ i_ξ. For i ∈ ℕ let A_{W,i} := {ξ ∈ A_W : i_ξ ≤ i}; these sets increase with i and their union is A_W. Fix i. Apply the Besicovitch covering theorem (Simon Ch. 1, 3.12; SimonGMT Chapter01.exists_besicovitchCovering_families, from Mathlib Besicovitch.exist_disjoint_covering_families) to the closed balls B_{ρ_ξ}(ξ), ξ ∈ A_{W,i} (radii in (0,1]): there are N_B = N_B(N) subfamilies 𝓑_1, …, 𝓑_{N_B}, each consisting of pairwise disjoint balls, whose union covers A_{W,i}. Each 𝓑_l is countable (pairwise disjoint sets with non-empty interior in the separable space ℝ^N: Mathlib Set.PairwiseDisjoint.countable_of_nonempty_interior). Every B ∈ 𝓑_l is some B_{ρ_ξ}(ξ) with ξ ∈ A_{W,i}, so i ≥ i_ξ and μ(B) < j^{-1}ν_i(B); and B ⊆ W̃. Therefore μ(A_{W,i}) ≤ Σ_l Σ_{B∈𝓑_l} μ(B) ≤ j^{-1} Σ_l Σ_{B∈𝓑_l} ν_i(B) = j^{-1} Σ_l ν_i(⋃𝓑_l) ≤ j^{-1} N_B ν_i(W̃) ≤ N_B S_W / j. By continuity of the outer measure along increasing sequences of arbitrary (not necessarily measurable) sets (Mathlib Monotone.measure_iUnion), μ(A_W) = sup_i μ(A_{W,i}) ≤ N_B S_W / j. As j is arbitrary and S_W < ∞, μ(A_W) = 0.

3. Exhaustion. If U = ∅ then μ = 0 (μ(U^c) = 0) and the claim is trivial. Otherwise let K_p (p ∈ ℕ) be compact with K_p ⊆ interior K_{p+1} and ⋃_p K_p = U, and W_p := interior K_p: W_p is open, closure W_p ⊆ K_p is compact and contained in U, so W_p ⊂⊂ U, and ⋃_p W_p = U. By step 2 the set A := (ℝ^N ∖ U) ∪ ⋃_p A_{W_p} is μ-null (μ(ℝ^N ∖ U) = 0 by hypothesis; the hypothesis μ(K) < ∞ is not needed). Every ξ ∉ A lies in some W_p and, since ξ ∉ A_{W_p}, there is c_1 ∈ ℝ with liminf_i ν_i(B_ρ(ξ)) ≤ ofReal(c_1)·μ(B_ρ(ξ)) for all ρ ∈ (0, r_{W_p}); replacing c_1 by max{c_1, 0} we may assume c_1 ≥ 0.

4. From μ(B_ρ(ξ)) to ρ^n. Let D be the μ-null set of points ξ at which Θ^n(μ, ξ) does not exist as a finite value. For ξ ∉ A ∪ D let θ_ξ := Θ^n(μ, ξ) ∈ [0,∞) and p, c_1 as in step 3. Since μ(B_ρ(ξ))/(ω_nρ^n) → θ_ξ < θ_ξ + 1, there is r' > 0 with μ(B_ρ(ξ)) ≤ ofReal((θ_ξ + 1)ω_nρ^n) for 0 < ρ < r' (using the real values of θ_ξ and of ω_n ∈ (0,∞)). Put r := min{r_{W_p}, r'} > 0 and c := c_1(θ_ξ + 1)ω_n ∈ ℝ. For 0 < ρ < r: liminf_i ν_i(B_ρ(ξ)) ≤ ofReal(c_1)·μ(B_ρ(ξ)) ≤ ofReal(c_1)·ofReal((θ_ξ + 1)ω_nρ^n) = ofReal(cρ^n). Since A ∪ D is μ-null, this holds for μ-a.e. ξ. ∎

## Key steps

1. For open W ⊂⊂ U choose r_W and the enlarged W̃ ⊂⊂ U with S_W = sup_i ν_i(W̃) < ∞.
2. Besicovitch with N_B disjoint subfamilies: the set where no c gives liminf_i ν_i(B_ρ) ≤ cμ(B_ρ) for ρ < r_W has outer measure ≤ N_B S_W/j for every j, hence is μ-null.
3. Countable exhaustion of U and μ(U^c) = 0.
4. Finite density: μ(B_ρ(x)) ≤ (Θ+1)ω_nρ^n for small ρ, giving liminf_i ν_i(B_ρ(x)) ≤ cρ^n.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum snapshot project/GMT/Ch08/Contract.lean, workspace GMT/Ch08/Contract.lean, GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `rg -l -i varifold mathlib/Mathlib (0 files)`
- `rg -n 'theorem exist_disjoint_covering_families|theorem hausdorffMeasure_image_le|theorem lintegral_iUnion₀|theorem lintegral_tsum|theorem _root_.Monotone.measure_iUnion|theorem lintegral_map_equiv|theorem restrict_restrict_of_subset|theorem measure_toMeasurable_inter_of_sFinite|theorem restrict_toMeasurable_of_sFinite|euclideanHausdorffMeasure_smul₀|euclideanHausdorffMeasure_homothety_image|Isometry.euclideanHausdorffMeasure_image|EuclideanSpace.euclideanHausdorffMeasure_eq_volume|theorem hausdorffMeasure_zero_singleton|theorem lintegral_withDensity_eq_lintegral_mul₀|IsCompact.exists_cthickening_subset_open|Set.PairwiseDisjoint.countable_of_nonempty_interior|theorem eventually_lt_of_lt_liminf|theorem ae_restrict_iff'₀|theorem exists_measurable_subset_ae_eq|theorem AEMeasurable.indicator₀|theorem measure_inter_add_sdiff₀|theorem lintegral_eq_lintegral_meas_lt' mathlib/Mathlib`
- `grep -n 'structure Varifold|def weight|def firstVariationNormOn|def HasLocallyBoundedFirstVariation|def domainMeasure|def project|def projectionLinearMap' simongmt Chapter08/Varifold.lean; grep RadonConverges Chapter08/VarifoldConvergence.lean`
- `grep -n 'def CountablyRectifiable|def HasWeightedApproximateTangentSpaceAt|def blowUpMap' simongmt Chapter03/Rectifiable.lean`
- `grep -n 'theorem simon_theorem_3_3|theorem simon_theorem_3_6|theorem mul_simonHausdorff_le_of_le_dimensionalUpperDensity|measurable_dimensional(Upper|Lower)Density|exists_besicovitchCovering_families' simongmt Chapter01/{DensityComparison,Densities}.lean`
- `grep -n 'hasDerivAt_normalized_weightedCutoffMass|weightedCutoffMass|weightedRadialVectorField|weightedRadialGradientTerm' simongmt Chapter08/WeightedRadialIdentity.lean; grep -n 'scaledRadialCutoff|squaredRadialVectorField' Chapter04/FirstVariation.lean`
- `grep -n 'isFirstVariationPolarRepresentation_riesz|firstVariationRieszMeasure_eq_norm|isFirstVariationMeasure_riesz' simongmt Chapter08/FirstVariationRiesz.lean`
- `python3 gmt-compare.py contract_scope(Contract.lean) -> replayed scope: open Set Filter MeasureTheory Metric; open scoped Topology ENNReal CompactlySupported Pointwise; namespace GMT.Ch08; open Poincare.SimonGMT; open Poincare.SimonGMT.Chapter08; section/end Definitions`
- `lake build GMT.Ch08.Submission && lake env lean Test/Assembly2.lean (scratch copy /tmp/ic-decomp-cAI8Ux: 8 child statements in comparator form + 6 sibling stubs + parent term Submission.integral_compactness_theorem : IntegralCompactnessTheorem; no sorry in the parent)`
- `lake env lean Test/Axioms.lean (#print axioms for 11 cited SimonGMT lemmas: propext, Classical.choice, Quot.sound only)`
- `python3 -c validate_lean_statement (verifier/lean_contract.py) on all 8 lean_statements; dag.json lean_name scan for collisions`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Layercake.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/AEMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/VarifoldConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/FirstVariationRiesz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/WeightedRadialIdentity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root/decomposition-v2.json`
- `/tmp/ic-decomp-cAI8Ux/Test/Assembly2.lean`
- `/tmp/ic-decomp-cAI8Ux/Test/Axioms.lean`

Snapshot = project 63436ae6 + Mathlib 25730c7c. Its Contract is byte-identical to the workspace Contract and Submission. Mathlib has no varifold theory (0 files), so all Ch. 8 obligations are proved in the DAG. Every Mathlib lemma cited in the child proofs exists in the snapshot with suitable hypotheses: the Besicovitch covering families, the Lipschitz/Hölder image bounds for Hausdorff measure, Euclidean Hausdorff measure scaling, isometry invariance and agreement with volume, the s-finite measurable-hull identities, restrict_restrict_of_subset, Monotone.measure_iUnion, lintegral_iUnion₀/tsum/map_equiv/withDensity, cthickening, countability of disjoint families, and the liminf lemmas. The SimonGMT lemmas used — Theorems 3.3/3.6, Borel-measurable densities, the Besicovitch families 3.12, the weighted radial identity 3.5, the Riesz polar representation and 2.5 characterization, and simonHausdorffMeasureReal = μHE[n] — exist in the pinned package and use only propext, Classical.choice and Quot.sound. 3.5 lives in Chapter08.WeightedRadialIdentity, which Submission does not import. In a scratch copy with the comparator's replayed contract scope, all 8 child lean_statements elaborate in the exact comparator form and pass validate_lean_statement. With the 8 children and 6 frozen root-level sibling types as sorried stubs, the parent assembly `Submission.integral_compactness_theorem : IntegralCompactnessTheorem` type-checks with no sorry of its own. dag.json and the node files reserve no `intcpt_*` names, so all 8 lean_names are fresh.
