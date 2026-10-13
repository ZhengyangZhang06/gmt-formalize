# Parent-supplied natural-language proof

- Parent DAG node: `root.density_semicontinuity-a1`
- Child DAG node: `root.density_semicontinuity-a1.monotonicity_mass_lower_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the application of 3.3 in printed step (4) of the proof of 3.7 (“the monotonicity formula 3.3 … gives Θ^n(μ_{q_i}, y_i) ≤ e^{jρ} ω_n^{-1} ρ^{-n} μ_{q_i}(B_ρ(y_i)), and Θ^n(μ_{q_i}, y_i) ≥ 1 … (uniqueness of limits identifies the two densities). So μ_{q_i}(B_ρ(y_i)) ≥ e^{-jρ} ω_n ρ^n”). Here it is stated for a single varifold and a general Λ.

1. Apply the hypothesis MonotonicityFormula to (N, n, U, V, x, ρ₀, Λ). Its hypotheses (local boundedness of the first variation, 0 < ρ₀, ball x ρ₀ ⊆ U, 0 ≤ Λ, and the ball bound (3.1) for 0 < ρ < ρ₀) are exactly ours. Discard the monotonicity conjunct. From the rest, obtain θ' with HasDensity n μ_V x θ' and, for all 0 < σ ≤ ρ' < ρ₀, θ' ≤ ofReal(e^{Λσ}) · densityRatio n μ_V x σ (first part of the last conjunct).

2. Uniqueness of the density. HasDensity n μ_V x θ and HasDensity n μ_V x θ' say that densityRatio n μ_V x tends to θ and to θ' along 𝓝[>] 0. This is a non-trivial filter on ℝ and [0,∞] is Hausdorff, so θ = θ' (tendsto_nhds_unique).

3. Fix ρ with 0 < ρ < ρ₀ and take σ = ρ' = ρ in step 1. By the definition of densityRatio, 1 ≤ θ = θ' ≤ ofReal(e^{Λρ}) · (μ_V(B_ρ(x)) / D), where D := ω_n · ofReal(ρ)^n and ω_n = unitBallVolume n.

4. D ∈ (0,∞). ω_n is the Lebesgue measure of the open unit ball of ℝ^n = EuclideanSpace ℝ (Fin n). It is positive, because an additive Haar measure charges nonempty open sets (Metric.measure_ball_pos), and finite (measure_ball_lt_top). Also ofReal(ρ)^n ∈ (0,∞) because ρ > 0.

5. Multiply the inequality of step 3 by ofReal(e^{-Λρ})·D:
 ofReal(e^{-Λρ})·D = ofReal(e^{-Λρ})·D·1
 ≤ ofReal(e^{-Λρ})·D·ofReal(e^{Λρ})·(μ_V(B_ρ(x))/D)
 = (ofReal(e^{-Λρ})·ofReal(e^{Λρ}))·(D·(μ_V(B_ρ(x))/D))
 = 1·μ_V(B_ρ(x)).
 This uses ofReal(a)·ofReal(b) = ofReal(ab) for a ≥ 0, e^{-Λρ}e^{Λρ} = 1, and D·(m/D) = m for D ≠ 0, ∞ (ENNReal.mul_div_cancel). By associativity, ofReal(e^{-Λρ})·D = ofReal(exp(-(Λρ))) * unitBallVolume n * ofReal(ρ)^n, which is the claim. ∎

## Key steps

1. MonotonicityFormula at (V, x, ρ₀, Λ) gives a density θ' with θ' ≤ e^{Λσ}·densityRatio(σ) for 0 < σ < ρ₀.
2. Uniqueness of limits along 𝓝[>] 0 gives θ = θ' ≥ 1.
3. With D = ω_n ρ^n ∈ (0,∞): 1 ≤ e^{Λρ} μ_V(B_ρ(x))/D, hence e^{-Λρ} ω_n ρ^n ≤ μ_V(B_ρ(x)).

## Reference use

### local-project

Queries:
- `cat local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum GMT/Ch08/Contract.lean GMT/Ch08/Submission.lean local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `cat simongmt Poincare/SimonGMT/Chapter08/VarifoldConvergence.lean; grep -n '^theorem\|^def' Chapter08/{Varifold,FirstVariationRiesz,BallVariationBound,StationaryMonotonicity,FirstVariationDensity,FirstVariationBounds}.lean`
- `grep -rn -i 'portmanteau\|le_liminf\|limsup_le\|liminf_le' simongmt/Poincare --include=*.lean; grep -rln RadonConverges simongmt/Poincare`
- `grep -n 'theorem exist_disjoint_covering_families' -A 12 and 'structure BallPackage' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `grep -rn 'countable_of_nonempty_interior\|countable_of_isOpen' mathlib/Mathlib/Topology/`
- `grep -n 'theorem exists_continuous_one_zero_of_isCompact\|theorem exists_compact_between' mathlib/Mathlib/Topology/UrysohnsLemma.lean mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean`
- `lake env lean Scratch/Api.lean Api2.lean Api3.lean (#check: HasBesicovitchCovering (Euclidean N), CompactSpace (Grassmannian N n), IsCompact.exists_cthickening_subset_open, IsCompact.cthickening, IsOpen.exists_iUnion_isClosed, TopologicalSpace.isOpen_iUnion_countable, closure_thickening_subset_cthickening, ball_subset_thickening, cthickening_closure, ENNReal.liminf_add_of_right_tendsto_zero, Monotone.map_liminf_of_continuousAt, ofReal_integral_eq_lintegral_ofReal, Filter.limsup_comp, limsup_le_limsup_of_le, ENNReal.inv_mul_cancel_left, measure_biUnion_null_iff; ENNReal.liminf_const_mul and ENNReal.mul_liminf: unknown constants)`
- `python3 -I gen.py: gmt-compare.contract_scope replay + lean_contract.validate_lean_statement on the 6 lean_statements; lake env lean Cmp/Challenge0..5.lean`
- `lake env lean Scratch/Small.lean, Scratch/C2.lean, Scratch/C3.lean, Scratch/C5.lean, Scratch/C6.lean, Scratch/All.lean (exact frozen statements with complete proofs + parent assembly + #print axioms)`
- `python3 dag.json lean_name collision check (15 nodes); grep -l -i portmanteau nodes/*/parent-supplied-natural-proof.md`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/UrysohnsLemma.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/VarifoldConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/FirstVariationRiesz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/BallVariationBound.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/FirstVariationDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-density-semicontinuity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`

Snapshot: project 63436ae6 + Mathlib 25730c7c. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. SimonGMT Chapter08/VarifoldConvergence.lean already proves RadonConverges.firstVariation_tendsto, firstVariationNormOn_le_liminf, hasLocallyBoundedFirstVariation and firstVariationRieszMeasure_le_liminf. FirstVariationRiesz.lean:218 firstVariationRieszMeasure_eq_norm identifies variationMeasure with firstVariationNormOn on W ⊂⊂ U. Remark 3.8(1) (child variation_lsc) therefore needs no sibling. The VarifoldConvergence module states that it does not prove the lower-density part. SimonGMT has no portmanteau for varifold weights: the only *_le_liminf lemmas are for first variation, BV and currents (Chapter06/Mass.lean WeaklyConvergesOn.massOn_le_liminf), hence the child weight_portmanteau. Mathlib supplies the needed tools: Besicovitch covering families (Covering/Besicovitch.lean:455 exist_disjoint_covering_families, whose BallPackage needs only bounded radii; HasBesicovitchCovering is inferred for Euclidean N); countability of disjoint balls (Topology/Bases.lean:493); Urysohn (UrysohnsLemma.lean:404, LocallyCompact.lean:172); and the thickening and ℝ≥0∞ liminf lemmas. ENNReal.liminf_const_mul does not exist, so the proofs use Monotone.map_liminf_of_continuousAt. All 6 child lean_statements pass validate_lean_statement and elaborate in the replayed contract scope. In a scratch copy, complete proofs of all 6 exact statements compile with axioms propext, Classical.choice and Quot.sound only, and the parent assembly via Submission.monotonicity_and_density_theorems checks against DensitySemicontinuity. dag.json has no lean_name collisions.
