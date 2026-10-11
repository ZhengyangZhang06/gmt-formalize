# Parent-supplied natural-language proof

- Parent DAG node: `root.density_semicontinuity-a1`
- Child DAG node: `root.density_semicontinuity-a1.limit_mass_lower_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the second half of printed step (4) of the proof of 3.7 (“Fix 0 < ρ < ρ0; for i large, |y_i − x| < ρ and B_{ρ−|y_i−x|}(y_i) ⊆ B_ρ(x), so by (P2) μ(B_ρ(x)) ≥ limsup_i μ_{q_i}(B_ρ(x)) ≥ limsup_i e^{-jρ}ω_n(ρ − |y_i − x|)^n = e^{-jρ} ω_n ρ^n. Hence the lower density … ≥ 1”), stated for general Λ, q and y.

Notation: μ = V.weight, μ_j = (V_j).weight, ω_n = unitBallVolume n, and F(r) := ofReal(e^{-Λr}) · ω_n · ofReal(r)^n ∈ [0,∞) for r ∈ ℝ.

1. ω_n ∈ (0,∞): it is the Lebesgue measure of the open unit ball of ℝ^n (Metric.measure_ball_pos, measure_ball_lt_top). F is continuous from ℝ to [0,∞]: r ↦ ofReal(e^{-Λr})·ω_n and r ↦ ofReal(r)^n are continuous with finite values, and multiplication on [0,∞] is continuous at every pair of finite values (ENNReal.Tendsto.mul with the side conditions “≠ ∞”).

2. Mass bound for V. Fix ρ with 0 < ρ < ρ₀ and put K := B_ρ(x) (closed ball). K is compact and K ⊆ B°_{ρ₀}(x) ⊆ U, so by (P2) of the sibling weight_portmanteau_of_radonConverges, limsup_j μ_j(K) ≤ μ(K).
 Let d_i := dist(y_i, x) → 0 and r_i := ρ − d_i. Then r_i → ρ and, by continuity, F(r_i) → F(ρ).
 For every i with d_i < ρ (which holds for all large i): 0 < r_i ≤ ρ < ρ₀, and B_{r_i}(y_i) ⊆ K, since dist(z, y_i) ≤ r_i implies dist(z, x) ≤ r_i + d_i = ρ. By hypothesis, F(r_i) ≤ μ_{q_i}(B_{r_i}(y_i)) ≤ μ_{q_i}(K).
 Therefore F(ρ) = limsup_i F(r_i) ≤ limsup_i μ_{q_i}(K) ≤ limsup_j μ_j(K) ≤ μ(K).
 - The first inequality holds because F(r_i) ≤ μ_{q_i}(K) eventually.
 - The second holds because q_i → ∞: with f(j) = μ_j(K), limsup_i f(q_i) is the limsup of f along the image filter map q atTop (Filter.limsup_comp), and map q atTop ≤ atTop, so it is ≤ limsup_j f(j) (Filter.limsup_le_limsup_of_le).
 This is the first conclusion.

3. Lower density. For 0 < ρ < ρ₀ the denominator D(ρ) := ω_n·ofReal(ρ)^n lies in (0,∞), so step 2 gives ofReal(e^{-Λρ}) ≤ μ(B_ρ(x))/D(ρ) = densityRatio n μ x ρ (ENNReal.le_div_iff_mul_le). Since Ioo 0 ρ₀ ∈ 𝓝[>] 0, densityRatio n μ x ≥ ofReal(e^{-Λ·}) eventually along 𝓝[>] 0. Also ofReal(e^{-Λr}) → ofReal(e^0) = 1 as r → 0, by continuity. Hence 1 = liminf_{r↓0} ofReal(e^{-Λr}) ≤ liminf_{r↓0} densityRatio n μ x r (Tendsto.liminf_eq and liminf_le_liminf; in the complete lattice [0,∞] no boundedness side conditions are needed). This is the second conclusion. ∎

## Key steps

1. F(r) = e^{-Λr} ω_n r^n is continuous with finite values; ω_n ∈ (0,∞).
2. For fixed ρ < ρ₀ and large i, B_{ρ−d_i}(y_i) ⊆ B_ρ(x) =: K, so F(ρ − d_i) ≤ μ_{q_i}(K).
3. F(ρ) = lim F(ρ − d_i) ≤ limsup μ_{q_i}(K) ≤ limsup μ_j(K) ≤ μ_V(K), by q_i → ∞ and portmanteau (P2).
4. Dividing by ω_n ρ^n: densityRatio ≥ e^{-Λρ} on (0, ρ₀), whose limit at 0⁺ is 1, so the lower density is ≥ 1.

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
