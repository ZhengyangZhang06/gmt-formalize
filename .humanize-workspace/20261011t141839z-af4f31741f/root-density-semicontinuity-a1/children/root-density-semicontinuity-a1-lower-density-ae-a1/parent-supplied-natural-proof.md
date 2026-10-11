# Parent-supplied natural-language proof

- Parent DAG node: `root.density_semicontinuity-a1`
- Child DAG node: `root.density_semicontinuity-a1.lower_density_ae-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 8, printed proof of 3.7 (pp. 211–213), steps (1)–(5), and the covering part of Step 4, exactly as filled in by the parent proof (its Steps 3 and 4). In particular:
- the printed constant “c independent of i, j” is replaced by the liminf hypothesis, taken inside the liminf over q;
- μ_i of the possibly non-measurable sets B_i is the outer measure;
- only subadditivity and covering estimates are used.

Notation: μ_i = (V_i).weight, μ = V.weight, ‖δV_i‖ = variationMeasure (V_i), B_ρ(y) = closedBall y ρ, B°_ρ(y) = ball y ρ, and W ⊂⊂ U means IsRelCompactOpenIn W U. Let C ∈ ℕ be the constant given by the sibling besicovitch_ratio_cover_estimate for the ambient dimension N. Let (P1) denote the first conclusion of the sibling weight_portmanteau_of_radonConverges applied to V_i → V.

STEP 1 (the claim for one W). Claim: for every W ⊂⊂ U there is a set E_W with μ(E_W) = 0 such that 1 ≤ liminf_{ρ↓0} densityRatio n μ x ρ for every x ∈ W ∖ E_W.

1a. Choice of ρ₀ and W̃. closure W is compact and contained in the open set U, so there is ρ₀ > 0 with cthickening(ρ₀, closure W) ⊆ U (IsCompact.exists_cthickening_subset_open). Note cthickening(ρ₀, closure W) = cthickening(ρ₀, W) (cthickening_closure). Put W̃ := thickening(ρ₀, W) = {z : dist(z, W) < ρ₀}. Then:
 - W̃ is open and W̃ ⊆ cthickening(ρ₀, W) ⊆ U;
 - closure W̃ ⊆ cthickening(ρ₀, W) ⊆ U (closure_thickening_subset_cthickening);
 - closure W̃ is compact, as a closed subset of the compact set cthickening(ρ₀, closure W) (IsCompact.cthickening).
 So W̃ ⊂⊂ U and, by hypothesis, L := liminf_q ‖δV_q‖(W̃) < ∞. For y ∈ W: B°_{ρ₀}(y) ⊆ W̃ ⊆ U (ball_subset_thickening), hence B_ρ(y) ⊆ W̃ for 0 < ρ < ρ₀; also W ⊆ U. This is the parent's choice “2ρ₀ < dist(closure W, ℝ^N ∖ U)”, in a form that also covers U = ℝ^N.

1b. Good and bad sets (printed (1)). For i, k ∈ ℕ let A_{i,k} be the set of y ∈ W such that y ∉ B_i and ‖δV_i‖(B_ρ(y)) ≤ k·μ_i(B_ρ(y)) for all 0 < ρ < ρ₀ (with k·m written ofReal(k)·m). Let Bad_{i,k} := W ∖ A_{i,k}.

1c. Covering estimate (printed (2)). For all i and k ≥ 1: μ_i(Bad_{i,k}) ≤ C·k⁻¹·‖δV_i‖(W̃) + μ_i(B_i ∩ W).
 Proof. Let x ∈ Bad_{i,k} ∖ B_i. Then x ∈ W, x ∉ B_i and x ∉ A_{i,k}, so there is σ with 0 < σ < ρ₀ and k·μ_i(B_σ(x)) < ‖δV_i‖(B_σ(x)). As k ∈ (0,∞), μ_i(B_σ(x)) = k⁻¹·(k·μ_i(B_σ(x))) ≤ k⁻¹·‖δV_i‖(B_σ(x)) (ENNReal.inv_mul_cancel_left). Hence besicovitch_ratio_cover_estimate applies with (μ, ν, A, ρ₀, t) = (μ_i, ‖δV_i‖, Bad_{i,k} ∖ B_i, ρ₀, k⁻¹). It gives μ_i(Bad_{i,k} ∖ B_i) ≤ C·k⁻¹·‖δV_i‖(thickening(ρ₀, Bad_{i,k} ∖ B_i)) ≤ C·k⁻¹·‖δV_i‖(W̃); the last step holds because Bad_{i,k} ∖ B_i ⊆ W and thickening is monotone in the set. Finally, μ_i(Bad_{i,k}) ≤ μ_i(Bad_{i,k} ∩ B_i) + μ_i(Bad_{i,k} ∖ B_i) by subadditivity of the outer measure (measure_le_inter_add_sdiff), and Bad_{i,k} ∩ B_i ⊆ B_i ∩ W.

1d. The open sets O_{i,k} (printed (3)). Let O_{i,k} := interior(⋂_{ℓ ≥ i} Bad_{ℓ,k}). Then O_{i,k} is open, and O_{i,k} ⊆ Bad_{ℓ,k} for every ℓ ≥ i, so O_{i,k} ⊆ W ⊆ U. Also O_{i,k} ⊆ O_{i',k} whenever i ≤ i', because the intersection over ℓ ≥ i' is larger. For k ≥ 1: μ(O_{i,k}) ≤ C·k⁻¹·L.
 Proof. Put c := C·k⁻¹ ∈ [0,∞).
 - By (P1) for the open set O_{i,k} ⊆ U: μ(O_{i,k}) ≤ liminf_q μ_q(O_{i,k}).
 - For q ≥ i, O_{i,k} ⊆ Bad_{q,k}, so by 1c μ_q(O_{i,k}) ≤ c·‖δV_q‖(W̃) + μ_q(B_q ∩ W) eventually in q. Hence liminf_q μ_q(O_{i,k}) ≤ liminf_q (c·‖δV_q‖(W̃) + μ_q(B_q ∩ W)).
 - That liminf equals liminf_q c·‖δV_q‖(W̃), because μ_q(B_q ∩ W) → 0 by hypothesis (W ⊂⊂ U) (ENNReal.liminf_add_of_right_tendsto_zero).
 - Multiplication by the finite constant c is monotone and continuous on [0,∞] (ENNReal.continuous_const_mul), so it commutes with liminf (Monotone.map_liminf_of_continuousAt): liminf_q c·‖δV_q‖(W̃) = c·L.

1e. The null set (printed (5)). Let E_W := ⋂_{k ≥ 1} ⋃_{i ∈ ℕ} O_{i,k}. Fix k ≥ 1. Since O_{i,k} increases with i, continuity from below (Monotone.measure_iUnion) gives μ(E_W) ≤ μ(⋃_i O_{i,k}) = sup_i μ(O_{i,k}) ≤ C·k⁻¹·L. As C < ∞ and L < ∞, C·k⁻¹·L → 0 as k → ∞ (ENNReal.tendsto_inv_nat_nhds_zero, ENNReal.Tendsto.const_mul, ENNReal.Tendsto.mul_const). Hence μ(E_W) = 0.

1f. Lower density off E_W (printed (4)). Let x ∈ W ∖ E_W, and choose k ≥ 1 with x ∉ O_{i,k} for every i.
 Choice of y_i, q_i. Fix i. The set G_i := W ∩ B°_{1/(i+1)}(x) is open and contains x. If G_i ⊆ ⋂_{ℓ≥i} Bad_{ℓ,k}, then G_i ⊆ interior(⋂_{ℓ≥i} Bad_{ℓ,k}) = O_{i,k} (interior_maximal), so x ∈ O_{i,k}, a contradiction. Hence there are y_i ∈ G_i and q_i ≥ i with y_i ∉ Bad_{q_i,k}. Since y_i ∈ W, this means y_i ∈ A_{q_i,k}: y_i ∈ W, y_i ∉ B_{q_i}, and ‖δV_{q_i}‖(B_ρ(y_i)) ≤ k·μ_{q_i}(B_ρ(y_i)) for all 0 < ρ < ρ₀. Choose such y_i, q_i for every i.
 Mass lower bounds at y_i. For each i: y_i ∈ W ⊆ U and y_i ∉ B_{q_i}, so by hypothesis there is θ_i ≥ 1 with HasDensity n μ_{q_i} y_i θ_i. Moreover V_{q_i} has locally bounded first variation, B°_{ρ₀}(y_i) ⊆ U (1a), and Λ := k ≥ 0. The sibling weight_closedBall_lower_bound_of_density_ge_one, applied to the hypothesis MonotonicityFormula, yields e^{-kρ}·ω_n·ρ^n ≤ μ_{q_i}(B_ρ(y_i)) for every i and every 0 < ρ < ρ₀.
 Passing to the limit. q_i ≥ i, so q_i → ∞ (tendsto_atTop_mono). dist(y_i, x) < 1/(i+1) → 0, so y_i → x. B°_{ρ₀}(x) ⊆ U because x ∈ W (1a). The sibling lower_density_ge_one_of_nearby_mass_bounds (with Λ = k) therefore gives 1 ≤ liminf_{ρ↓0} densityRatio n μ x ρ. This proves the claim of Step 1.

STEP 2 (exhaustion; the covering part of the parent's Step 4).
 - For every x ∈ U pick r_x > 0 with B_{r_x}(x) ⊆ U; U, the domain of V, is open, so take half the radius of an open ball around x inside U.
 - W_x := B°_{r_x}(x) is open, and closure W_x ⊆ B_{r_x}(x) (closure_ball_subset_closedBall), which is compact and ⊆ U. So W_x ⊂⊂ U.
 - Because ℝ^N is second countable, there is a countable T ⊆ U with ⋃_{x∈T} W_x = ⋃_{x∈U} W_x (TopologicalSpace.isOpen_iUnion_countable). The latter union contains U, since x ∈ W_x.
 - Let E_x := E_{W_x} be given by Step 1.
 Let y be a point at which 1 ≤ liminf_{ρ↓0} densityRatio n μ y ρ fails. If y ∈ U, then y ∈ W_x for some x ∈ T, and y ∈ E_x (otherwise Step 1 would give the inequality at y). Hence the exceptional set is contained in Uᶜ ∪ ⋃_{x∈T} E_x. Now μ(Uᶜ) = V.measure(Uᶜ × G(N,n)) = 0 (Varifold.weight_apply and V.supported), and μ(⋃_{x∈T} E_x) = 0 as a countable union of null sets (measure_biUnion_null_iff). Therefore 1 ≤ liminf_{ρ↓0} densityRatio n μ y ρ for μ-almost every y. ∎

## Key steps

1. Fix W ⊂⊂ U; choose ρ₀ with cthickening(ρ₀, closure W) ⊆ U, so W̃ = thickening(ρ₀, W) ⊂⊂ U and L = liminf ‖δV_q‖(W̃) < ∞.
2. Printed (1)-(2): bad sets Bad_{i,k} = W ∖ A_{i,k}; the Besicovitch sibling gives μ_i(Bad_{i,k}) ≤ C k⁻¹ ‖δV_i‖(W̃) + μ_i(B_i ∩ W).
3. Printed (3): O_{i,k} = interior ⋂_{ℓ≥i} Bad_{ℓ,k}; portmanteau (P1) and μ_q(B_q ∩ W) → 0 give μ(O_{i,k}) ≤ C k⁻¹ L.
4. Printed (5): E_W = ⋂_k ⋃_i O_{i,k} has μ(E_W) ≤ C k⁻¹ L for every k, so μ(E_W) = 0.
5. Printed (4): for x ∈ W ∖ E_W pick y_i → x and q_i ≥ i with y_i ∈ A_{q_i,k}; the monotonicity sibling gives e^{-kρ}ω_nρ^n ≤ μ_{q_i}(B_ρ(y_i)); the limit sibling gives lower density ≥ 1 at x.
6. Step 4 exhaustion: countably many balls W_x ⊂⊂ U cover U (Lindelöf); the exceptional set ⊆ Uᶜ ∪ ⋃ E_x is μ-null.

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
