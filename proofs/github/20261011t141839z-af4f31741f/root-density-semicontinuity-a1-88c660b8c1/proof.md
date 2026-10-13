# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.density_semicontinuity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 8, Theorem 3.7, Remark 3.8(1) and the printed proof of 3.7 (pp. 211–213). No erratum in the statement; details filled in: (a) the printed constant “c independent of i, j” is replaced by the liminf hypothesis exactly as stated (only liminf_i ‖δV_i‖(W̃) < ∞ is assumed), taken inside the liminf over q in step (3); (b) the sets B_i may be non-measurable, so μ_i(·) of them is outer measure (all estimates below are subadditivity/covering estimates, valid for outer measures); (c) the final “Θ^n(μ_V, y) ≥ 1” is a statement about the density, whose existence μ_V-a.e. comes from Lemma 3.6 (sibling monotonicity_density, third conjunct DensityExistsAE) applied to V. Notation: μ_i = μ_{V_i} = (Vi i).weight, μ = μ_V, ‖δV_i‖ = variationMeasure (Vi i), B_ρ(y) = closedBall y ρ, W ⊂⊂ U means IsRelCompactOpenIn W U (open, compact closure inside U).

Hypotheses: Vi → V (Varifold.RadonConverges, i.e. ∫ f dV_i → ∫ f dV for every f ∈ C_c(U × G)); each V_i has locally bounded first variation; liminf_i ‖δV_i‖(W) < ∞ for every W ⊂⊂ U; for every i and y ∈ U ∖ B_i, Θ^n(μ_i, y) exists and is ≥ 1; μ_i(B_i ∩ W) → 0 for every W ⊂⊂ U.

STEP 1 (first two conclusions; Remark 3.8(1), “a trivial consequence of the definitions”). For X ∈ K(U;ℝ^N), div_S X is a continuous function with compact support in U × G, so δV_i(X) → δV(X) (SimonGMT RadonConverges.firstVariation_tendsto). Hence for every set W, firstVariationNormOn V W ≤ liminf_i firstVariationNormOn V_i W (RadonConverges.firstVariationNormOn_le_liminf, VarifoldConvergence.lean). For open W ⊂⊂ U the sibling first_variation (2.5, IsFirstVariationMeasure) identifies variationMeasure V_i W = firstVariationNormOn V_i W; so the hypothesis gives liminf_i firstVariationNormOn V_i W < ∞, hence firstVariationNormOn V W < ∞ for all such W, i.e. V has locally bounded first variation (RadonConverges.hasLocallyBoundedFirstVariation), and then variationMeasure V W = firstVariationNormOn V W ≤ liminf_i variationMeasure V_i W for every open W ⊂⊂ U (RadonConverges.firstVariationRieszMeasure_le_liminf).

STEP 2 (portmanteau facts used below). Testing with functions of x alone (G is compact, so (x,S) ↦ f(x) is in C_c(U × G) for f ∈ C_c(U)), μ_i → μ as Radon measures on U. Consequently: (P1) μ(O) ≤ liminf_i μ_i(O) for open O ⊆ U; (P2) μ(K) ≥ limsup_i μ_i(K) for compact K ⊆ U (approximate 1_O from below and 1_K from above by functions in C_c(U), using inner/outer regularity of the Radon measure μ on U).

STEP 3 (the proof of 3.7). Fix W ⊂⊂ U and ρ0 > 0 with 2ρ0 < dist(closure W, ℝ^N ∖ U) (positive, closure W compact in U open; if U = ℝ^N simply take ρ0 := 1 — note Lean's infDist to ∅ is 0, so this case is treated separately); put W̃ := {x : dist(x, W) < ρ0}, which is open with compact closure inside U, so L := liminf_q ‖δV_q‖(W̃) < ∞. For y ∈ W and ρ < ρ0 we have B_ρ(y) ⊆ W̃ ⊆ U.
 (1) For i, j ≥ 1 let A_{i,j} be the set of y ∈ W ∖ B_i such that ‖δV_i‖(B_ρ(y)) ≤ j μ_i(B_ρ(y)) for all 0 < ρ < ρ0, and B_{i,j} := W ∖ A_{i,j}.
 (2) If x ∈ B_{i,j} then either x ∈ B_i ∩ W, or μ_i(B_σ(x)) < j^{-1}‖δV_i‖(B_σ(x)) for some σ ∈ (0, ρ0).
 Besicovitch. Let 𝔅 be the family of closed balls B_σ(x), x ∈ B_{i,j} ∖ B_i, σ ∈ (0,ρ0), satisfying (2). The centres form a bounded set, so by the Besicovitch Covering Lemma (Ch. 1 3.12) there are N = N(N_ambient) countable subfamilies 𝔅_1,…,𝔅_N ⊆ 𝔅, each pairwise disjoint, whose union covers B_{i,j} ∖ B_i. Summing (2) over them (all balls lie in W̃): μ_i(B_{i,j}) ≤ μ_i(B_{i,j} ∖ B_i) + μ_i(B_i ∩ W) ≤ N j^{-1} ‖δV_i‖(W̃) + μ_i(B_i ∩ W) (outer measure, countable subadditivity).
 (3) For i, j ≥ 1 put O_{i,j} := interior(∩_{ℓ≥i} B_{ℓ,j}) (open, ⊆ W). For q ≥ i, O_{i,j} ⊆ B_{q,j}, so by (P1) and the previous estimate μ(O_{i,j}) ≤ liminf_q μ_q(O_{i,j}) ≤ liminf_q (N j^{-1}‖δV_q‖(W̃) + μ_q(B_q ∩ W)) ≤ N j^{-1} L, using μ_q(B_q ∩ W) → 0 (liminf(a_q + b_q) ≤ liminf a_q + limsup b_q). Write c := N L.
 (4) Lower density outside the bad set. Fix j and suppose x ∈ W ∖ ∪_i O_{i,j}. Then for each i we can pick y_i ∈ W ∩ B°_{1/i}(x) with y_i ∉ ∩_{q≥i}B_{q,j} (W ∩ B°_{1/i}(x) is an open neighbourhood of x and x is not an interior point of ∩_{q≥i}B_{q,j}), hence q_i ≥ i with y_i ∉ B_{q_i,j}, i.e. y_i ∈ A_{q_i,j}: y_i ∈ W ∖ B_{q_i} and ‖δV_{q_i}‖(B_ρ(y_i)) ≤ j μ_{q_i}(B_ρ(y_i)) for 0 < ρ < ρ0. Since ball y_i ρ0 ⊆ U, the monotonicity formula 3.3 (sibling monotonicity_density, first conjunct MonotonicityFormula with Λ = j) gives Θ^n(μ_{q_i}, y_i) ≤ e^{jρ} ω_n^{-1} ρ^{-n} μ_{q_i}(B_ρ(y_i)) (0 < ρ < ρ0), and Θ^n(μ_{q_i}, y_i) ≥ 1 because y_i ∈ U ∖ B_{q_i} (uniqueness of limits identifies the two densities). So μ_{q_i}(B_ρ(y_i)) ≥ e^{-jρ} ω_n ρ^n for 0 < ρ < ρ0. Fix 0 < ρ < ρ0; for i large, |y_i − x| < ρ and B_{ρ−|y_i−x|}(y_i) ⊆ B_ρ(x), so by (P2) (B_ρ(x) compact ⊆ U) μ(B_ρ(x)) ≥ limsup_i μ_{q_i}(B_ρ(x)) ≥ limsup_i e^{-jρ}ω_n(ρ − |y_i − x|)^n = e^{-jρ} ω_n ρ^n. Hence the lower density liminf_{ρ↓0} μ(B_ρ(x))/(ω_nρ^n) ≥ 1 for every x ∈ W ∖ ∪_i O_{i,j}, for some j; i.e. it is ≥ 1 for every x ∈ W ∖ E_W, E_W := ∩_{j≥1} ∪_{i≥1} O_{i,j}.
 (5) μ(E_W) = 0: O_{i,j} increases with i, so μ(E_W) ≤ μ(∪_i O_{i,j}) = lim_i μ(O_{i,j}) ≤ c j^{-1} for every j.

STEP 4 (conclusion). By Step 1, V has locally bounded first variation, so by the sibling monotonicity_density (third conjunct, DensityExistsAE), Θ^n(μ, y) exists (and is finite) for μ-a.e. y. Cover U by countably many W ⊂⊂ U (e.g. W_m = {x ∈ U : |x| < m, dist(x, ℝ^N∖U) > 1/m}); off the μ-null set ∪_m E_{W_m} ∪ {density fails to exist} ∪ Uᶜ, the density exists and is ≥ its lower density ≥ 1. Hence ∀ᵐ y ∂μ_V, ∃ θ, HasDensity n μ_V y θ ∧ 1 ≤ θ. Together with Step 1 this is DensitySemicontinuity.

## Key steps

1. Remark 3.8(1): δV_i(X) → δV(X), so firstVariationNormOn is lower semicontinuous; with 2.5 this gives LBFV of V and ‖δV‖(W) ≤ liminf ‖δV_i‖(W) (SimonGMT VarifoldConvergence).
2. Portmanteau for weights: μ(O) ≤ liminf μ_i(O) (O open), μ(K) ≥ limsup μ_i(K) (K compact).
3. Printed (1)–(2): bad sets B_{i,j}; Besicovitch gives μ_i(B_{i,j}) ≤ N j^{-1}‖δV_i‖(W̃) + μ_i(B_i ∩ W).
4. Printed (3): μ(interior ∩_{ℓ≥i}B_{ℓ,j}) ≤ N j^{-1} liminf_q ‖δV_q‖(W̃) =: c/j.
5. Printed (4): outside ∪_i interior(∩_{ℓ≥i}B_{ℓ,j}), points y_i → x with 3.1 at y_i (Λ = j) and Θ ≥ 1 give μ_{q_i}(B_ρ(y_i)) ≥ e^{-jρ}ω_nρ^n by 3.3, hence lower density ≥ 1 at x.
6. Printed (5): the exceptional set has μ-measure ≤ c/j for all j, so is null; Lemma 3.6 for V gives existence of Θ^n(μ_V,·) a.e., hence Θ ≥ 1 a.e.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum project/GMT/Ch08/Contract.lean workspace GMT/Ch08/Contract.lean GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `rg -l -i 'varifold' mathlib/Mathlib (0 files)`
- `rg -n 'theorem ae_tendsto_measure_inter_div|theorem ae_tendsto_rnDeriv' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `rg -n 'theorem hausdorffMeasure_image_le' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'Isometry.euclideanHausdorffMeasure_image|EuclideanSpace.euclideanHausdorffMeasure_eq_volume|euclideanHausdorffMeasure_homothety_image' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n 'theorem LipschitzOnWith.extend_real' mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `rg -n 'theorem withDensity_rnDeriv_eq' mathlib/Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`
- `rg -n 'ext_of_integral_eq_on_compactlySupported' mathlib/Mathlib`
- `rg -n 'theorem measure_toMeasurable_inter_of_sFinite|theorem restrict_toMeasurable_of_sFinite' mathlib/Mathlib`
- `rg -n 'theorem addHaar_closedBall' mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `grep -n '^theorem|^def' simongmt Chapter03/{Rectifiable,SubmanifoldCover,DisjointCover,Differential}.lean`
- `grep -n '^theorem' simongmt Chapter02/{Area,AreaLipschitz,AreaNoninjective,AreaMultiplicity,AreaLiteral}.lean`
- `grep -n '^theorem' simongmt Chapter01/{DensityComparison,Densities,HausdorffDensityBounds,InfiniteDensitySet}.lean`
- `grep -rn 'theorem <name>' simongmt for hasDerivAt_pushforwardMeasure_cylinder_family_of_velocity, aemeasurable_imageMap, measurable_imageMap_domain, pushforwardMeasure_apply_of_contDiffOn, imageMap_preimage_cylinder_ae_of_fixed, eq_of_plane_eq, hasDerivAt_normalized_weightedCutoffMass, simonHausdorffMeasureReal_toOuterMeasure, volume_euclidean_ball_eq, mul_simonHausdorff_le_of_le_dimensionalUpperDensity, measurable_dimensionalUpperDensity`
- `lake env lean Scratch/Final.lean (import GMT.Ch08.Submission + comparator scope replay; 12 child statements + parent assembly + example : type_of% GMT.Ch08.main_theorem)`
- `lake env lean Scratch/Axioms.lean (#print axioms for 13 cited SimonGMT lemmas)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaNoninjective.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/HausdorffDensityBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/InfiniteDensitySet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DeformationIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/WeightedRadialIdentity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/ConstancyTangent.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/VarifoldConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`

Snapshot = project 63436ae6 + Mathlib 25730c7c; its project/GMT/Ch08/Contract.lean is byte-identical to the workspace Contract and Submission. Mathlib has no varifold theory (0 files), so every Ch. 8 result is proved in the DAG. Pinned SimonGMT Chapter03 has no Theorem 1.6/1.9 (no rectifiable ⇒ approximate tangents / density one) and no area formula on rectifiable carriers (Chapter02 area formulas have a Euclidean parameter domain) — the reason v1 was rejected — so the new decomposition avoids both: density one and the 5.9 mass/fibre comparison are proved with Lipschitz graphs of small slope from the new sibling tangent_graph_cover, using only Mathlib LipschitzOnWith.hausdorffMeasure_image_le (Hausdorff.lean:733/745), Isometry.euclideanHausdorffMeasure_image + EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean:131,187), Besicovitch.ae_tendsto_measure_inter_div / ae_tendsto_rnDeriv (Covering/Besicovitch.lean:1105,1078), withDensity_rnDeriv_eq (RadonNikodym.lean:60), LipschitzOnWith.extend_real (Lipschitz.lean:308), measure_toMeasurable_inter_of_sFinite (SFinite.lean:477), and SimonGMT simon_theorem_3_3 / simon_theorem_3_6 / measurable_dimensional{Upper,Lower}Density (Chapter01). The first-variation derivative is the kernel-checked Varifold.hasDerivAt_pushforwardMeasure_cylinder_family_of_velocity (DeformationIntegral.lean:266), whose hypotheses match the contract. #print axioms for the 13 newly cited SimonGMT lemmas shows only propext, Classical.choice, Quot.sound. In a scratch copy importing GMT.Ch08.Submission with the comparator's replayed scope, all 12 child lean_statements elaborate and pass validate_lean_statement, and the parent assembly term checks against type_of% GMT.Ch08.main_theorem with no sorry of its own. The active DAG contains only root, so no name reservations conflict; all lean_names are fresh bare identifiers.
