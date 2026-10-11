# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.plane_disintegration-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 8, Lemma 1.3 and its printed proof (pp. 207–208). The printed proof is followed; details filled in: (a) the differentiation theorem “XXX Theorem 3.23 of Ch. 1” is applied to finite restrictions of μ_V to compact subsets of U (μ_V need not be locally finite at ∂U); (b) the positive functional η̃^(x) is represented by Riesz's theorem for positive functionals on the compact space G (Ch. 1 4.12) — the printed appeal to 4.14 with a “total variation measure” gives the same measure, which is moreover a probability measure; (c) the second part is stated with lintegrals of β ≥ 0 and arbitrary Borel A (both sides vanish on A ∖ U). Notation: G = Grassmannian N n (compact metric space), μ = μ_V = V.weight, B_ρ(x) = closedBall x ρ, Gₙ(A) = A × G, 𝒦 = C(G,ℝ), 𝒦⁺ = {β ∈ 𝒦 : β ≥ 0}.

Statement. For every n-varifold V on U there is η : ℝ^N → Measure(G) such that (i) for μ-a.e. x, η(x) is a probability measure and, for every β ∈ 𝒦, ∫_{Gₙ(B_ρ(x))} β(S) dV(y,S) / μ(B_ρ(x)) → ∫ β dη(x) as ρ ↓ 0; (ii) for every Borel A ⊆ ℝ^N and β ∈ 𝒦⁺: ∫⁻_{Gₙ(A)} β(S) dV(x,S) = ∫⁻_A (∫⁻ β dη(x)) dμ(x).

0. Degenerate case. If n > N then G = ∅, V.measure = 0, μ = 0; take η ≡ 0: (i) is vacuous and both sides of (ii) are 0. Assume G ≠ ∅ below; fix S0 ∈ G.

1. Countable dense family. 𝒦 with the sup norm is separable (G compact metric), so there are β_1, β_2, … ∈ 𝒦⁺ dense in 𝒦⁺; we may take β_1 ≡ 1.

2. Differentiation (printed (1)–(2)). For each j define the Borel measure γ_j(B) := ∫_{Gₙ(B)} β_j(S) dV(y,S) on ℝ^N; then γ_j ≤ (sup β_j)·μ, γ_j vanishes off U and is finite on compact subsets of U, so γ_j ≪ μ. Let K_m be a compact exhaustion of U with K_m ⊆ interior K_{m+1}. Apply the differentiation / Radon–Nikodym theorem (Ch. 1, 3.23(i), 3.24(i); every Radon measure on ℝ^N has the symmetric Vitali property; formally Mathlib Besicovitch.ae_tendsto_rnDeriv and Measure.withDensity_rnDeriv_eq) to the finite measures γ_j⌞K_{m+1} and μ⌞K_{m+1}: for μ-a.e. x ∈ interior K_{m+1} (where small closed balls lie inside K_{m+1}),
 (1) e(x,j) := lim_{ρ↓0} γ_j(B_ρ(x))/μ(B_ρ(x)) exists (finite),
 and e(·,j) is μ-measurable with
 (2) ∫_A e(x,j) dμ(x) = γ_j(A) = ∫_{Gₙ(A)} β_j(S) dV for Borel A ⊆ U.
 Taking the union over m and j, there is a μ-null set Z with: for x ∉ Z, x ∈ U ∩ spt μ (μ(Uᶜ) = 0 by V.supported, μ(ℝ^N ∖ spt μ) = 0), μ(B_ρ(x)) ∈ (0,∞) for small ρ, and (1) holds for every j.

3. Limits for all β (printed (3)–(4)). For x ∉ Z write avg_ρ(β) := ∫_{Gₙ(B_ρ(x))} β dV / μ(B_ρ(x)). Since V(Gₙ(B_ρ(x))) = μ(B_ρ(x)), |avg_ρ(β) − avg_ρ(β')| ≤ sup|β − β'| (printed (3)). Given β ∈ 𝒦⁺ and ε > 0 choose β_j with sup|β − β_j| < ε; then limsup avg_ρ(β) − liminf avg_ρ(β) ≤ 2ε, so η̃^(x)(β) := lim_{ρ↓0} avg_ρ(β) exists (printed (4)). For general β ∈ 𝒦 write β = (β + c) − c with c = sup|β| (constants are in 𝒦⁺, avg_ρ(c) = c): the limit exists for all β ∈ 𝒦. η̃^(x) is linear, positive, and η̃^(x)(1) = 1.

4. Riesz (printed end of proof). By the Riesz representation theorem on the compact Hausdorff space G (Ch. 1 4.12; Mathlib RealRMK.rieszMeasure), for x ∉ Z there is a Radon measure η(x) on G with η̃^(x)(β) = ∫ β dη(x) for all β ∈ 𝒦; η(x)(G) = η̃^(x)(1) = 1, so η(x) is a probability measure. For x ∈ Z put η(x) := Dirac(S0). Part (i) follows: for x ∉ Z and small ρ the Lean quotient (∫_{B_ρ(x) ×ˢ univ} β(z.2) dV)/ (μ(B_ρ(x))).toReal equals avg_ρ(β) (μ(B_ρ(x)) is finite and positive for small ρ, and ∫_{B_ρ(x)×G} β dV is a finite Bochner integral since β is bounded).

5. Second part (printed “follows directly from (2), (3)”). Since e(x,j) = η̃^(x)(β_j) = ∫ β_j dη(x) for x ∉ Z, (2) gives ∫_{Gₙ(A)} β_j dV = ∫_A (∫β_j dη(x)) dμ(x) for Borel A ⊆ U. For β ∈ 𝒦⁺, Borel A and each m, choose β_{j_k} → β uniformly; on A ∩ K_m (finite μ-measure, and V(Gₙ(A ∩ K_m)) = μ(A ∩ K_m) < ∞) both sides converge (|∫β dη(x) − ∫β_{j_k} dη(x)| ≤ sup|β − β_{j_k}| as η(x) is a probability measure for x ∉ Z), so ∫_{Gₙ(A∩K_m)} β dV = ∫_{A∩K_m} (∫ β dη(x)) dμ(x). Both sides are countably additive in A, so summing over the disjoint pieces A ∩ (K_m ∖ K_{m−1}) and adding A ∖ U (where both sides vanish: V(Uᶜ × G) = 0 = μ(Uᶜ)) gives the identity for every Borel A, as an equality in [0,∞]; for β ≥ 0 the Bochner integrals here equal the lintegrals of ofReal(β) (∫⁻ ofReal(β) dη(x) = ofReal(∫ β dη(x)) for the probability measure η(x)), and the values of η on the μ-null set Z do not affect ∫⁻_A … dμ. This is part (ii).

## Key steps

1. Countable dense {β_j} ⊆ C(G)⁺.
2. Differentiation theorem for γ_j(B) = ∫_{Gₙ(B)}β_j dV ≪ μ_V on compact pieces of U: e(x,j) exists μ_V-a.e. and ∫_A e(·,j)dμ_V = γ_j(A) (printed (1)–(2)).
3. |avg_ρ(β) − avg_ρ(β')| ≤ sup|β − β'| (printed (3)), so the limit η̃^(x)(β) exists for all β (printed (4)); it is positive, linear, η̃^(x)(1) = 1.
4. Riesz on the compact space G: η̃^(x)(β) = ∫β dη(x), η(x) a probability measure; Dirac elsewhere.
5. Second part from (2) by uniform approximation on finite-measure pieces A ∩ K_m and countable additivity; lintegral form for β ≥ 0.

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
