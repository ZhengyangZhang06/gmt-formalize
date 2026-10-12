# Parent-supplied natural-language proof

- Parent DAG node: `root.first_rectifiability-a1`
- Child DAG node: `root.first_rectifiability-a1.tangent_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step (0c) of the parent proof of Simon, Ch. 8, Theorem 1.2 (cf. Ch. 3, Remark 1.8(2)). Notation: μ := V.weight; ω := unitBallVolume n = volume(ball (0 : ℝ^n) 1) where ℝ^n := EuclideanSpace ℝ (Fin n); B_ρ(y) := closedBall y ρ; H^n := μHE[n].

1. By HasTangentPlane, x ∈ U and θ > 0. U is open (V.isOpen_domain), so there is r₀ > 0 with closedBall x r₀ ⊆ U; for 0 < t ≤ r₀ the ball B_t(x) is compact and contained in U, hence μ(B_t(x)) < ∞ (Varifold.weight_finite_on_compact).

2. ω ∈ (0, ∞): the open unit ball of ℝ^n is a nonempty bounded open set and volume is an additive Haar measure (measure_ball_pos, measure_ball_lt_top).

3. Plane balls: H^n(T.plane ∩ B_κ(0)) = ω κ^n for κ > 0. Indeed finrank T.plane = n (Grassmannian.finrank_plane), so there is a linear isometry equivalence e : ℝ^n ≃ₗᵢ[ℝ] T.plane (coordinates of an orthonormal basis of T.plane indexed by Fin n); ι := Subtype.val ∘ e : ℝ^n → ℝ^N is an isometry with range T.plane, and ι(closedBall 0 κ) = T.plane ∩ closedBall 0 κ (ι is linear, norm-preserving and onto T.plane). By Isometry.euclideanHausdorffMeasure_image and EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Mathlib Geometry/Euclidean/Volume/Measure.lean:131,187), H^n(T.plane ∩ B_κ(0)) = volume(closedBall (0 : ℝ^n) κ) = ENNReal.ofReal(κ^n) · ω (Measure.addHaar_closedBall, finrank ℝ^n = n). (For n = 0 this reads H^0({0}) = 1 = ω.) In particular H^n⌞T.plane is finite on bounded sets, so every g ∈ C_c(ℝ^N) is H^n⌞T.plane-integrable.

4. Cutoffs: for 0 < a < b put χ_{a,b}(y) := max(0, min(1, (b − |y|)/(b − a))). It is continuous, 0 ≤ χ_{a,b} ≤ 1, χ_{a,b} = 1 on B_a(0) and χ_{a,b} = 0 outside ball 0 b; hence tsupport χ_{a,b} ⊆ B_b(0) is compact and χ_{a,b} ∈ C_c(ℝ^N).

5. Lower bound. Let κ ∈ (0, 1) and g := χ_{κ,1}. For 0 < t ≤ r₀ and all z, 0 ≤ g(t⁻¹ • (z − x)) ≤ 1_{B_t(x)}(z). The function z ↦ g(t⁻¹ • (z − x)) is continuous, bounded and vanishes outside B_t(x), which has finite μ-measure, so it is μ-integrable and ∫ g(t⁻¹ • (z − x)) dμ ≤ μ(B_t(x)).toReal. By frt_weight_blowup_tendsto, t⁻¹ ^ n ∫ g(t⁻¹ • (z − x)) dμ → θ ∫_{T.plane} g dH^n ≥ θ (H^n(T.plane ∩ B_κ(0))).toReal = θ ω.toReal κ^n (g ≥ 1 on B_κ(0), g ≥ 0, θ > 0). Hence liminf_{t↓0} t^{−n} μ(B_t(x)).toReal ≥ θ ω.toReal κ^n.

6. Upper bound. Let κ > 1 and g := χ_{1,κ}. For 0 < t ≤ r₀/κ, 1_{B_t(x)}(z) ≤ g(t⁻¹ • (z − x)) ≤ 1_{B_{κt}(x)}(z) and μ(B_{κt}(x)) < ∞, so μ(B_t(x)).toReal ≤ ∫ g(t⁻¹ • (z − x)) dμ, and by frt_weight_blowup_tendsto, t⁻¹ ^ n times the right-hand side tends to θ ∫_{T.plane} g dH^n ≤ θ (H^n(T.plane ∩ B_κ(0))).toReal = θ ω.toReal κ^n (g ≤ 1_{B_κ(0)}). Hence limsup_{t↓0} t^{−n} μ(B_t(x)).toReal ≤ θ ω.toReal κ^n.

7. Letting κ ↑ 1 in 5 and κ ↓ 1 in 6 gives t^{−n} μ(B_t(x)).toReal → θ ω.toReal as t ↓ 0.

8. For 0 < t ≤ r₀ the quantities μ(B_t(x)), ω, ENNReal.ofReal t ^ n are finite and the last two are positive, so densityRatio n μ x t = μ(B_t(x)) / (ω · ENNReal.ofReal t ^ n) = ENNReal.ofReal(t^{−n} μ(B_t(x)).toReal / ω.toReal). By 7 and continuity of ENNReal.ofReal, densityRatio n μ x t → ENNReal.ofReal(θ ω.toReal / ω.toReal) = ENNReal.ofReal θ as t ↓ 0, which is HasDensity n V.weight x (ENNReal.ofReal θ). ∎

## Key steps

1. x ∈ U and θ > 0; μ_V(B_t(x)) < ∞ for small t.
2. H^n(T.plane ∩ B_κ(0)) = ω_n κ^n via a linear isometry ℝ^n → T.plane.
3. Continuous cutoffs below/above the unit ball with frt_weight_blowup_tendsto give liminf ≥ θω_nκ^n (κ < 1) and limsup ≤ θω_nκ^n (κ > 1).
4. Let κ → 1: t^{-n} μ_V(B_t(x)) → θ ω_n.
5. Rewrite densityRatio as ENNReal.ofReal of the real ratio and pass to the limit.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum project/GMT/Ch08/Contract.lean and workspace GMT/Ch08/{Contract,Submission}.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `rg -n 'def FirstRectifiabilityTheorem|def IsVarifoldOf|def HasTangentPlane|def HasDensity|def densityRatio|def rescaledMeasure|def planeVarifoldMeasure' project/GMT/Ch08/Contract.lean`
- `rg -n 'theorem ae_tendsto_measure_inter_div |theorem ae_tendsto_rnDeriv ' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `rg -n 'theorem hausdorffMeasure_image_le|theorem hausdorffMeasure_apply|theorem hausdorffMeasure_zero_singleton' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'Isometry.euclideanHausdorffMeasure_image|EuclideanSpace.euclideanHausdorffMeasure_eq_volume|euclideanHausdorffMeasure_homothety|euclideanHausdorffMeasure_zero |euclideanHausdorffMeasure_smul₀' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n 'theorem LipschitzOnWith.extend_real' mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `rg -n 'theorem withDensity_rnDeriv_eq ' mathlib/Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`
- `rg -n 'ext_of_integral_eq_on_compactlySupported$' mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `rg -n 'theorem ext_of_generateFrom_of_iUnion' mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `rg -n 'of_pseudoMetrizableSpace_of_isFiniteMeasure' mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `rg -n 'lemma measure_compl_support' mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `rg -n 'theorem addHaar_closedBall ' mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean (no Nontrivial assumption)`
- `rg -n 'lemma volume_euclideanSpace_eq_dirac' mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `rg -n 'theorem exists_countable_dense ' mathlib/Mathlib/Topology/Bases.lean`
- `rg -l -i 'varifold' mathlib/Mathlib | wc -l (0 files)`
- `grep -rn 'theorem eq_of_plane_eq|instance instCompactSpace|theorem simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure|theorem volume_euclidean_ball_eq|theorem measurable_closedBall_mass_of_sFinite|theorem mul_simonHausdorff_le_of_le_dimensionalUpperDensity|theorem simonHausdorffMeasureReal_toOuterMeasure' simongmt Poincare/SimonGMT`
- `sed Chapter03/Rectifiable.lean (CountablyRectifiable, blowUpMap, HasWeightedApproximateTangentSpaceAt(.unique), regular/support_euclideanHausdorffMeasure_restrict_submodule) and Chapter08/Varifold.lean (Varifold, Grassmannian, weight, finrank_plane)`
- `lake env lean Scratch/Final.lean (import GMT.Ch08.Submission + comparator scope replay: 2 sibling types + 12 child statements as sorry'd lemmas + parent assembly with no sorry)`
- `lake env lean Scratch/Ch_<key>.lean for each of the 12 children (comparator NodeChallenge form)`
- `lake env lean Scratch/Avail3.lean (#print axioms for 5 SimonGMT lemmas outside the Submission import closure: propext, Classical.choice, Quot.sound)`
- `lake env lean Scratch/Omega0.lean (unitBallVolume 0 = 1 via volume_euclideanSpace_eq_dirac)`
- `lake env lean Review/Mine2.lean (Borel ball mass via measurable_measure_prodMk_left; SimonGMT measurable_closedBall_mass_of_sFinite does not apply verbatim)`
- `python3 dag.json lean_name collision check (no collision among 45 nodes)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/ConstancyTangent.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/HausdorffDensityBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/EuclideanHausdorffUpper.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/InfiniteDensitySet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-08.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1/parent-child-handoff.json`

The snapshot is project 63436ae6 with Mathlib 25730c7c. Its Contract.lean is byte-identical to the workspace Contract and Submission. Mathlib contains no varifold theory, and pinned SimonGMT has neither Ch. 3, 1.6/1.9 nor an area formula on rectifiable carriers. Each child therefore builds on library facts that do exist. The Mathlib facts are Besicovitch.ae_tendsto_measure_inter_div / ae_tendsto_rnDeriv (Besicovitch.lean:1105/1078), LipschitzOnWith/LipschitzWith.hausdorffMeasure_image_le (Hausdorff.lean:733/745), hausdorffMeasure_apply (546), Isometry.euclideanHausdorffMeasure_image and EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Volume/Measure.lean:131/187), euclideanHausdorffMeasure_homothety_preimage and _smul₀ (152–172), LipschitzOnWith.extend_real (Lipschitz.lean:308), withDensity_rnDeriv_eq (RadonNikodym.lean:60), Measure.ext_of_integral_eq_on_compactlySupported (RieszMarkovKakutani/Real.lean:412), ext_of_generateFrom_of_iUnion (Restrict.lean:491), WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure (Regular.lean:1072), measure_compl_support (Support.lean:202), addHaar_closedBall (EqHaar.lean:500, no Nontrivial assumption), volume_euclideanSpace_eq_dirac (ω_0 = 1) and measurable_measure_prodMk_left. The SimonGMT facts are Grassmannian.instCompactSpace and finrank_plane, Chapter03 regular/support_euclideanHausdorffMeasure_restrict_submodule and HasWeightedApproximateTangentSpaceAt.unique, Grassmannian.eq_of_plane_eq (ConstancyTangent.lean:33), mul_simonHausdorff_le_of_le_dimensionalUpperDensity (DensityComparison.lean:251), simonHausdorffMeasureReal_toOuterMeasure and simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure (AreaLiteral.lean:42), and volume_euclidean_ball_eq (n > 0). The five SimonGMT lemmas outside Submission's import closure import cleanly and use only propext, Classical.choice and Quot.sound. SimonGMT measurable_closedBall_mass_of_sFinite is stated under a local Borel instance and does not apply verbatim, so the children cite measurable_measure_prodMk_left instead (checked in Lean). In a scratch copy importing GMT.Ch08.Submission with the comparator's replayed scope, all 12 child lean_statements elaborate, both together and as individual NodeChallenge files, and pass validate_lean_statement. The parent assembly checks against type FirstRectifiabilityTheorem with no sorry of its own. None of the frt_-prefixed names collides with any node of the 45-node DAG.
