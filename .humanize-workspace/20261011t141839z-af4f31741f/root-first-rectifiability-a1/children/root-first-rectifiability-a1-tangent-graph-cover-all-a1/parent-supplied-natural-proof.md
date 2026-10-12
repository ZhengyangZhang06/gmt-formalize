# Parent-supplied natural-language proof

- Parent DAG node: `root.first_rectifiability-a1`
- Child DAG node: `root.first_rectifiability-a1.tangent_graph_cover_all-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the net-of-planes step in Steps 2 and 5 of the parent proof ("choose P_1, …, P_J ∈ G such that every T ∈ G satisfies ‖p_T − p_{P_j}‖ ≤ L/4 for some j"), which is the choice of the reference planes π_1, …, π_N in Simon's printed proof of Ch. 3, Theorem 1.6 ⇐ (p. 73). A countable dense family of planes replaces the finite net; this suffices because the resulting cover is countable anyway. Notation: G := Grassmannian N n; p_S := Grassmannian.project S (the function of the linear map projectionLinearMap S); "Γ is an L-graph over P" means ‖(y − z) − p_P(y − z)‖ ≤ L‖p_P(y − z)‖ for all y, z ∈ Γ.

1. Fix L ∈ (0, 1] and put ε := L/4 > 0.

2. Continuity of S ↦ p_S. Let Φ : G → (ℝ^N →L[ℝ] ℝ^N) send S to projectionLinearMap S regarded as a continuous linear map (LinearMap.toContinuousLinearMap). Φ is continuous: S ↦ S.1 is the continuous inclusion of the subtype into the real N×N matrices, and M ↦ LinearMap.toContinuousLinearMap ((LinearMap.toMatrix b b).symm M) (b the standard orthonormal basis) is a linear map between finite-dimensional spaces, hence continuous (LinearMap.continuous_of_finiteDimensional). Moreover Φ(S) v = p_S v. [Elementary alternative: |p_S v − p_{S'} v| ≤ (Σ_{i,j} (S_{ij} − S'_{ij})²)^{1/2} |v| by Cauchy–Schwarz in each coordinate.]

3. Countable net. G is a subspace of the second-countable metrizable space of real N×N matrices, hence second countable and separable; let D ⊆ G be countable and dense (TopologicalSpace.exists_countable_dense). For T ∈ G the set {S ∈ G : ‖Φ S − Φ T‖ < ε} is open by 2 and contains T, so it contains some P ∈ D. Then for every v ∈ ℝ^N, |p_T v − p_P v| = |(Φ T − Φ P) v| ≤ ‖Φ T − Φ P‖ |v| ≤ (L/4)|v|.

4. For each P ∈ D the hypothesis (applied with this L and P) provides Γ^P : ℕ → Set ℝ^N such that (a) every Γ^P_i is closed, (b) every Γ^P_i is an L-graph over P, and (c) every x with HasTangentPlane V x T θ and |p_T v − p_P v| ≤ (L/4)|v| for all v lies in some Γ^P_i. Fix such a choice for every P ∈ D (classical choice). Put C := {(P, Γ^P_i) : P ∈ D, i ∈ ℕ}, the image of the countable set D ×ˢ univ ⊆ G × ℕ under (P, i) ↦ (P, Γ^P_i); C is countable (Set.Countable.prod, Set.Countable.image).

5. For c = (P, Γ^P_i) ∈ C, c.2 = Γ^P_i is closed by (a) and an L-graph over c.1 = P by (b).

6. Covering. Let x satisfy HasTangentPlane V x T θ. By 3 there is P ∈ D with |p_T v − p_P v| ≤ (L/4)|v| for all v, and by (c) there is i with x ∈ Γ^P_i; thus x ∈ ⋃_{c ∈ C} c.2, witnessed by c = (P, Γ^P_i) ∈ C. (If G = ∅, i.e. n > N, then D = C = ∅ and there are no tangent points, so the statement holds as well.) ∎

## Key steps

1. S ↦ p_S is continuous into operators (finite-dimensional linear maps).
2. A countable dense D ⊆ G yields, for every T, some P ∈ D with |p_T v − p_P v| ≤ (L/4)|v|.
3. Apply the per-plane cover hypothesis to every P ∈ D.
4. C := {(P, Γ^P_i)} is countable; its sets are closed L-graphs and cover all tangent points.

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
