# Parent-supplied natural-language proof

- Parent DAG node: `root.first_rectifiability-a1`
- Child DAG node: `root.first_rectifiability-a1.tangent_unique-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step (0d) of the parent proof of Simon, Ch. 8, Theorem 1.2 (limits of Radon measures are unique; cf. Ch. 3, Remark 1.5(1)). Notation: μ := V.weight, H^n := μHE[n].

1. Multiplicity. By frt_tangent_plane_hasDensity, HasDensity n μ x (ENNReal.ofReal θ) and HasDensity n μ x (ENNReal.ofReal θ'), i.e. the function densityRatio n μ x tends to both values along 𝓝[>] 0, a non-trivial filter. By tendsto_nhds_unique, ENNReal.ofReal θ = ENNReal.ofReal θ'. Since θ > 0 and θ' > 0 (second clause of HasTangentPlane), θ = θ' (ENNReal.ofReal_eq_ofReal_iff).

2. Plane measures have equal integrals. Let g ∈ C_c(ℝ^N). By frt_weight_blowup_tendsto applied to (T, θ) and to (T', θ'), the same function t ↦ t⁻¹ ^ n ∫ g(t⁻¹ • (z − x)) dμ(z) tends along 𝓝[>] 0 both to θ ∫_{T.plane} g dH^n and to θ' ∫_{T'.plane} g dH^n. By uniqueness of limits and θ = θ' ≠ 0, ∫ g d(H^n.restrict T.plane) = ∫ g d(H^n.restrict T'.plane).

3. Equality of measures. finrank T.plane = finrank T'.plane = n (Grassmannian.finrank_plane), so both H^n.restrict T.plane and H^n.restrict T'.plane are regular measures (SimonGMT Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule, Chapter03/Rectifiable.lean). By Measure.ext_of_integral_eq_on_compactlySupported (Mathlib MeasureTheory/Integral/RieszMarkovKakutani/Real.lean:412) and 2, H^n.restrict T.plane = H^n.restrict T'.plane.

4. Equality of planes. By SimonGMT Chapter03.support_euclideanHausdorffMeasure_restrict_submodule (the support of H^n⌞P is P for every n-dimensional subspace P), taking supports in 3 gives (T.plane : Set ℝ^N) = T'.plane, hence T.plane = T'.plane as submodules (SetLike.ext').

5. Equality of points of G. For S ∈ G the linear map p_S := projectionLinearMap S is symmetric and idempotent (Grassmannian.projectionLinearMap_isSymmetric, Grassmannian.projectionLinearMap_comp_self) with range S.plane; for every v, p_S v ∈ S.plane and v − p_S v ⊥ S.plane (⟨v − p_S v, p_S w⟩ = ⟨p_S v − p_S(p_S v), w⟩ = 0), so p_S is the orthogonal projection onto S.plane. Therefore T.plane = T'.plane forces p_T = p_{T'}; since LinearMap.toMatrix is injective, the matrices T.1 and T'.1 coincide, i.e. T = T' in the subtype G. (This is SimonGMT Grassmannian.eq_of_plane_eq, Chapter08/ConstancyTangent.lean:33, usable after adding the import Poincare.SimonGMT.Chapter08.ConstancyTangent.) With 1, T' = T ∧ θ' = θ. ∎

## Key steps

1. θ = θ' by uniqueness of the density limit (frt_tangent_plane_hasDensity).
2. Equal C_c integrals against H^n⌞T.plane and H^n⌞T'.plane (frt_weight_blowup_tendsto, θ = θ' > 0).
3. Regular measures with equal C_c integrals are equal.
4. Supports give T.plane = T'.plane.
5. A projection matrix is determined by its plane, so T = T'.

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
