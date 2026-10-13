# Parent-supplied natural-language proof

- Parent DAG node: `root.first_rectifiability-a1`
- Child DAG node: `root.first_rectifiability-a1.rectifiable_of_graph_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 2 of the parent proof (Simon, Ch. 3, proof of Theorem 1.6 ⇐, p. 74: every piece lies in the rotated graph of a Lipschitz map, by the Lipschitz extension theorem Ch. 2, 1.2). Notation: for P ∈ G := Grassmannian N n, p := Grassmannian.project P; ℝ^n := EuclideanSpace ℝ (Fin n).

1. Linear algebra. projectionLinearMap P is symmetric and idempotent (Grassmannian.projectionLinearMap_isSymmetric, Grassmannian.project_project), so ⟨p v, v − p v⟩ = ⟨v, p v − p(p v)⟩ = 0 and |v|² = |p v|² + |v − p v|²; in particular |p v| ≤ |v|. Its range is P.plane, of dimension n (Grassmannian.finrank_plane).

2. One graph. Fix c = (P, Γ) ∈ C. For y, z ∈ Γ, by 1 and the hypothesis, |y − z|² = |p(y − z)|² + |(y − z) − p(y − z)|² ≤ 2|p y − p z|². Hence p is injective on Γ, and h := Function.invFunOn p Γ satisfies h(p y) = y for y ∈ Γ and |h a − h b| ≤ √2 |a − b| for a, b ∈ p(Γ) (LipschitzOnWith √2 h (p '' Γ)).

3. Parametrising the plane. Let e : ℝ^n ≃ₗᵢ[ℝ] P.plane be a linear isometry equivalence (inverse coordinates of an orthonormal basis of P.plane, reindexed by Fin n via finrank P.plane = n) and ι := Subtype.val ∘ e : ℝ^n → ℝ^N, an isometry with range P.plane. Let S := ι⁻¹(p(Γ)) ⊆ ℝ^n and k := h ∘ ι. For a, b ∈ S, |k a − k b| ≤ √2 |ι a − ι b| = √2 |a − b|.

4. Extension (McShane). For each coordinate j ∈ Fin N the function k_j(a) := (k a) j is √2-Lipschitz on S (|u j − w j| ≤ |u − w| in EuclideanSpace), so by LipschitzOnWith.extend_real (Mathlib Topology/MetricSpace/Lipschitz.lean:308) there is a √2-Lipschitz g_j : ℝ^n → ℝ with g_j = k_j on S. Let F_c : ℝ^n → ℝ^N be the vector with coordinates g_j, F_c a := WithLp.toLp 2 (fun j ↦ g_j a). Then |F_c a − F_c b|² = Σ_j |g_j a − g_j b|² ≤ 2N |a − b|², so F_c is Lipschitz (with constant √(2N)), and F_c = k on S. (Alternatively use SimonGMT exists_lipschitz_extension_finiteDimensional, Chapter02/AreaDomain.lean, or Mathlib LipschitzOnWith.extend_pi transported along the continuous linear equivalence ℝ^N ≃ (Fin N → ℝ); any Lipschitz constant suffices.)

5. Γ ⊆ range F_c. For y ∈ Γ, p y ∈ P.plane = range ι, so p y = ι a for some a ∈ ℝ^n; then a ∈ S and F_c a = k a = h(ι a) = h(p y) = y.

6. Assembly. If C = ∅ then M ⊆ ∅, so M = ∅, which is countably n-rectifiable by Chapter03.countablyRectifiable_of_measure_zero (μHE[n] ∅ = 0). Otherwise C is countable and nonempty, so there is σ : ℕ → C with range σ = C (Set.Countable.exists_eq_range). Take M₀ := ∅ and F_j := F_{σ j}. Each F_j is Lipschitz by 4, and M ⊆ ⋃_{c ∈ C} c.2 ⊆ ⋃_j range F_j by 5. This is exactly Chapter03.CountablyRectifiable n M (∃ M₀ with μHE[n] M₀ = 0 and Lipschitz F_j : ℝ^n → ℝ^N, j ∈ ℕ, with M ⊆ M₀ ∪ ⋃_j range F_j). (Equivalently: each c.2 ⊆ range F_c is countably rectifiable by Chapter03.countablyRectifiable_range and Chapter03.CountablyRectifiable.mono; conclude with Chapter03.countablyRectifiable_sUnion for the countable family {c.2 : c ∈ C} and .mono.) ∎

## Key steps

1. Pythagoras for the symmetric idempotent p_P: |y − z|² ≤ 2|p y − p z|² on a 1-graph.
2. p_P is injective on Γ with √2-Lipschitz inverse h on p_P(Γ).
3. Compose with a linear isometry ℝ^n → P.plane and extend coordinatewise (McShane) to a Lipschitz F_c : ℝ^n → ℝ^N with Γ ⊆ range F_c.
4. Enumerate the countable family (empty case separately): CountablyRectifiable n M with M₀ = ∅.

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
