# Parent-supplied natural-language proof

- Parent DAG node: `root.tangent_graph_cover-a1`
- Child DAG node: `root.tangent_graph_cover-a1.weight_blowup-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step (1.1) of the parent proof (the cone/Lipschitz-graph argument of Simon's printed proof of Ch. 3, Thm 1.6 '⇐', run at varifold tangent points in the sense of Ch. 8, Def. 1.1), with every identification written out. Notation: μ := V.weight = V.measure.map Prod.fst; G := Grassmannian N n; H := μHE[n] on ℝ^N; W := (T.plane : Set ℝ^N); for t > 0, φ_t : ℝ^N × G → ℝ^N × G, φ_t(z) := (t^{−1}·(z.1 − x), z.2), so rescaledMeasure V x t = ofReal(t^{−1}^n) • V.measure.map φ_t (definition); ι : ℝ^N → ℝ^N × G, ι(y) := (y, T), so planeVarifoldMeasure T = (H.restrict W).map ι (definition).

1. The lifted test function. Fix g ∈ C_c(ℝ^N, ℝ) and define f : ℝ^N × G → ℝ by f(y, S) := g(y). f = g ∘ Prod.fst is continuous. Let K := tsupport g ×ˢ univ. K is compact: tsupport g is compact because g has compact support, and G is a compact space (SimonGMT instance Grassmannian.instCompactSpace), so K = tsupport g × G is compact (IsCompact.prod with isCompact_univ). If z ∉ K then z.1 ∉ tsupport g, hence f(z) = g(z.1) = 0 (image_eq_zero_of_notMem_tsupport). By HasCompactSupport.intro, f has compact support, i.e. f ∈ C_c(ℝ^N × G, ℝ).

2. Applying Def. 1.1. The third conjunct of HasTangentPlane V x T θ, applied to f, gives
 ∫ f d(rescaledMeasure V x t) → θ · ∫ f d(planeVarifoldMeasure T) as t → 0 in 𝓝[>] 0.

3. The limit. ι is measurable (measurable_id.prodMk measurable_const) and f is continuous, hence a.e.-strongly measurable for every measure. By the change-of-variables formula for push-forward measures (integral_map),
 ∫ f d((H.restrict W).map ι) = ∫ f(ι(y)) d(H.restrict W)(y) = ∫ g(y) d(H.restrict W)(y) = ∫_{W} g dH.
 So the limit in step 2 is θ ∫_W g dH.

4. The blow-up integrals for t > 0. Let t > 0. (a) integral_smul_measure: ∫ f d(c • ν) = c.toReal · ∫ f dν for c ∈ [0,∞]; here c = ofReal(t^{−1}^n) and c.toReal = t^{−1}^n because t^{−1}^n ≥ 0 (ENNReal.toReal_ofReal). (b) φ_t is continuous, hence measurable, so integral_map gives ∫ f d(V.measure.map φ_t) = ∫ f(φ_t z) dV.measure(z) = ∫ g(t^{−1}·(z.1 − x)) dV.measure(z). (c) Prod.fst is measurable and y ↦ g(t^{−1}·(y − x)) is continuous, so integral_map gives ∫ g(t^{−1}·(z.1 − x)) dV.measure(z) = ∫ g(t^{−1}·(y − x)) d(V.measure.map Prod.fst)(y) = ∫ g(t^{−1}·(y − x)) dμ(y). Hence for every t > 0:
 ∫ f d(rescaledMeasure V x t) = t^{−1}^n · ∫ g(t^{−1}·(y − x)) dμ(y).
 No integrability is needed: integral_map and integral_smul_measure are identities of Bochner integrals, valid whether or not the integrands are integrable.

5. Conclusion. The functions t ↦ ∫ f d(rescaledMeasure V x t) and t ↦ t^{−1}^n ∫ g(t^{−1}(y − x)) dμ(y) agree on (0, ∞), and (0, ∞) ∈ 𝓝[>] 0 (self_mem_nhdsWithin). By Tendsto.congr', steps 2–4 give t^{−1}^n ∫ g(t^{−1}·(y − x)) dμ(y) → θ ∫_W g dH as t → 0 in 𝓝[>] 0, which is the claim. ∎

Formalization note (checked in a scratch copy importing GMT.Ch08.Submission): build f as ⟨⟨fun z ↦ g z.1, g.continuous.comp continuous_fst⟩, HasCompactSupport.intro (g.hasCompactSupport.prod isCompact_univ) _⟩; rewrite with integral_map (f := fun z ↦ f z) using Continuous.aestronglyMeasurable of map_continuous f; then filter_upwards [self_mem_nhdsWithin], unfold rescaledMeasure, rw [integral_smul_measure, integral_map, ENNReal.toReal_ofReal], and finish with integral_map along measurable_fst.

## Key steps

1. Lift g ∈ C_c(ℝ^N) to f(y,S) := g(y); f ∈ C_c(ℝ^N × G) because G is compact (f vanishes off tsupport g × G).
2. Apply the third conjunct of HasTangentPlane V x T θ to f.
3. Identify the limit: integral_map along y ↦ (y,T) turns θ∫ f dv(T) into θ∫_{T.plane} g dH^n.
4. For t > 0 identify the blow-up integral: integral_smul_measure (toReal(ofReal t^{−n}) = t^{−n}) and integral_map along φ_t and along Prod.fst give t^{−n}∫ g(t^{−1}(y − x)) dμ_V.
5. Transfer the limit with Tendsto.congr' on (0,∞) ∈ 𝓝[>] 0.

## Reference use

### local-project

Queries:
- `cat local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum project/GMT/Ch08/Contract.lean and workspace GMT/Ch08/Submission.lean (both 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `rg -n 'notation.*μHE|def euclideanHausdorffMeasure|theorem Isometry.euclideanHausdorffMeasure_image|euclideanHausdorffMeasure_eq_volume' mathlib/Mathlib`
- `rg -n 'theorem addHaar_closedBall' mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `rg -n 'countable_meas_pos_of_disjoint_iUnion|countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top' mathlib/Mathlib`
- `rg -n 'theorem tendsto_measure_cthickening' mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean`
- `rg -n 'theorem cthickening_closedBall|theorem mem_cthickening_of_dist_le|theorem cthickening_subset_of_subset|theorem mem_cthickening_iff' mathlib/Mathlib`
- `rg -n 'theorem exists_dense_seq|def denseSeq|theorem denseRange_denseSeq' mathlib/Mathlib/Topology`
- `rg -n 'theorem countable_iff_exists_subset_range' mathlib/Mathlib`
- `grep -n 'structure Varifold|def weight|instSigmaFinite|finite_on_compact|def project|def plane|finrank_plane|instCompactSpace' simongmt Poincare/SimonGMT/Chapter08/Varifold.lean`
- `rg -n 'theorem (norm_project|project_|inner_project)' simongmt Chapter08/*.lean; rg -n 'planeMeasure|locallyFinite_planeMeasure|unitBallVolume' simongmt`
- `#check after import GMT.Ch08.Submission for 35 cited lemmas (Scratch/Avail.lean)`
- `sed -n 100,280p book/sources/chapter-03-source.txt (printed proof of Ch. 3, Thm 1.6 ⇐)`
- `python3 validate_lean_statement (verifier/lean_contract.py) on the 7 statements; dag.json lean_name collision check`
- `lake env lean Scratch/Challenge_<key>.lean (7 files) and Scratch/Assembly.lean in a /tmp copy importing GMT.Ch08.Submission with the comparator's replayed scope`
- `lake env lean Scratch/Full2.lean and Scratch/FullCheck.lean (proofs of all 7 children with exact frozen types and of the parent; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Normed/Module/Ball/Pointwise.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Data/Set/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/RadialFirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/EuclideanHausdorffUpper.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-03-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-tangent-graph-cover-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`

The snapshot is project 63436ae6 plus Mathlib 25730c7c, and its Contract is byte-identical to the workspace Submission. Mathlib has no varifold theory, so no existing declaration matches any child. Mathlib does supply every tool the children use: Isometry.euclideanHausdorffMeasure_image and EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean:131,187), Measure.addHaar_closedBall (EqHaar.lean:500), Measure.countable_meas_pos_of_disjoint_iUnion (SFinite.lean:305), tendsto_measure_cthickening_of_isClosed (BorelSpace/Metric.lean:143), cthickening_closedBall (Normed/Module/Ball/Pointwise.lean:318), mem_cthickening_of_dist_le (Thickening.lean:201), denseSeq/denseRange_denseSeq (Topology/Bases.lean:373,378) and countable_iff_exists_subset_range (Data/Set/Countable.lean:119). The SimonGMT Varifold API is in the import closure of GMT.Ch08.Submission (Grassmannian.project/plane/finrank_plane/projectionLinearMap_isSymmetric/project_project/projectionLinearMap_apply_of_mem/instCompactSpace, Varifold.weight/weight_finite_on_compact/weight.instSigmaFinite). The SimonGMT lemmas norm_project_sq_add_norm_normalProject_sq (Chapter08/RadialFirstVariation.lean) and planeMeasure_unit_closedBall/locallyFinite_planeMeasure (Chapter04/TangentDensity.lean) are NOT in that closure (#check fails), so the child proofs derive Pythagoras and the plane-ball formula directly. All seven statements elaborate in the comparator scope and pass the validator. Scratch proofs of all seven with their exact frozen types, and of the parent from them, use only propext, Classical.choice and Quot.sound.
