# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_tangent_cones-a1`
- Child DAG node: `root.allard_tangent_cones-a1.flat_blowup_ball_limits-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the portmanteau step of the supplied proof of Simon 8.5.5. Step A8 uses it for a sequence λ_j ↓ 0 (printed (9) and the display before it). Step B3(b) uses it for the full limit λ ↓ 0, by approximating 1_{B_1(0)} from above and below. It is stated here for an arbitrary filter so that one proof covers both uses.

Notation. G := Grassmannian N n. It is a compact Hausdorff space (SimonGMT Grassmannian.instCompactSpace; a closed bounded set of projection matrices). No metric on G is needed. μ := V.weight. H := μHE[n]. ω := (unitBallVolume n).toReal. B_r(y) is the closed ball and B°_r(y) the open ball. For r > 0, V_r := rescaledMeasure V x r = ofReal(r⁻¹^n) • V.measure.map Φ_r with Φ_r(z,S) := (r⁻¹(z − x), S).

1. ω ∈ (0,∞). unitBallVolume n = volume(ball 0 1) in EuclideanSpace ℝ (Fin n). The open unit ball is nonempty, so this volume is positive; it is bounded, so the volume is finite. Hence ω > 0 (for n = 0, ω = 1).

2. Good radii. U is open and x ∈ U, so there is δ > 0 with B_{3δ}(x) ⊆ U. For 0 < r ≤ δ the set B_{2r}(x) is compact and contained in U, so V.measure(B_{2r}(x) × G) < ∞ (Varifold.finite_on_compact). Since t_i → 0 within (0,∞) along l, eventually 0 < t_i ≤ δ.

3. Change of variables. Let 0 < r ≤ δ and let F be a bounded continuous function on ℝ^N × G that vanishes outside B_2(0) × G. Then ∫ F dV_r = r^{-n} ∫ F(r⁻¹(z − x), S) dV(z,S).
 Proof: integral_smul_measure gives ∫ F d(c • ν) = c.toReal · ∫ F dν with c = ofReal(r⁻¹^n), and c.toReal = r^{-n}. Then integral_map (Φ_r is continuous, F is measurable) gives ∫ F d(V.measure.map Φ_r) = ∫ F∘Φ_r dV.measure. The function F∘Φ_r is bounded and vanishes outside B_{2r}(x) × G, which has finite V-measure, so it is integrable.

4. The plane side. For F ∈ C_c(ℝ^N × G), ∫ F dv(T) = ∫ F(y,T) d(H⌞T.plane)(y), by integral_map along the measurable map y ↦ (y,T).

5. Cut-offs. For k ∈ ℕ, k ≥ 1, define on ℝ^N
 φ_k⁺(z) := max(0, 1 − k·max(0, |z| − 1)),   φ_k⁻(z) := min(1, k·max(0, 1 − |z|)).
 Both are continuous with values in [0,1].
 - φ_k⁺ equals 1 on B_1(0) and vanishes for |z| ≥ 1 + 1/k, so it vanishes outside B_2(0).
 - φ_k⁻ vanishes for |z| ≥ 1.
 Hence:
 (5a) φ_k⁻ ≤ 1_{B_1(0)} ≤ φ_k⁺ pointwise.
 (5b) As k → ∞, φ_k⁺(z) → 1_{B_1(0)}(z) and φ_k⁻(z) → 1_{B°_1(0)}(z) for every z. For |z| > 1, φ_k⁺(z) = 0 once k ≥ 1/(|z| − 1). For |z| < 1, φ_k⁻(z) = 1 once k ≥ 1/(1 − |z|).
 (5c) For r > 0, |r⁻¹(z − x)| ≤ 1 iff z ∈ B_r(x). So (5a) gives φ_k⁻(r⁻¹(z − x)) ≤ 1_{B_r(x)}(z) ≤ φ_k⁺(r⁻¹(z − x)).

6. Plane integrals of the cut-offs. Put c_k^± := ∫_{T.plane} φ_k^± dH. We claim c_k^± → ω.
 Let J : EuclideanSpace ℝ (Fin n) → ℝ^N be a linear isometry with range T.plane. It exists because finrank T.plane = n (Grassmannian.finrank_plane): compose a LinearIsometryEquiv from EuclideanSpace ℝ (Fin n) onto T.plane, built from an orthonormal basis of T.plane indexed by Fin n, with the subtype inclusion.
 - By Isometry.euclideanHausdorffMeasure_image and EuclideanSpace.euclideanHausdorffMeasure_eq_volume, H(J(E)) = vol_n(E) for every E.
 - J preserves norms and has range T.plane, so T.plane ∩ B_r(0) = J(B_r(0)) and T.plane ∩ B°_r(0) = J(B°_r(0)).
 - So H(T.plane ∩ B_1(0)) = vol_n(B_1(0)) = ω, H(T.plane ∩ B°_1(0)) = vol_n(B°_1(0)) = ω, and H(T.plane ∩ B_2(0)) = vol_n(B_2(0)) < ∞.
   For n ≥ 1, use Measure.addHaar_closedBall and Measure.addHaar_ball (finrank = n, and ℝ^n is nontrivial), which give vol_n(B_r(0)) = vol_n(B°_r(0)) = ofReal(r)^n·unitBallVolume n for r > 0.
   For n = 0, EuclideanSpace ℝ (Fin 0) is a single point: B_1(0) = B°_1(0) = B_2(0) = univ, each of volume 1 = unitBallVolume 0, and T.plane = {0}.
 In particular H(T.plane ∩ B_2(0)) < ∞. So 1_{B_2(0)} is H⌞T.plane-integrable and dominates every φ_k^±. By (5b) and dominated convergence, c_k⁺ → H(T.plane ∩ B_1(0)) = ω and c_k⁻ → H(T.plane ∩ B°_1(0)) = ω.

7. The case β ≥ 0. Fix a continuous β : G → ℝ with β ≥ 0, and put m_i := t_i^{-n} ∫_{B_{t_i}(x) × G} β(S) dV.
 For k ≥ 1 let F_k^±(z,S) := φ_k^±(z)·β(S). F_k^± is continuous and vanishes outside B_2(0) × G, which is compact because G is compact. So F_k^± ∈ C_c(ℝ^N × G).
 Let i be such that 0 < t_i ≤ δ. All three integrands below are bounded, measurable and vanish outside B_{2t_i}(x) × G, a set of finite V-measure. Monotonicity of the integral, (5c) and step 3 (after multiplying by t_i^{-n} > 0) give
  ∫ F_k⁻ dV_{t_i} ≤ m_i ≤ ∫ F_k⁺ dV_{t_i}.
 By hypothesis and step 4, along l,
  ∫ F_k^± dV_{t_i} → θ·∫ F_k^± dv(T) = θ·β(T)·c_k^±.
 Let L := θ·ω·β(T) and ε > 0. By step 6 choose k with |θβ(T)c_k⁺ − L| < ε and |θβ(T)c_k⁻ − L| < ε. Then eventually along l:
  m_i ≥ ∫ F_k⁻ dV_{t_i} > θβ(T)c_k⁻ − ε > L − 2ε,
  m_i ≤ ∫ F_k⁺ dV_{t_i} < θβ(T)c_k⁺ + ε < L + 2ε.
 Hence m_i → L along l (Metric.tendsto_nhds). The sign of θ plays no role here.

8. General β. G is compact and nonempty (T ∈ G), and a continuous function on a compact space is bounded, so c := sup_S |β(S)| < ∞ and β + c is continuous and ≥ 0. For 0 < t_i ≤ δ, the functions β(S) and the constant c are integrable on B_{t_i}(x) × G (bounded on a set of finite measure). By linearity, m_i(β) = m_i(β + c) − m_i(c). Step 7 applies to β + c and to the constant function c. So m_i(β) → θω(β(T) + c) − θωc = θωβ(T). This is the first conclusion.

9. The weight. Take β ≡ 1 (ContinuousMap.const). Then ∫_{B_r(x) × G} 1 dV = (V.measure(B_r(x) × G)).toReal = (μ(B_r(x))).toReal, by Varifold.weight_apply (closed balls are measurable). Step 8 with β ≡ 1 gives (μ(B_{t_i}(x))).toReal / t_i^n → θω along l, which is the second conclusion. ∎

## Key steps

1. Change of variables for rescaledMeasure: ∫F dV_{x,r} = r^{-n}∫F(r⁻¹(z−x),S) dV, and the integrands are integrable for small r because x ∈ U.
2. Continuous cut-offs φ_k⁻ ≤ 1_{B_1(0)} ≤ φ_k⁺ supported in B_2(0) and converging pointwise to 1_{B°_1} and 1_{B_1}.
3. H^n(T∩B_1(0)) = H^n(T∩B°_1(0)) = ω_n, via a linear isometry ℝ^n → T; dominated convergence gives ∫_T φ_k^± dH^n → ω_n.
4. For β ≥ 0, sandwich t^{-n}∫_{B_t(x)×G}β dV between ∫φ_k^±β dV_{x,t}; the hypothesis and an ε-argument give the limit θω_nβ(T).
5. For general β, write β = (β + sup|β|) − sup|β|; β ≡ 1 gives the weight limit θω_n.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum project/GMT/Ch08/Contract.lean GMT/Ch08/Contract.lean GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487); git rev-parse HEAD in .lake/packages/simongmt (2b3663083f3fe399b6296fb8eaee52169170e197)`
- `sed -n 480,700p book/chapter-08.txt (printed 5.1-5.9, proofs of 5.5 and 5.7)`
- `python3 dag.json dump of node ids, lean_names, lean_statements (siblings varifold_tangent_theorems, plane_disintegration, first_rectifiability_theorem, monotonicity_and_density_theorems, constancy_theorem, first_variation_theorems)`
- `contract_scope(Contract.lean, 'GMT.Ch08.main_theorem') and validate_lean_statement from verifier/gmt-compare.py and verifier/lean_contract.py`
- `grep -n '^def|^structure|^theorem' Chapter08/Varifold.lean; grep 'def Stationary|Stationary.hasLocallyBoundedFirstVariation|instCompactSpace'`
- `grep 'def HasWeightedApproximateTangentSpaceAt|def CountablyRectifiable|HasWeightedApproximateTangentSpaceAt.unique|support_euclideanHausdorffMeasure_restrict_submodule|regular_euclideanHausdorffMeasure_restrict_submodule' Chapter03/Rectifiable.lean`
- `grep '^theorem' Chapter08/TangentRadialRigidity.lean Chapter08/TangentRescaling.lean Chapter08/ConstancyTangentGraph.lean Chapter08/TangentScalingCounterexample.lean`
- `grep 'simon_theorem_3_3|simon_theorem_3_6|dimensionalUpperDensity|realUnitBallVolume_nat_eq|volume_euclidean_ball_eq|measure_toOuterMeasure_isBorelRegular|simonHausdorffMeasureReal_toOuterMeasure|simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure|eq_of_plane_eq|continuous_normalProject|ae_exists_ballFirstVariationBound_inside|IsSimonSubmanifold' (SimonGMT Chapter01/02/08)`
- `grep 'theorem ae_tendsto_measure_inter_div_of_measurableSet|theorem ae_tendsto_measure_inter_div' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `grep 'theorem' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (Isometry.euclideanHausdorffMeasure_image, euclideanHausdorffMeasure_smul0, EuclideanSpace.euclideanHausdorffMeasure_eq_volume)`
- `grep 'restrict_congr_set|restrict_apply0'|restrict_restrict_of_subset|MeasurableEquiv.restrict_map|lintegral_map_equiv|ext_of_integral_eq_on_compactlySupported|addHaar_closedBall|measure_toMeasurable_inter_of_sFinite|hausdorffMeasure_image_le|smul_closedBall|ofReal_div_of_pos|tendsto_measure_iInter_atTop' mathlib/Mathlib`
- `grep -rl allard_tc_ over the run directory, GMT/ and .swarm-worktrees (no matches); dag.json lean_name collision check (45 nodes, none)`
- `lake env lean GMT/Ch08/Submission.lean -o /tmp/allard-a1-decomp/olean/GMT/Ch08/Submission.olean`
- `lean /tmp/allard-a1-decomp/scratch/Final.lean (import GMT.Ch08.Submission + replayed contract scope, autoImplicit false: 10 child statements, 6 verbatim sibling statements, parent assembly, comparator target)`
- `lean /tmp/allard-a1-decomp/scratch/Skel2.lean (sorry-free Part B glue from children 8-9; Part A glue skeleton; s = 1 uniqueness and dilation interface checks)`
- `lean /tmp/allard-a1-decomp/scratch/Axioms2.lean (#print axioms for 13 cited SimonGMT lemmas)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-08.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/TangentRadialRigidity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/TangentRescaling.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/ConstancyTangentGraph.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/ConstancyTangent.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/RadialFirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/BallVariationBound.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/EuclideanHausdorffUpper.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/tmp/allard-a1-decomp/scratch/Final.lean`
- `/tmp/allard-a1-decomp/scratch/Skel2.lean`
- `/tmp/allard-a1-decomp/scratch/Axioms2.lean`

The snapshot is project 63436ae6 with Mathlib 25730c7c. Its project/GMT/Ch08/Contract.lean is byte-identical to the workspace Contract and Submission, and the pinned SimonGMT is 2b366308. Mathlib has no varifold theory, so the Ch. 8 facts enter the children only as explicit hypotheses copied verbatim from the frozen sibling statements in dag.json, or as the contract's named Props. SimonGMT supplies the needed library lemmas: Varifold.weight_support_eq_fst_image_support, Stationary.hasLocallyBoundedFirstVariation, Grassmannian.eq_of_plane_eq, Grassmannian.continuous_normalProject, Chapter03.HasWeightedApproximateTangentSpaceAt (no r^{-n} factor) with .unique, support/regular_euclideanHausdorffMeasure_restrict_submodule, Chapter01.simon_theorem_3_3, measure_toOuterMeasure_isBorelRegular, realUnitBallVolume_nat_eq, volume_euclidean_ball_eq, simonHausdorffMeasureReal_toOuterMeasure, Chapter02.simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure and ae_exists_ballFirstVariationBound_inside. #print axioms for all 13 shows only propext, Classical.choice and Quot.sound. Several of them need extra imports in Submission: Chapter08.{RadialFirstVariation,ConstancyTangent,ConstancyTangentGraph}, Chapter01.{DensityComparison,EuclideanHausdorffUpper} and Chapter02.AreaLiteral. Mathlib supplies Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet, Isometry.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.euclideanHausdorffMeasure_smul₀, Measure.ext_of_integral_eq_on_compactlySupported, Measure.restrict_congr_set and restrict_apply₀' (both for arbitrary sets), MeasurableEquiv.restrict_map, lintegral_map_equiv, Measure.measure_toMeasurable_inter_of_sFinite and LipschitzWith.hausdorffMeasure_image_le. Grassmannian N n has a CompactSpace instance but no MetricSpace instance, so plane uniqueness uses matrix-entry test functions. All 10 child lean_statements pass validate_lean_statement and elaborate after import GMT.Ch08.Submission in the comparator's replayed scope, also with autoImplicit false. The parent term, built from the 6 verbatim sibling interfaces and the 10 children, checks against AllardRectifiabilityTheorem ∧ TangentConesAreRectifiableCones and adds no sorry of its own. The names allard_tc_* occur nowhere else in the run, GMT/ or dag.json (45 nodes).
