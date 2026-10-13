# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1.integral_density-a1.tangent_point_density-a1`
- Child DAG node: `root.integral_compactness-a1.integral_density-a1.tangent_point_density-a1.ball_sandwich-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2–3 (cutoff comparison and sandwich) of the selected proof (Simon Ch. 3, Remark 1.8(2)), for one cutoff f and one radius r. Notation: H^n := μHE[n]; B̄_s(z) := closedBall z s; ν := (H^n⌞M).withDensity(ofReal ∘ θ); η := Chapter03.blowUpMap x r, η(z) = r⁻¹ • (z − x); I := ∫_{η(M)} f(y) θ(x + r•y) dH^n(y); and
 J := ∫⁻_M ofReal(f(η z)) · ofReal(θ z) dH^n(z) ∈ [0, ∞].

1. Where f ∘ η is 0 or 1. For every z, ‖η z‖ = r⁻¹‖z − x‖ = dist(z, x)/r (norm_smul, norm_inv, r > 0, dist_eq_norm).
 - If z ∈ B̄_{ra}(x), then dist(z, x) ≤ r·a, so ‖η z‖ ≤ a and f(η z) = 1.
 - If z ∉ B̄_{rR}(x), then dist(z, x) > r·R, so ‖η z‖ > R and f(η z) = 0.

2. ν on closed balls. For every s ∈ ℝ the closed ball B̄_s(x) is Borel, so
 ν(B̄_s(x)) = ∫⁻_{B̄_s(x)} ofReal θ d(H^n⌞M) (withDensity_apply)
 = ∫⁻_M 1_{B̄_s(x)}(z) · ofReal θ(z) dH^n(z) (lintegral_indicator).
 Neither step needs measurability of θ.

3. Sandwich of J. For every z:
 1_{B̄_{ra}(x)}(z) · ofReal θ(z) ≤ ofReal(f(η z)) · ofReal θ(z) ≤ 1_{B̄_{rR}(x)}(z) · ofReal θ(z).
 - Left inequality: for z ∈ B̄_{ra}(x), f(η z) = 1 by step 1 and both sides are equal; otherwise the left side is 0.
 - Right inequality: for z ∈ B̄_{rR}(x), ofReal(f(η z)) ≤ 1 because f ≤ 1 (ENNReal.ofReal_le_one); otherwise f(η z) = 0 by step 1 and the middle term is 0.
 Integrating over H^n⌞M (lintegral_mono, which needs no measurability) and using step 2 gives ν(B̄_{ra}(x)) ≤ J ≤ ν(B̄_{rR}(x)).

4. J < ∞. Since r·R ≤ r₀, B̄_{rR}(x) ⊆ B̄_{r₀}(x), so by step 3 and monotonicity J ≤ ν(B̄_{r₀}(x)). Moreover
 ν(B̄_{r₀}(x)) = ∫⁻_{B̄_{r₀}(x)} ofReal θ d(H^n⌞M) = ∫⁻_{M ∩ B̄_{r₀}(x)} ofReal θ dH^n (withDensity_apply, Measure.restrict_restrict, inter_comm),
 which is finite because θ is H^n-integrable on M ∩ B̄_{r₀}(x) (Integrable.lintegral_lt_top).

5. Change of variables. Apply the sibling lemma blowup_cov (Submission.intcpt_id_tpd_setIntegral_blowUpMap_image N n x r M F hr) to F(y) := f(y)·θ(x + r•y). It gives I = r⁻¹^n ∫_M f(η z) θ(x + r•η z) dH^n(z). Since x + r•η(z) = x + r•(r⁻¹•(z − x)) = z (smul_smul, mul_inv_cancel₀, one_smul, add_sub_cancel), this is I = r⁻¹^n ∫_M g dH^n with g(z) := f(η z)·θ(z). Hence r^n · I = ∫_M g dH^n, because r^n · r⁻¹^n = (r · r⁻¹)^n = 1.

6. Bochner integral as a lintegral: ∫_M g dH^n = J.toReal. Apply integral_eq_lintegral_of_nonneg_ae for the measure H^n⌞M; it needs (a) and (b).
 (a) g ≥ 0 H^n⌞M-a.e.: M is H^n-null-measurable, so H^n⌞M-a.e. z lies in M (ae_restrict_mem₀). There θ(z) ≥ 0, and f ≥ 0 everywhere.
 (b) g is AEStronglyMeasurable for H^n⌞M. Let B := B̄_{r₀}(x), a closed (hence measurable) set. By step 1 and B̄_{rR}(x) ⊆ B, g vanishes off B, so g = 1_B · g. By aestronglyMeasurable_indicator_iff it suffices that g is AEStronglyMeasurable for (H^n⌞M)⌞B = H^n⌞(B ∩ M) (Measure.restrict_restrict). The function z ↦ f(η z) is continuous (f continuous, η affine), hence AEStronglyMeasurable for every measure. θ is AEStronglyMeasurable for H^n⌞(M ∩ B), being integrable on M ∩ B = B ∩ M. So the product g is AEStronglyMeasurable there.
 The lemma gives ∫_M g dH^n = (∫⁻_M ofReal(g z) dH^n).toReal. Since f(η z) ≥ 0, ofReal(g z) = ofReal(f(η z)) · ofReal(θ z) (ENNReal.ofReal_mul, lintegral_congr). Hence the lintegral is J.

7. Conclusion. By steps 5–6, r^n · I = J.toReal, so ofReal(r^n · I) = ofReal(J.toReal) = J (ENNReal.ofReal_toReal, J ≠ ∞ by step 4). Step 3 now reads ν(B̄_{ra}(x)) ≤ ofReal(r^n · I) ≤ ν(B̄_{rR}(x)). ∎

## Key steps

1. ‖η z‖ = dist(z,x)/r, so f∘η = 1 on B̄_{ra}(x) and f∘η = 0 off B̄_{rR}(x).
2. ν(B̄_s(x)) = ∫⁻_M 1_{B̄_s(x)} ofReal θ dH^n (withDensity_apply, lintegral_indicator); pointwise comparison and lintegral_mono give ν(B̄_{ra}) ≤ J ≤ ν(B̄_{rR}).
3. J ≤ ν(B̄_{r₀}(x)) = ∫⁻_{M∩B̄_{r₀}(x)} ofReal θ dH^n < ∞ by integrability of θ.
4. Change of variables (sibling blowup_cov) with x + r•η(z) = z: r^n·I = ∫_M f(η z)θ(z) dH^n.
5. That integrand is a.e. ≥ 0 (ae_restrict_mem₀) and AEStronglyMeasurable (indicator of B̄_{r₀}(x)), so the integral equals J.toReal; then ofReal(r^n I) = J.

## Reference use

### local-project

Queries:
- `cat local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); diff GMT/Ch08/Contract.lean GMT/Ch08/Submission.lean (identical)`
- `grep -n 'HasDensity\|densityRatio\|unitBallVolume' GMT/Ch08/Contract.lean; sed -n 28,60p GMT/Ch08/Contract.lean`
- `grep -n 'def blowUpMap\|def HasWeightedApproximateTangentSpaceAt' -A 14 .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -rn 'abbrev Euclidean ' .lake/packages/simongmt/Poincare; grep -rn 'def ofSubmodule\|plane_ofSubmodule\|finrank_plane' .lake/packages/simongmt/Poincare/SimonGMT/Chapter08/`
- `rg -n 'euclideanHausdorffMeasure_smul₀|euclideanHausdorffMeasure_eq_volume|theorem Isometry.euclideanHausdorffMeasure_image' snapshot mathlib/Mathlib; grep -rn 'notation "μHE' snapshot mathlib/Mathlib`
- `rg -n 'theorem _root_.MeasurableEmbedding.integral_map|theorem restrict_map|theorem integral_smul_measure|theorem addHaar_closedBall |theorem integral_eq_lintegral_of_nonneg_ae|theorem ae_restrict_mem₀|theorem withDensity_apply |theorem lintegral_indicator |theorem Integrable.lintegral_lt_top|theorem integral_indicator_one|le_div_iff_mul_le|theorem div_le_of_le_mul |theorem measurePreserving \(|theorem measure_ball_pos|theorem measure_ball_lt_top|theorem Ioo_mem_nhdsLT|theorem ofReal_lt_ofReal_iff' snapshot mathlib/Mathlib`
- `python3 -I dag.json scan: lean_name/status/parent/lean_statement for frt_wat_setIntegral_blowUpMap_image, intcpt_canon_plane_closedBall_hausdorff, frt_td_hasDensity_of_ball_mass_bounds, frt_td_ball_mass_lower/upper_of_blowup, allard_tc_tpr_blowup_setIntegral; cross-parent reused children scan`
- `grep -c / grep -rl 'intcpt_id_tpd_' over dag.json, DAG.md, nodes/; git for-each-ref loop: git show REF:GMT/Ch08/Submission.lean | grep 'intcpt_id_tpd_\|intcpt_id_tangent_point_density'; grep -rl intcpt_id_tpd .lake/packages/simongmt and snapshot mathlib`
- `sed -n 274,326p book/chapter-03.txt (Simon Ch. 3, Definition 1.7 and Remark 1.8(2))`
- `verifier/gmt-compare.py child_modules + contract_scope (challenge form); python3 -I importlib verifier/lean_contract.py validate_lean_statement on all 8 statements`
- `lake env lean /tmp/tpd3-decomp/Full.lean; lake env lean /tmp/tpd3-decomp/Assembly.lean; lake env lean /tmp/tpd3-decomp/Challenge_{0..6}.lean; lake env lean /tmp/tpd3-decomp/PP.lean (set_option pp.parens/pp.coercions, #check of each child)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-integral-density-a1-tangent-point-density-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-integral-density-a1-tangent-point-density-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-tangent-plane-dilation-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/tpd-decomp/Full2.lean`
- `/tmp/tpd3-decomp/Full.lean`
- `/tmp/tpd3-decomp/Assembly.lean`
- `/tmp/tpd3-decomp/Challenge_0.lean`
- `/tmp/tpd3-decomp/PP.lean`

The snapshot is project 63436ae6 plus Mathlib 25730c7c, and Submission.lean is identical to Contract.lean.

Definitions used: Contract.lean defines unitBallVolume (Lebesgue volume of the open unit ball of ℝ^n), densityRatio and HasDensity. SimonGMT Chapter03/Rectifiable.lean defines blowUpMap x r y = r⁻¹ • (y − x) (line 96) and HasWeightedApproximateTangentSpaceAt (line 330): finrank P = n and the integrals of f y * θ (x + r • y) converge along 𝓝[>] 0. Euclidean N is EuclideanSpace ℝ (Fin N) (Varifold.lean:54), and μHE[d] is notation in Geometry/Euclidean/Volume/Measure.lean:72.

Every Mathlib lemma the child proofs cite is located in the snapshot, including:
- Isometry.euclideanHausdorffMeasure_image (Measure.lean:131)
- Measure.euclideanHausdorffMeasure_smul₀ (:152)
- InnerProductSpace.euclideanHausdorffMeasure_eq_volume (:191)
- MeasurableEmbedding.integral_map (Bochner/Basic.lean:1093)
- integral_eq_lintegral_of_nonneg_ae (:515)
- MeasurableEmbedding.restrict_map (Restrict.lean:890)
- ae_restrict_mem₀ (:637)
- withDensity_apply (WithDensity.lean:44)
- addHaar_closedBall (EqHaar.lean:500)
- LinearIsometryEquiv.measurePreserving (Haar/InnerProductSpace.lean:151)
- ENNReal.le_div_iff_mul_le and div_le_of_le_mul (ENNReal/Inv.lean:369 and :392)
Full.lean uses all of them and compiles with only propext, Classical.choice and Quot.sound.

Reuse: the three declarations v1 reused (frt_wat_setIntegral_blowUpMap_image, frt_td_hasDensity_of_ball_mass_bounds, intcpt_canon_plane_closedBall_hausdorff) are accepted nodes under other parents. The controller rejected reuse of the first as reserved by an active node, so no cross-branch name is reused. Fresh intcpt_id_tpd_* names are used throughout, and plane_ball is restated for a Submodule. The 7 names occur nowhere except this node's rejected decomposition-v1.json. They are absent from dag.json, DAG.md, other node directories, every git ref's Submission.lean (842 refs at check time), simongmt and Mathlib.

Simon Ch. 3, Remark 1.8(2) (book/chapter-03.txt lines 298–313) is the source of the cutoff argument the children formalize.
