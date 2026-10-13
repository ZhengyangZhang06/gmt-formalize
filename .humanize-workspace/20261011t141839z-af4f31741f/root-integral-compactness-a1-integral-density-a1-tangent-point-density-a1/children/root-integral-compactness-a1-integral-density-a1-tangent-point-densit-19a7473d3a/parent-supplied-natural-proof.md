# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1.integral_density-a1.tangent_point_density-a1`
- Child DAG node: `root.integral_compactness-a1.integral_density-a1.tangent_point_density-a1.ball_mass_lower-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2–5 of the selected proof (Simon Ch. 3, Remark 1.8(2)), lower half: the inner cutoff f₁ (1_{B̄_κ} ≤ f₁ ≤ 1_{B̄_1}) and the liminf bound, written for a single c. Notation: H^n := μHE[n]; B̄_s(z) := closedBall z s; ν := (H^n⌞M).withDensity(ofReal ∘ θ); ω̂ := unitBallVolume n; ω := ω̂.toReal; η_t := Chapter03.blowUpMap x t; and, for f ∈ C_c(ℝ^N, ℝ), I_f(t) := ∫_{η_t(M)} f(y) θ(x + t•y) dH^n(y). The hypothesis HWATS gives finrank P = n (first component) and, for each f, I_f(t) → θ(x) ∫_P f dH^n along 𝓝[>] 0 (second component).

0. 0 < ω̂ < ∞. ω̂ is the volume of the open unit ball of EuclideanSpace ℝ (Fin n). Volume is an additive Haar measure, hence positive on the nonempty open ball (measure_ball_pos volume 0 one_pos), and the ball is bounded in a proper space (measure_ball_lt_top). Hence ω = ω̂.toReal > 0 (ENNReal.toReal_pos) and ω̂ = ofReal ω. (For n = 0 the space is a point and ω̂ = 1.)

1. Fix c with c < ofReal(θ(x)) · ω̂.
 - θ(x) > 0: otherwise ofReal(θ(x)) = 0 (ENNReal.ofReal_of_nonpos), the right side is 0, and c < 0 is impossible in [0, ∞] (ENNReal.not_lt_zero).
 - So ofReal(θ(x)) · ω̂ = ofReal(θ(x)·ω) (ENNReal.ofReal_mul, ENNReal.ofReal_toReal). In particular c < ∞.
 - Put c' := c.toReal ≥ 0, so c = ofReal(c'). Then c' < θ(x)·ω (ENNReal.ofReal_lt_ofReal_iff, as θ(x)·ω > 0).

2. Choice of κ. The map κ ↦ θ(x)·ω·κ^n is continuous at κ = 1 with value θ(x)·ω > c'. So eventually along 𝓝[<] 1 it exceeds c' (Filter.Tendsto.eventually_const_lt). Also Ioo 0 1 ∈ 𝓝[<] 1 (Ioo_mem_nhdsLT). The filter 𝓝[<] 1 on ℝ is non-trivial (1 is a limit of points below it), so the intersection of these two eventual sets is nonempty (Filter.Eventually.and, Filter.Eventually.exists). Pick κ in it: 0 < κ < 1 and c' < θ(x)·ω·κ^n. (For n = 0 any κ ∈ (0,1) works.)

3. Inner cutoff. Apply the sibling plane_cutoff (Submission.intcpt_id_tpd_plane_cutoff) to P with (a, R) := (κ, 1), using finrank P = n and 0 < κ < 1. It gives f ∈ C_c(ℝ^N, ℝ) with: 0 ≤ f ≤ 1; f(y) = 1 for ‖y‖ ≤ κ; f(y) = 0 for ‖y‖ > 1; and ω·κ^n ≤ ∫_P f dH^n.

4. Limit. By HWATS applied to f, I_f(t) → θ(x)·∫_P f dH^n as t ↓ 0. Moreover
 c' < θ(x)·ω·κ^n = θ(x)·(ω·κ^n) ≤ θ(x)·∫_P f dH^n (θ(x) > 0, step 3).
 Hence ∀ᶠ t in 𝓝[>] 0, c' < I_f(t) (Filter.Tendsto.eventually_const_lt).

5. Sandwich. Also ∀ᶠ t in 𝓝[>] 0, t ∈ (0, r₀] (Ioc_mem_nhdsGT, r₀ > 0). Fix t in both eventual sets. Apply the sibling ball_sandwich (Submission.intcpt_id_tpd_ball_sandwich) with (f, r₀, a, R, r) := (f, r₀, κ, 1, t). Its hypotheses are: M null-measurable, θ ≥ 0 on M, integrability on M ∩ B̄_{r₀}(x), the four pointwise properties of f, t > 0, and t·1 ≤ r₀. Its right inequality gives ofReal(t^n · I_f(t)) ≤ ν(B̄_{t·1}(x)) = ν(B̄_t(x)).

6. Conclusion. For such t:
 c · ofReal(t)^n = ofReal(c') · ofReal(t^n) = ofReal(t^n · c') (ENNReal.ofReal_pow with t ≥ 0, ENNReal.ofReal_mul with c' ≥ 0, mul_comm)
 ≤ ofReal(t^n · I_f(t)) (ENNReal.ofReal_le_ofReal, since t^n ≥ 0 and c' < I_f(t))
 ≤ ν(B̄_t(x)) (step 5).
 This holds for all t in a set belonging to 𝓝[>] 0, which is the claim. ∎

## Key steps

1. 0 < ω̂ < ∞; c < ofReal(θ x)·ω̂ forces θ(x) > 0 and c = ofReal(c') with c' < θ(x)ω.
2. Choose κ ∈ (0,1) with c' < θ(x)ωκ^n (continuity of κ^n at 1).
3. Sibling plane_cutoff with (a,R) = (κ,1): f ∈ C_c, 1_{B̄_κ} ≤ f ≤ 1_{B̄_1}, ωκ^n ≤ ∫_P f.
4. HWATS: I_f(t) → θ(x)∫_P f > c', so eventually c' < I_f(t).
5. For 0 < t ≤ r₀, sibling ball_sandwich gives ofReal(t^n I_f(t)) ≤ ν(B̄_t(x)); hence c·ofReal(t)^n = ofReal(t^n c') ≤ ν(B̄_t(x)).

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
