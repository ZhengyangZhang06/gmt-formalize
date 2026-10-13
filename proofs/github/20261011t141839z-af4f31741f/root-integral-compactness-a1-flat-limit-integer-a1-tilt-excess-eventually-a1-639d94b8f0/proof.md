# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1.flat_limit_integer-a1`
- Child DAG node: `root.integral_compactness-a1.flat_limit_integer-a1.tilt_excess_eventually-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4(iii) of the supplied proof of the parent theorem intcpt_flat_limit_integer_multiplicity (test (H) with χ(|z|)t_P(S), where t_P(P) = 0). Notation: G := Grassmannian N n (compact, Grassmannian.instCompactSpace); H^n := μHE[n]; unitBallVolume n is the extended-real volume of the open unit ball of EuclideanSpace ℝ (Fin n) and ω := (unitBallVolume n).toReal; μ_V := V.weight = V.measure.map Prod.fst; B_ρ(y) := closedBall y ρ, B°_ρ(y) := ball y ρ; v(T) := planeVarifoldMeasure T = (H^n⌞T.plane).map (y ↦ (y,T)); p_S := Grassmannian.project S = Grassmannian.projectionLinearMap S; t_P(S) := ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap S − Grassmannian.projectionLinearMap P)‖ (operator norm of p_S − p_P). (H) denotes the hypothesis ∫ f dW_k → θ₀ ∫ f dv(P) for every f ∈ C_c(ℝ^N × G, ℝ) with tsupport f ⊆ B°_5(0) × G.
1. χ(z) := max(0, min(1, 4 − |z|)) is continuous with values in [0,1], χ = 1 on |z| ≤ 3, χ = 0 on |z| ≥ 4; hence tsupport χ ⊆ B_4(0) and χ has compact support.
2. The sibling tilt_cutoff gives f ∈ C_c(ℝ^N × G) with f(z,S) = χ(z)t_P(S) and tsupport f ⊆ tsupport χ × G ⊆ B_4(0) × G ⊆ B°_5(0) × G.
3. By (H), ∫ f dW_k → θ₀ ∫ f dv(P). By integral_map along y ↦ (y,P), ∫ f dv(P) = ∫_{P.plane} χ(y)t_P(P) dH^n = 0, because t_P(P) = ‖toContinuousLinearMap(projectionLinearMap P − projectionLinearMap P)‖ = ‖0‖ = 0. Hence ∫ f dW_k → 0, ofReal(∫ f dW_k) → ofReal 0 = 0, and since ofReal η > 0, ofReal(∫ f dW_k) < ofReal η for all large k.
4. For each k: f ≥ 0; f is bounded (a continuous function with compact support has bounded range, Continuous.bddAbove_range_of_hasCompactSupport applied to ‖f‖) and vanishes off B_4(0) × G, and W_k(B_4(0) × G) < ∞ (Varifold.finite_on_compact: B_4(0) is a compact subset of B°_5(0)); so f is W_k-integrable (Measure.integrableOn_of_bounded, integrableOn_iff_integrable_of_support_subset) and ofReal(∫ f dW_k) = ∫⁻ ofReal(f) dW_k (ofReal_integral_eq_lintegral_ofReal).
5. On B°_3(0) × G we have χ(z) = 1, so ofReal(t_P(S)) = ofReal(f(z,S)) there; therefore ∫⁻_{B°_3(0)×G} ofReal(t_P) dW_k = ∫⁻_{B°_3(0)×G} ofReal(f) dW_k ≤ ∫⁻ ofReal(f) dW_k = ofReal(∫ f dW_k) (setLIntegral_congr_fun, setLIntegral_le_lintegral).
6. By 3 and 5, the tilt excess is < ofReal η for all large k.

Implementation aid (optional; not part of the proof): a kernel-checked Lean proof of this exact statement following these steps is Submission.intcpt_fli_tilt_excess_eventually in the git-ignored file GMT/Scratch/FLI_Decomp.lean of the gmt-ch08 workspace (copy: /tmp/fli-decomp/FullCmp.lean), if still present.

## Key steps

1. Cutoff χ = 1 on B_3(0), 0 off B°_4(0); tilt_cutoff gives f = χ(z)t_P(S) ∈ C_c with support in B°_5(0) × G.
2. (H) and t_P(P) = 0 give ∫ f dW_k → 0.
3. f is W_k-integrable, and the tilt excess over B°_3(0) × G is ≤ ofReal(∫ f dW_k).

## Reference use

### local-project

Queries:
- `cat local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum snapshot project/GMT/Ch08/Contract.lean, workspace GMT/Ch08/Contract.lean, GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `rg -n -F in snapshot mathlib/Mathlib: exists_continuousMap_one_of_isCompact_subset_isOpen, addHaar_closedBall, addHaar_ball_of_pos, Isometry.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, euclideanHausdorffMeasure_zero, hausdorffMeasure_zero_singleton, lintegral_countable, finite_const_le_of_tsum_ne_top, isClosedEmbedding_coe_real, finite_cover_balls_of_compact, eventually_all_finite, Infinite.exists_subset_card_eq, lintegral_withDensity_eq_lintegral_mul₀, setLIntegral_eq_of_support_subset, integral_map, integral_smul_measure, measure_eq_zero_iff_ae_notMem, lintegral_indicator₀, integrableOn_of_bounded, integrableOn_iff_integrable_of_support_subset, le_opNorm, LinearMap.continuous_of_finiteDimensional, integral_singleton, ofReal_integral_eq_lintegral_ofReal, integral_eq_lintegral_of_nonneg_ae, lintegral_add_compl, measure_toMeasurable, tsum_eq_sum, setLIntegral_mono', lintegral_mul_const', ae_restrict_mem₀, integral_indicator_one, integral_mono_of_nonneg, bddAbove_range_of_hasCompactSupport`
- `rg -n 'theorem finrank_plane|theorem projectionLinearMap_apply_of_mem|theorem weight_apply|theorem weight_finite_on_compact|finite_on_compact :|instCompactSpace' simongmt Chapter08/Varifold.lean; grep -n 'def CountablyRectifiable|def HasWeightedApproximateTangentSpaceAt' simongmt Chapter03/Rectifiable.lean`
- `python3 scans of dag.json: lean_name collisions for intcpt_fli_* (none), cross-branch depends_on (none), reused-node children (2 cases, both used only by their parent); exact frozen types of intcpt_allard_integrality_lemma, intcpt_integral_density_integer, intcpt_canonical_tangent_representation, intcpt_lipschitz_graph_fibre_bound`
- `git log/show of implementation bases 2c2e689, cc4ec2c, 1d5fcdf, 9d1b76a, b951e87 (child bases start from bare dispatch commits; reuse of frt_weight_blowup_tendsto happened only via an explicit reused child)`
- `python3 -I verifier/lean_contract.validate_lean_statement on all 11 lean_statements; verifier/gmt-compare.py contract_scope(Contract.lean, GMT.Ch08.main_theorem) replay`
- `lake env lean /tmp/fli-decomp/{Stmts,Parent,Claim,Core,Canon,Tilt,Small,C3,C1,Full,FullCmp}.lean (statements, parent assembly, each child proof, end-to-end file, comparator-form targets; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/UrysohnsLemma.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Order/Filter/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Data/Set/Finite/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/VectorMeasure/SetIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/VarifoldConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-flat-limit-integer-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-tangent-plane-dilation-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1/rlcr-plan-v1.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Scratch/FLI_Decomp.lean`

Snapshot = project 63436ae6 + Mathlib 25730c7c; its Contract is byte-identical to the workspace Contract and Submission. Every Mathlib and SimonGMT declaration cited in the 11 child proofs exists in the pinned snapshot / package (several as `lemma`), with the hypotheses used. No existing accepted declaration has the type of any child, so all 11 lean_names (intcpt_fli_*) are fresh and unreserved. Child implementation bases do not contain the parent's dependency declarations, so those four frozen types and the TGC statement are passed as explicit hypotheses. All 11 statements elaborate in the exact comparator form and pass validate_lean_statement. Complete kernel-checked proofs of all 11 children use only propext, Classical.choice and Quot.sound. The frozen parent statement type-checks from the children and the four pre-existing sibling declarations, with no unproved step of its own.
