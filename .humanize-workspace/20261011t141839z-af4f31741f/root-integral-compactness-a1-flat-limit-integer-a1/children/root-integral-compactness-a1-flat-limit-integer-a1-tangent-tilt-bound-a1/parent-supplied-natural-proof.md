# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1.flat_limit_integer-a1`
- Child DAG node: `root.integral_compactness-a1.flat_limit_integer-a1.tangent_tilt_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 7 of the supplied proof of the parent theorem intcpt_flat_limit_integer_multiplicity ("for κ ∈ (0,1) let χ_κ ... letting ρ ↓ 0 ... letting κ ↑ 1 ..."). Notation: G := Grassmannian N n (compact, Grassmannian.instCompactSpace); H^n := μHE[n]; unitBallVolume n is the extended-real volume of the open unit ball of EuclideanSpace ℝ (Fin n) and ω := (unitBallVolume n).toReal; μ_V := V.weight = V.measure.map Prod.fst; B_ρ(y) := closedBall y ρ, B°_ρ(y) := ball y ρ; v(T) := planeVarifoldMeasure T = (H^n⌞T.plane).map (y ↦ (y,T)); p_S := Grassmannian.project S = Grassmannian.projectionLinearMap S; t_P(S) := ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap S − Grassmannian.projectionLinearMap P)‖ (operator norm of p_S − p_P).
1. ω ∈ (0,∞) (positive finite volume of the unit ball of ℝ^n). Write t(S) := t_P(S) ≥ 0.
2. Claim: t(T)·ω·κ^n ≤ ε for every κ ∈ (0,1). Fix κ.
  2a. χ_κ(z) := max(0, min(1, (1 − |z|)/(1 − κ))) is continuous, [0,1]-valued, = 1 for |z| ≤ κ, = 0 for |z| ≥ 1; so it has compact support (⊆ B_1(0)). The sibling tilt_cutoff gives f ∈ C_c(ℝ^N × G) with f(z,S) = χ_κ(z)t(S).
  2b. Fix ρ ∈ (0,1). rescaledMeasure W y ρ = ofReal(ρ^{-n}) • W.measure.map (z ↦ (ρ^{-1}(z.1 − y), z.2)), so by integral_smul_measure and integral_map, ∫ f d(rescaledMeasure W y ρ) = ρ^{-n} ∫ h dW with h(z) := f(ρ^{-1}(z.1 − y), z.2) = χ_κ(ρ^{-1}(z.1 − y))·t(z.2), a continuous function with h ≥ 0.
  2c. ofReal(h(z)) ≤ 1_{B_ρ(y)×G}(z)·ofReal(t(z.2)) for all z: if z.1 ∈ B_ρ(y) use χ_κ ≤ 1; otherwise |z.1 − y| > ρ, so |ρ^{-1}(z.1 − y)| > 1 and χ_κ(ρ^{-1}(z.1 − y)) = 0.
  2d. Hence ∫⁻ ofReal(h) dW ≤ ∫⁻_{B_ρ(y)×G} ofReal(t) dW ≤ ofReal(ερ^n) (lintegral_indicator and the hypothesis). As h ≥ 0 is continuous, ∫ h dW = (∫⁻ ofReal(h) dW).toReal ≤ ερ^n (integral_eq_lintegral_of_nonneg_ae, ENNReal.toReal_le_of_le_ofReal). So ∫ f d(rescaledMeasure W y ρ) ≤ ρ^{-n}·ερ^n = ε.
  2e. By HasTangentPlane W y T θ (applied to f), ∫ f d(rescaledMeasure W y ρ) → θ ∫ f dv(T) as ρ ↓ 0; the values are ≤ ε for ρ ∈ (0,1), a set in 𝓝[>]0, so θ ∫ f dv(T) ≤ ε (le_of_tendsto).
  2f. By integral_map along z ↦ (z,T) and integral_mul_const, ∫ f dv(T) = t(T)·J with J := ∫_{T.plane} χ_κ dH^n ≥ 0.
  2g. J ≥ ωκ^n: χ_κ ≥ 1_{B_κ(0)}; χ_κ is integrable on T.plane since χ_κ ≤ 1_{B_1(0)} and H^n(T.plane ∩ B_1(0)) = unitBallVolume n < ∞ (sibling plane_ball_measure with a = 0); and ∫_{T.plane} 1_{B_κ(0)} dH^n = H^n(T.plane ∩ B_κ(0)).toReal = ωκ^n (plane_ball_measure with a = 0, r = κ).
  2h. Since t(T) ≥ 0, J ≥ 0 and θ ≥ 1: t(T)ωκ^n ≤ t(T)J ≤ θ·t(T)J ≤ ε.
3. The map κ ↦ t(T)ωκ^n is continuous with value t(T)ω at κ = 1; letting κ ↑ 1 in 2 (le_of_tendsto along 𝓝[<]1, where κ ∈ (0,1) eventually) gives t(T)ω ≤ ε, i.e. t(T) ≤ ε/ω.
4. p_T v − p_P v = toContinuousLinearMap(projectionLinearMap T − projectionLinearMap P) v (definition of Grassmannian.project), so |p_T v − p_P v| ≤ t(T)|v| ≤ (ε/ω)|v| (ContinuousLinearMap.le_opNorm).

Implementation aid (optional; not part of the proof): a kernel-checked Lean proof of this exact statement following these steps is Submission.intcpt_fli_tangent_tilt_bound in the git-ignored file GMT/Scratch/FLI_Decomp.lean of the gmt-ch08 workspace (copy: /tmp/fli-decomp/FullCmp.lean), if still present.

## Key steps

1. For κ ∈ (0,1) build f = χ_κ(z)t_P(S) ∈ C_c with χ_κ = 1 on B_κ(0), 0 off B°_1(0).
2. Rescaling: ∫ f d(W_{y,ρ}) = ρ^{-n}∫χ_κ(ρ^{-1}(z−y))t_P dW ≤ ρ^{-n}·ερ^n = ε for ρ ∈ (0,1).
3. Tangent-plane limit: θ·t_P(T)·∫_{T.plane}χ_κ dH^n ≤ ε, and ∫_{T.plane}χ_κ ≥ ωκ^n.
4. θ ≥ 1 and κ ↑ 1 give t_P(T) ≤ ε/ω; the operator-norm bound gives the claim.

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
