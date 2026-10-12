# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1.flat_limit_integer-a1`
- Child DAG node: `root.integral_compactness-a1.flat_limit_integer-a1.canonical_domination-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 of the supplied proof of the parent theorem intcpt_flat_limit_integer_multiplicity (canonical form of W via integral_density and canonical_representation; Z is μ-null hence H^n-null; μ⌞B ≤ (H^n⌞(M̃ ∩ B)).withDensity(ofReal θ̃)). Notation: G := Grassmannian N n (compact, Grassmannian.instCompactSpace); H^n := μHE[n]; unitBallVolume n is the extended-real volume of the open unit ball of EuclideanSpace ℝ (Fin n) and ω := (unitBallVolume n).toReal; μ_V := V.weight = V.measure.map Prod.fst; B_ρ(y) := closedBall y ρ, B°_ρ(y) := ball y ρ; v(T) := planeVarifoldMeasure T = (H^n⌞T.plane).map (y ↦ (y,T)); p_S := Grassmannian.project S = Grassmannian.projectionLinearMap S; t_P(S) := ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap S − Grassmannian.projectionLinearMap P)‖ (operator norm of p_S − p_P).
1. By (hD) for W, μ_W-a.e. x has HasDensity n μ_W x k with k ∈ ℕ, k ≥ 1; then (k : [0,∞]) > 0, so the density hypothesis of (hC) holds for W.
2. (hC) for W gives θ with IsVarifoldOf W M θ, the tangent-plane and density property at every x ∈ M, and the null transfer property. These are the first two conclusions.
3. Let Z := {x ∈ M : ¬∃ m ∈ ℕ, m ≥ 1 ∧ θ(x) = m}. Then μ_W(Z) = 0: by 1, for μ_W-a.e. x there is k ≥ 1 with HasDensity n μ_W x k; if such an x lay in Z, then x ∈ M gives also HasDensity n μ_W x (ofReal θ(x)); limits along the non-trivial filter 𝓝[>]0 in the Hausdorff space [0,∞] are unique (tendsto_nhds_unique), so ofReal θ(x) = k; θ(x) > 0 by IsVarifoldOf, so θ(x) = toReal(ofReal θ(x)) = k, contradicting x ∈ Z. Thus μ_W-a.e. x ∉ Z (measure_eq_zero_iff_ae_notMem). As Z ⊆ M, the null transfer property of 2 gives H^n(Z) = 0.
4. Domination. Fix K compact ⊆ U and u Borel, u = 0 off K. By IsVarifoldOf, θ is H^n-integrable on M ∩ K, so ofReal ∘ θ is a.e.-measurable for H^n⌞(M ∩ K). Let ν := (H^n⌞(M ∩ K)).withDensity(ofReal ∘ θ).
5. μ_W⌞K ≤ ν. For Borel B: μ_W⌞K(B) = μ_W(B ∩ K) = W.measure((B ∩ K) × G) (Varifold.weight_apply; K is closed). By IsVarifoldOf with the Borel set A := (B ∩ K) × G this equals ∫⁻ over {x ∈ M : ∃ S, (weighted approximate tangent at x) ∧ (x,S) ∈ A} of ofReal θ dH^n; that set is contained in B ∩ (M ∩ K), so (lintegral_mono_set) μ_W⌞K(B) ≤ ∫⁻_{B ∩ (M ∩ K)} ofReal θ dH^n = ν(B) (Measure.restrict_restrict, withDensity_apply). Measure.le_iff gives μ_W⌞K ≤ ν.
6. Since support u ⊆ K, ∫⁻ u dμ_W = ∫⁻_K u dμ_W (setLIntegral_eq_of_support_subset) ≤ ∫⁻ u dν (lintegral_mono' with the measure inequality) = ∫⁻_{M ∩ K} ofReal(θ)·u dH^n (lintegral_withDensity_eq_lintegral_mul₀; ofReal ∘ θ is a.e.-measurable and u is measurable) = ∫⁻_{M ∩ K} u·ofReal(θ) dH^n.

Implementation aid (optional; not part of the proof): a kernel-checked Lean proof of this exact statement following these steps is Submission.intcpt_fli_integral_canonical_domination in the git-ignored file GMT/Scratch/FLI_Decomp.lean of the gmt-ch08 workspace (copy: /tmp/fli-decomp/FullCmp.lean), if still present.

## Key steps

1. (hD) gives positive integer densities μ_W-a.e., so (hC) applies and yields θ, M and the tangent/density/null-transfer properties.
2. Points of M where θ is not a positive integer form a μ_W-null set (uniqueness of density limits), hence an H^n-null set.
3. IsVarifoldOf gives μ_W⌞K ≤ (H^n⌞(M ∩ K)).withDensity(ofReal θ) on Borel sets.
4. Integrate a Borel u vanishing off K against this inequality and expand the withDensity integral.

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
