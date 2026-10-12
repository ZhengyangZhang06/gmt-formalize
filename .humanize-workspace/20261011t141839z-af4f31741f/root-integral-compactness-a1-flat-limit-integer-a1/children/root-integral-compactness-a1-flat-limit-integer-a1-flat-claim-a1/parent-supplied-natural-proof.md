# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1.flat_limit_integer-a1`
- Child DAG node: `root.integral_compactness-a1.flat_limit_integer-a1.flat_claim-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2, 3, 4, 10 (choice of test function) and 11 of the supplied proof of the parent theorem intcpt_flat_limit_integer_multiplicity: the claim of its step 3, proved here for every k₀ ∈ ℕ satisfying the displayed inequality (that proof uses k₀ = ⌊θ₀⌋). Notation: G := Grassmannian N n (compact, Grassmannian.instCompactSpace); H^n := μHE[n]; unitBallVolume n is the extended-real volume of the open unit ball of EuclideanSpace ℝ (Fin n) and ω := (unitBallVolume n).toReal; μ_V := V.weight = V.measure.map Prod.fst; B_ρ(y) := closedBall y ρ, B°_ρ(y) := ball y ρ; v(T) := planeVarifoldMeasure T = (H^n⌞T.plane).map (y ↦ (y,T)); p_S := Grassmannian.project S = Grassmannian.projectionLinearMap S; t_P(S) := ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap S − Grassmannian.projectionLinearMap P)‖ (operator norm of p_S − p_P). (H) denotes the hypothesis ∫ f dW_k → θ₀ ∫ f dv(P) for every f ∈ C_c(ℝ^N × G, ℝ) with tsupport f ⊆ B°_5(0) × G.
1. ω ∈ (0,∞) and unitBallVolume n = ofReal ω. Put Λ := θ₀ω3^n + 1 ≥ 1. The sibling good_mass_estimate (with (hA), (hD), (hC), (hG), (TGC), N, n, Λ; 1 ≤ n, 1 ≤ Λ) gives δ̄₁ > 0, c₀ ≥ 0 with its property (★). Put δ̄ := min(δ̄₁, 1) > 0.
2. ψ(a) := max(0, min(1, 2 − 4|a|)) is continuous, [0,1]-valued, = 1 for |a| ≤ 1/4 and = 0 for |a| ≥ 1/2. P.plane is closed (finite-dimensional subspace), hence Borel, and 0 ∈ P.plane. By the sibling plane_ball_measure (a = 0), H^n(P.plane ∩ B_r(0)) = unitBallVolume n·(ofReal r)^n < ∞ for r > 0. Since 0 ≤ ψ ≤ 1_{B_{1/2}(0)}, ψ is H^n-integrable on P.plane; put I₀ := ∫_{P.plane} ψ dH^n. Since ψ ≥ 1_{B_{1/4}(0)}, I₀ ≥ H^n(P.plane ∩ B_{1/4}(0)).toReal = ω4^{-n} > 0.
3. Fix δ ∈ (0,δ̄] and k₀ ∈ ℕ with (1+δ)(θ₀+δ) + δ < k₀ + 1 and 4δ⁴ ≤ ω. Put ε := δ⁴, m := θ₀ + δ. Then 0 < ε ≤ δ⁴, ε ≤ 1 (δ ≤ 1), 4ε ≤ ω, δ ≤ δ̄₁, m ≥ 0 and (1+δ)m + δ < k₀ + 1.
4. Test function. χ(t) := max(0, min(1, 2 − 2t/ε)) is continuous, [0,1]-valued, χ(0) = 1 and χ(t) = 0 for t ≥ ε. With p := p_P (continuous linear) let g₀(y) := ψ(p y)·χ(|y − p y|). Then g₀ is continuous, 0 ≤ g₀ ≤ ψ(p y) ≤ 1; g₀(y) ≠ 0 implies |p y| < 1/2 and |y − p y| < ε, hence |y| ≤ |p y| + |y − p y| < 2, so tsupport g₀ ⊆ B_2(0) (closed), g₀ has compact support and tsupport g₀ ⊆ B°_5(0). For a ∈ P.plane, p a = a (projectionLinearMap_apply_of_mem), so g₀(a) = ψ(a)χ(0) = ψ(a).
5. By the sibling weight_tendsto, ∫ g₀ dμ_{W_k} → θ₀∫_{P.plane} g₀ dH^n = θ₀I₀ (setIntegral_congr_fun on the Borel set P.plane, using 4).
6. Hypotheses of (★) for all large k:
  (i) choose η ∈ (0,1) with θ₀ω(3+η)^n < Λ (continuity at η = 0, value θ₀ω3^n < Λ). K := B_3(0) is compact, O := B°_{3+η}(0) is open, K ⊆ O ⊆ B°_5(0), and θ₀·H^n(P.plane ∩ O) = ofReal(θ₀ω(3+η)^n) < ofReal Λ (plane_ball_measure). The sibling compact_mass_eventually gives eventually μ_k(B_3(0)) < ofReal Λ, hence μ_k(B°_3(0)) ≤ ofReal Λ;
  (ii) ‖δW_k‖(B°_5(0)) → 0 < ofReal(ε²), so eventually ‖δW_k‖(B°_3(0)) ≤ ‖δW_k‖(B°_5(0)) < ofReal(ε²);
  (iii) the sibling tilt_excess_eventually with η := ε² gives eventually ∫⁻_{B°_3(0)×G} t_P dW_k < ofReal(ε²);
  (iv) the sibling unit_disc_mass with η := δ gives eventually μ_k(B_1(a)) ≤ ofReal((θ₀+δ)ω) = ofReal(mω) for all a ∈ P.plane with |a| ≤ 1, in particular for |a| < 1.
7. For every k satisfying (i)–(iv), apply (★) with δ, ε, m, k₀, U := B°_5(0) ⊇ B°_3(0), W := W_k (integral, locally bounded first variation), P, g := ofReal ∘ g₀ (Borel, ≤ 1, ≤ (ofReal ∘ ψ) ∘ p, and g(y) ≠ 0 ⇒ g₀(y) ≠ 0 ⇒ |p y| < 1/2 < 1, |y − p y| < ε) and φ := ofReal ∘ ψ: ∫⁻ ofReal(g₀) dμ_k ≤ ofReal(c₀ε) + ofReal(Q)·k₀·∫⁻_{P.plane} ofReal ψ dH^n with Q := (1 + (4ε/ω)²)^{n/2} ≥ 0. Here ∫⁻_{P.plane} ofReal ψ dH^n = ofReal I₀ (ofReal_integral_eq_lintegral_ofReal), so the right side is ofReal(c₀ε + Qk₀I₀). As g₀ ≥ 0 is continuous, ∫ g₀ dμ_k = (∫⁻ ofReal(g₀) dμ_k).toReal ≤ c₀ε + Qk₀I₀ (integral_eq_lintegral_of_nonneg_ae, ENNReal.toReal_le_of_le_ofReal).
8. By 5 and 7 (le_of_tendsto), θ₀I₀ ≤ c₀ε + Qk₀I₀ = c₀δ⁴ + (1 + (4δ⁴/ω)²)^{n/2}k₀I₀.

Implementation aid (optional; not part of the proof): a kernel-checked Lean proof of this exact statement following these steps is Submission.intcpt_fli_flat_claim in the git-ignored file GMT/Scratch/FLI_Decomp.lean of the gmt-ch08 workspace (copy: /tmp/fli-decomp/FullCmp.lean), if still present.

## Key steps

1. Λ := θ₀ω3^n + 1; constants δ̄₁, c₀ from good_mass_estimate; δ̄ := min(δ̄₁, 1).
2. Profile ψ with I₀ = ∫_{P.plane}ψ dH^n ≥ ω4^{-n} > 0 (plane_ball_measure).
3. Test function g₀(y) = ψ(p_P y)χ(|y − p_P y|), continuous with compact support in B°_5(0), equal to ψ on P.plane.
4. Eventually in k: mass on B°_3 ≤ Λ (compact_mass_eventually), ‖δW_k‖ small, tilt excess small (tilt_excess_eventually), unit-disc masses ≤ ofReal((θ₀+δ)ω) (unit_disc_mass).
5. good_mass_estimate: ∫ g₀ dμ_k ≤ c₀δ⁴ + (1+(4δ⁴/ω)²)^{n/2}k₀I₀ eventually; weight_tendsto: ∫ g₀ dμ_k → θ₀I₀.

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
