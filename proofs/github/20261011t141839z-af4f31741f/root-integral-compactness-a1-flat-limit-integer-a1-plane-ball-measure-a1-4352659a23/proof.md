# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1.flat_limit_integer-a1`
- Child DAG node: `root.integral_compactness-a1.flat_limit_integer-a1.plane_ball_measure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 0(c) of the supplied proof of the parent theorem intcpt_flat_limit_integer_multiplicity (T.plane is isometric to ℝ^n, on which μHE[n] is Lebesgue measure). Notation: G := Grassmannian N n (compact, Grassmannian.instCompactSpace); H^n := μHE[n]; unitBallVolume n is the extended-real volume of the open unit ball of EuclideanSpace ℝ (Fin n) and ω := (unitBallVolume n).toReal; μ_V := V.weight = V.measure.map Prod.fst; B_ρ(y) := closedBall y ρ, B°_ρ(y) := ball y ρ; v(T) := planeVarifoldMeasure T = (H^n⌞T.plane).map (y ↦ (y,T)); p_S := Grassmannian.project S = Grassmannian.projectionLinearMap S; t_P(S) := ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap S − Grassmannian.projectionLinearMap P)‖ (operator norm of p_S − p_P).
1. dim T.plane = n (Grassmannian.finrank_plane). Choose an orthonormal basis B of the subspace T.plane indexed by Fin n (stdOrthonormalBasis reindexed along finCongr of this equality) and let L := (T.plane).subtypeₗᵢ ∘ B.repr.symm : EuclideanSpace ℝ (Fin n) → ℝ^N. L is a linear isometry, L(x) ∈ T.plane for every x, and L(B.repr v) = v for every v ∈ T.plane.
2. Put ι(x) := a + L(x). Then dist(ι x, ι y) = ‖L x − L y‖ = ‖L(x − y)‖ = ‖x − y‖, so ι is an isometry.
3. For every s: ι(B_s(0)) = T.plane ∩ B_s(a) and ι(B°_s(0)) = T.plane ∩ B°_s(a). Indeed, a + L x ∈ T.plane because a ∈ T.plane, and dist(a + L x, a) = ‖L x‖ = ‖x‖; conversely, if y ∈ T.plane and dist(y,a) ≤ s (resp. < s), then y − a ∈ T.plane, x := B.repr(y − a) has ‖x‖ = ‖y − a‖ ≤ s (resp. < s), and ι x = a + (y − a) = y.
4. By Isometry.euclideanHausdorffMeasure_image, H^n(ι(S)) = μHE[n](S) for every S ⊆ ℝ^n, and μHE[n] = volume on EuclideanSpace ℝ (Fin n) (EuclideanSpace.euclideanHausdorffMeasure_eq_volume).
5. volume(B_r(0)) = ofReal(r^n)·volume(B°_1(0)) (Measure.addHaar_closedBall, r ≥ 0, finrank = n) and volume(B°_r(0)) = ofReal(r^n)·volume(B°_1(0)) (Measure.addHaar_ball_of_pos, r > 0; this form needs no nontriviality, so n = 0 is included). volume(B°_1(0)) = unitBallVolume n by definition and ofReal(r^n) = (ofReal r)^n.
6. Combining 3–5: H^n(T.plane ∩ B_r(a)) = H^n(ι(B_r(0))) = volume(B_r(0)) = unitBallVolume n·(ofReal r)^n, and likewise for the open ball.

Implementation aid (optional; not part of the proof): a kernel-checked Lean proof of this exact statement following these steps is Submission.intcpt_fli_plane_ball_measure in the git-ignored file GMT/Scratch/FLI_Decomp.lean of the gmt-ch08 workspace (copy: /tmp/fli-decomp/FullCmp.lean), if still present.

## Key steps

1. Parametrize T.plane by a linear isometry L : ℝ^n → ℝ^N built from an orthonormal basis.
2. ι(x) = a + L x is an isometry mapping B_s(0) and B°_s(0) onto T.plane ∩ B_s(a) and T.plane ∩ B°_s(a).
3. μHE[n] is isometry invariant and equals volume on ℝ^n.
4. Haar scaling of balls gives unitBallVolume n · r^n.

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
