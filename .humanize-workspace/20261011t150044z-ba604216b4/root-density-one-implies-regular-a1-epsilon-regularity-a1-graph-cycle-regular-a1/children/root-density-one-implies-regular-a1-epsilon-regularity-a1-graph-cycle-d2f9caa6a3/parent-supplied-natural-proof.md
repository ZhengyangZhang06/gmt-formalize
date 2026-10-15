# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.smooth_to_c1_tests-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 14 of the parent proof ("extend the identity to C¹ compactly supported a by mollifying a (∂ⱼ(a ∗ ϱ_t) = (∂ⱼa) ∗ ϱ_t → ∂ⱼa uniformly, with supports in a fixed compact subset of D, while G is integrable there)"). The parent then applies Poincare.SimonGMT.Chapter08.ae_eq_const_of_weak_coordinate_derivatives_zero, whose hypothesis is exactly the conclusion of this lemma (Chapter08's Euclidean n is the same type EuclideanSpace ℝ (Fin n) as Euclid n); that library module is outside the frozen import closure, so its application stays in the parent.
Notation: ℝⁿ means Euclid n = EuclideanSpace ℝ (Fin n) with Lebesgue measure volume; eᵢ := EuclideanSpace.basisFun (Fin n) ℝ i = EuclideanSpace.single i 1 (EuclideanSpace.basisFun_apply); ∂ᵢf(x) := Df(x)eᵢ = fderiv ℝ f x eᵢ; convolution is Mathlib's (ϱ ⋆ f)(x) = ∫ ϱ(t)·f(x − t) dt (convolution with lsmul ℝ ℝ and volume).
Formalization note: unless this child is split further it is a machine leaf (one theorem appended to the frozen GMT/Ch07/Submission.lean, no new import or helper declaration). Mathlib's normalized-bump API (ContDiffBump.normed, BumpFunction.Convolution) is NOT in the frozen import closure, so the mollifier is normalized by hand below; all lemmas cited are in the import closure of GMT.Ch07.Submission.
1. Fix φ : ℝⁿ → ℝ of class C¹ with compact support and tsupport φ ⊆ D, and fix i. (If n = 0 there is no index i; assume n ≥ 1.) K := tsupport φ is compact and K ⊆ D; choose δ > 0 with K_δ := cthickening δ K ⊆ D (IsCompact.exists_cthickening_subset_open); K_δ is compact (IsCompact.cthickening). G is integrable on K_δ (LocallyIntegrableOn.integrableOn_compact_subset with K_δ ⊆ D).
2. Mollifiers. For r > 0 let B_r be a ContDiffBump centred at 0 ∈ ℝⁿ with rIn = r/2 and rOut = r; as a function ℝⁿ → ℝ it is smooth (ContDiffBump.contDiff), 0 ≤ B_r ≤ 1, B_r = 1 on B̄_{r/2}(0), and support B_r = B_r(0) (ContDiffBump.support_eq), so it is continuous with compact support and integrable (Continuous.integrable_of_hasCompactSupport). I_r := ∫ B_r > 0 by integral_pos_iff_support_of_nonneg, since B_r ≥ 0 and its support, the open ball B_r(0), has positive Lebesgue measure (Metric.measure_ball_pos). Put ϱ_r := I_r⁻¹·B_r. Then ϱ_r is smooth with compact support, ϱ_r ≥ 0, ∫ϱ_r = 1 (integral_smul / integral_const_mul), and support ϱ_r ⊆ B_r(0).
3. For ℓ ∈ ℕ put r_ℓ := δ/(ℓ+1) and φ_ℓ := ϱ_{r_ℓ} ⋆ φ.
 (a) φ_ℓ is smooth: HasCompactSupport.contDiff_convolution_left (ϱ_{r_ℓ} smooth with compact support, φ continuous hence locally integrable), with order (⊤ : ℕ∞).
 (b) support φ_ℓ ⊆ support ϱ_{r_ℓ} + support φ ⊆ B_{r_ℓ}(0) + K (MeasureTheory.support_convolution_subset) ⊆ thickening r_ℓ K ⊆ cthickening δ K = K_δ, a closed set; hence tsupport φ_ℓ ⊆ K_δ ⊆ D and φ_ℓ has compact support (closed subset of the compact K_δ; HasCompactSupport.intro).
 (c) Dφ_ℓ = ϱ_{r_ℓ} ⋆ Dφ (HasCompactSupport.hasFDerivAt_convolution_right with φ ∈ C¹ of compact support and ϱ_{r_ℓ} locally integrable; the convolution is taken with the precomposed bilinear map), and evaluating at eᵢ (MeasureTheory.convolution_precompR_apply) gives ∂ᵢφ_ℓ(x) = (ϱ_{r_ℓ} ⋆ ∂ᵢφ)(x) for every x.
 (d) Uniform convergence. ∂ᵢφ is continuous (ContDiff.continuous_fderiv with one_ne_zero) with compact support (support ⊆ tsupport φ, HasCompactSupport.fderiv), hence uniformly continuous (HasCompactSupport.uniformContinuous_of_continuous). Given ε > 0 choose r₀ > 0 with |∂ᵢφ(x') − ∂ᵢφ(x)| ≤ ε whenever ‖x' − x‖ < r₀. For ℓ with r_ℓ ≤ r₀ and every x, MeasureTheory.dist_convolution_le (kernel ϱ_{r_ℓ} ≥ 0 pointwise with ∫ϱ_{r_ℓ} = 1 and support in B_{r_ℓ}(0); ∂ᵢφ is AE-strongly measurable; |∂ᵢφ(x') − ∂ᵢφ(x)| ≤ ε for x' ∈ B_{r_ℓ}(x)) gives |∂ᵢφ_ℓ(x) − ∂ᵢφ(x)| ≤ ε for every x.
4. By hypothesis, applied to a := φ_ℓ (smooth, compact support, tsupport ⊆ D) and j := i: ∫_D G·∂ᵢφ_ℓ = 0 for every ℓ.
5. Both ∂ᵢφ and ∂ᵢφ_ℓ vanish outside K_δ (fderiv vanishes outside the topological support, fderiv_of_notMem_tsupport, and tsupport φ, tsupport φ_ℓ ⊆ K_δ). Hence the integrals over D equal the integrals over K_δ (MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero with K_δ ⊆ D, both measurable), and all integrands are integrable on K_δ (G integrable on K_δ times a bounded continuous function, Integrable.mul_bdd). Let ε > 0 and take ℓ as in step 3(d). Then by step 4
 |∫_D G·∂ᵢφ| = |∫_{K_δ} G·∂ᵢφ − ∫_{K_δ} G·∂ᵢφ_ℓ| = |∫_{K_δ} G·(∂ᵢφ − ∂ᵢφ_ℓ)| ≤ ε·∫_{K_δ}|G| (MeasureTheory.norm_integral_le_of_norm_le). As ε > 0 is arbitrary and ∫_{K_δ}|G| < ∞, ∫_D G·∂ᵢφ = 0.
6. Finally ∫_{ℝⁿ} G·∂ᵢφ = ∫_D G·∂ᵢφ because the integrand vanishes outside tsupport φ ⊆ D (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero), so ∫ x, G x * fderiv ℝ φ x (EuclideanSpace.basisFun (Fin n) ℝ i) = 0. ∎

## Key steps

1. Choose δ > 0 with K_δ := cthickening δ (tsupport φ) ⊆ D; G is integrable on the compact K_δ.
2. Hand-normalized smooth mollifiers ϱ_r = (∫B_r)⁻¹B_r (ContDiffBump, support B_r(0), integral 1).
3. φ_ℓ := ϱ_{r_ℓ} ⋆ φ is smooth, tsupport φ_ℓ ⊆ K_δ ⊆ D, and ∂ᵢφ_ℓ = ϱ_{r_ℓ} ⋆ ∂ᵢφ → ∂ᵢφ uniformly (dist_convolution_le, uniform continuity).
4. The smooth-test hypothesis gives ∫_D G ∂ᵢφ_ℓ = 0, and |∫_D G ∂ᵢφ| ≤ ε·∫_{K_δ}|G| for every ε > 0, so ∫_D G ∂ᵢφ = 0.
5. The integrand vanishes off tsupport φ ⊆ D, so the whole-space integral is 0 (the exact hypothesis form of the Chapter 8 constancy theorem).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD vs manifest.json`
- `rg -n 'integral_area_formula_of_injective_derivative|weighted_area_formula_of_injective_derivative|areaJacobianAt_eq_sqrt_det_adjoint_comp|def areaJacobianAt' simongmt/Poincare/SimonGMT/Chapter02`
- `rg -n 'def HasApproximateTangentSpaceAt|support_euclideanHausdorffMeasure_restrict_submodule|regular_euclideanHausdorffMeasure_restrict_submodule|HasApproximateTangentSpaceAt.unique|def blowUpMap' Chapter03/Rectifiable.lean`
- `rg -n 'exteriorDerivative_apply|def affinePullbackForm|exteriorDerivative_affinePullbackForm|tsupport_exteriorDerivative_subset|GeometricCurrentOn.boundary|def GeometricCurrentOn.zeroRegion|def GeometricCurrentOn.support|VanishesOn' Chapter06/{Forms,Currents,AffineCurrentPushforward,CurrentLocalEquality}.lean`
- `rg -n 'ae_eq_const_of_weak_coordinate_derivatives_zero|WeakDerivativesZero|abbrev Euclidean' Chapter08/{DistributionalConstancy,Varifold}.lean (C¹ tests only; no smooth-test variant)`
- `rg -n 'theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume|theorem dist_convolution_le|def apply (m : ι → E)|theorem ContDiffOn.differentiableOn|continuousOn_fderiv_of_isOpen' in pinned Mathlib`
- `lake env lean /tmp/gcr3-work/Closure{,2,3}.lean: #exists tests (Lean environment lookup) of ~150 cited names against import GMT.Ch07.Submission`
- `lake env lean /tmp/gcr3-work/{Orig,Plus}.lean: hash dump of all GMT.Ch07 constants without/with import Chapter02.WeightedArea + Chapter08.DistributionalConstancy (diff: identical)`
- `python3 lean_contract.validate_lean_statement + gmt-compare.contract_scope; lake env lean /tmp/gcr3-work/Challenges.lean`
- `lake env lean /tmp/gcr3-work/Assembly.lean; #print axioms GMT.Ch07.dgcr_assembly_check`
- `python3 scan of dag.json and nodes/*/{decomposition-v*,parent-child-handoff}.json lean_names (dgcr_ collisions; accepted reusable declarations such as rsdic_unitOrientation_eq_or_eq_neg); git grep dgcr_ over all refs`
- `read runtime flow: leaf_verification.check_source_delta / check_git_delta, parent_verification.check_parent_git_delta, runtime._machine_leaf, _solve_children node bound, _existing_lean_name_problem, _overlay_accepted_children, _publish_workspace_branch; swarm-configs/583ac9fefa804936b5c9a125fda7b1f6.json (max_nodes 1000, leaf_lean_agent_review false)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-07a3972eec1d/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-07a3972eec1d/_recursive_lean/parent_verification.py`
- `/runtime/flows/gmt-claude-07a3972eec1d/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/583ac9fefa804936b5c9a125fda7b1f6.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-regular-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-regular-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-im-sub-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-integer-combination-a1-orientation-sign-a1/parent-child-handoff.json`
- `/tmp/gcr3-work/Closure.lean`
- `/tmp/gcr3-work/Closure2.lean`
- `/tmp/gcr3-work/Closure3.lean`
- `/tmp/gcr3-work/Orig.lean`
- `/tmp/gcr3-work/Plus.lean`
- `/tmp/gcr3-work/Challenges.lean`
- `/tmp/gcr3-work/Assembly.lean`

Snapshot = project b4d606d and mathlib 25730c7c. The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean, and the simongmt package is at its pinned commit 2b36630.
Reusable facts found:
- Chapter02.integral_area_formula_of_injective_derivative: Bochner area formula for an injective map with injective derivative, any integrand. Used by the parent with areaJacobianAt_eq_sqrt_det_adjoint_comp.
- Chapter08.ae_eq_const_of_weak_coordinate_derivatives_zero: distributional constancy, C¹ tests only, so the smooth-to-C¹ child is needed.
- Chapter03 HasApproximateTangentSpaceAt with finrank_eq, support_/regular_euclideanHausdorffMeasure_restrict_submodule.
- Chapter06 exteriorDerivative_apply (Mathlib extDeriv convention), affinePullbackForm with exteriorDerivative_affinePullbackForm, tsupport_exteriorDerivative_subset, boundary_apply, zeroRegion/support.
- Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn.
- Mathlib: EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.measure_compl_support, Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le, convolution smoothness/derivative lemmas and dist_convolution_le, ContinuousAlternatingMap.apply / norm_image_sub_le, AlternatingMap.eq_smul_basis_det, Fin.sign_cycleRange.
Outside the frozen import closure, hence used only in the parent: Chapter02.WeightedArea/Area and Chapter08.DistributionalConstancy. Adding these two imports keeps all 103 GMT.Ch07 declarations hash-identical. Mathlib BumpFunction.Normed/Convolution are also outside, so the mollifier child normalizes a ContDiffBump by hand.
Workflow facts: childless nodes are machine leaves that may append only one theorem. This worker allows 1000 nodes and the DAG has 249. The accepted rsdic_unitOrientation_eq_or_eq_neg exists but is not reused, because a leaf would depend on it across branches.
Lean checks:
- All 9 child types pass validate_lean_statement and elaborate in the comparator contract scope.
- The exact parent type follows from the 7 parent-level child types plus the two library modules, using only propext, Classical.choice and Quot.sound.
- No name collisions.
