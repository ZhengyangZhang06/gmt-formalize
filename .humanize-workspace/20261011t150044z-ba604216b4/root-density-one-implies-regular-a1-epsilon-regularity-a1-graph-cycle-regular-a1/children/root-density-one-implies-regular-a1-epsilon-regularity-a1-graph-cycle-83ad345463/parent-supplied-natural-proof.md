# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.integer_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2, 9, 10, 11 and 12(a)–(c) of the parent proof, up to (but not including) the final application of the area formula: the representation is stated as an Hⁿ-integral over the graph Σ, and the parent converts it to the base disc with the library area formula (outside the frozen import closure). The graph orientation (ξ, β) is taken as a hypothesis; the parent supplies the one constructed by the sibling dgcr_graph_orientation_jacobian. Sibling lemmas used (as the frozen declarations Submission.<name>): dgcr_orthogonal_coordinates (DEC), dgcr_graph_measure_bounds (MB), dgcr_approxTangent_eq_graph_tangent (AT), dgcr_unitOrientation_eq_or_neg (SG).
Notation used throughout: ℝ^m means Euclid m = EuclideanSpace ℝ (Fin m); Hⁿ := μHE[n] (on ℝⁿ it equals Lebesgue measure Lⁿ = volume); ι : ℝⁿ → ℝ^{n+k} and ι' : ℝ^k → ℝ^{n+k} are linear isometries with ⟨ιv, ι'w⟩ = 0 for all v, w; ι*, ι'* are their adjoints; D := B_s(0) ⊆ ℝⁿ (open ball); Φ(v) := z + ιv + ι'u(v); Σ := Φ(D); C := {z + ιv + ι'w : ‖v‖ < s, ‖w‖ < h}; Pr(x) := ι*(x − z), Q(x) := ι'*(x − z); M := R.carrier, θ := R.mult, ξ_R := R.orient, μ := R.measure = θHⁿ⌞M (withDensity of Hⁿ⌞M); ξ and β are the given maps (β continuous on Σ, ξ(x)(β(x)) = 1 on Σ, ξ(Φ(v)) a unit orientation of range DΦ(v) for v ∈ D).
Formalization note: unless this child is split further it is a machine leaf (one theorem appended to the frozen GMT/Ch07/Submission.lean, no new import or helper declaration); the accepted sibling declarations are merged into its base; all library lemmas cited are in the import closure of GMT.Ch07.Submission.
1. Coordinates and openness of C. Adjoint identities: since ι is an isometry, ⟨ι*ιv, v'⟩ = ⟨ιv, ιv'⟩ = ⟨v, v'⟩ for all v', so ι*ι = id; by orthogonality ⟨ι*ι'w, v'⟩ = ⟨ι'w, ιv'⟩ = 0, so ι*ι' = 0; symmetrically ι'*ι' = id and ι'*ι = 0 (ContinuousLinearMap.adjoint_inner_left, LinearIsometry.inner_map_map). Hence Pr(z + ιv + ι'w) = v and Q(z + ιv + ι'w) = w. By DEC(a) applied to x − z, every x equals z + ιv + ι'w for some v, w, and then v = Pr x, w = Q x. Therefore C = {x : ‖Pr x‖ < s and ‖Q x‖ < h} = Pr⁻¹(B_s(0)) ∩ Q⁻¹(B_h(0)), which is open because Pr and Q are continuous (affine). Also Pr∘Φ = id, so Φ is injective.
2. Position of Σ. By hypothesis Σ = spt μ ∩ C, so Σ ⊆ C, and Σ is a Borel set (spt μ is closed, Measure.isClosed_support; C is open).
3. μ is carried by Σ inside C. As ℝ^{n+k} is second countable, μ((spt μ)ᶜ) = 0 (MeasureTheory.Measure.measure_compl_support). For Borel S, μ(S) = ∫⁻_{S} θ d(Hⁿ⌞M) = ∫⁻_{M∩S} θ dHⁿ ≥ Hⁿ(M ∩ S) (withDensity_apply, Measure.restrict_restrict; θ ≥ 1 on M by R.mult_pos, θ being ℕ-valued). With S := (spt μ)ᶜ (open): Hⁿ(M ∖ spt μ) = 0. Since spt μ ∩ C = Σ, (M ∩ C) ∖ Σ ⊆ M ∖ spt μ, hence Hⁿ((M ∩ C) ∖ Σ) = 0. (*)
4. Orientation comparison. By R.orients and ae_restrict_iff' (M is measurable, R.measurableSet_carrier), the set N₁ of x ∈ M for which there is no subspace Q_x with HasApproximateTangentSpaceAt n M x Q_x ∧ IsUnitOrientationOf (ξ_R(x)) Q_x satisfies Hⁿ(N₁) = 0. Put Y := (M ∩ Σ) ∖ N₁. Let x ∈ Y, x = Φ(v) with v ∈ D, and choose Q_x as above. Since C is open and x ∈ Σ ⊆ C, choose r > 0 with B_r(x) ⊆ C; then (M ∩ B_r(x)) ∖ Σ ⊆ (M ∩ C) ∖ Σ is Hⁿ-null by (*). By AT (with A := M, v₀ := v, this r and Q := Q_x), Q_x = range DΦ(v). So ξ_R(x) and ξ(x) = ξ(Φ(v)) are both unit orientations of range DΦ(v), and by SG ξ_R(x) = ξ(x) or ξ_R(x) = −ξ(x). Put ε(x) := ξ_R(x)(β(x)); as ξ(x)(β(x)) = 1, ε(x) ∈ {1, −1} and ξ_R(x) = ε(x)·ξ(x). (**) Finally N₀ := (M ∩ C) ∖ Y ⊆ ((M ∩ C) ∖ Σ) ∪ N₁ is Hⁿ-null.
5. The density on Σ. Define g : ℝ^{n+k} → ℝ by g(x) := θ(x)·ξ_R(x)(β(x)) for x ∈ M and g(x) := 0 for x ∉ M (Set.indicator M). Then: (a) θ(x)·ξ_R(x)(ω) = g(x)·ξ(x)(ω) for every x ∈ Y and every n-covector ω, by (**) (g(x) = θ(x)ε(x)); (b) g = 0 on Σ ∖ M; (c) for x ∈ Y, g(x) = ±θ(x) ∈ ℤ and |g(x)| = θ(x); hence every x ∈ Σ ∖ N₀ satisfies g(x) ∈ ℤ and |g(x)| ≤ θ(x)·1_M(x) (because Σ ∖ N₀ ⊆ Y ∪ (Σ ∖ M)); (d) g is a.e.-strongly measurable for Hⁿ⌞Σ: θ is measurable (R.measurable_mult); ξ_R is a.e.-strongly measurable for Hⁿ⌞M (R.aestronglyMeasurable_orient), hence for the smaller measure Hⁿ⌞(Σ ∩ M) (AEStronglyMeasurable.mono_measure with Measure.restrict_mono); β is continuous on the Borel set Σ, hence a.e.-strongly measurable for Hⁿ⌞Σ (ContinuousOn.aestronglyMeasurable) and for Hⁿ⌞(Σ ∩ M); the evaluation (ζ, α) ↦ ζ(α) is a continuous bilinear map, so x ↦ θ(x)·ξ_R(x)(β(x)) is a.e.-strongly measurable for Hⁿ⌞(Σ ∩ M) = (Hⁿ⌞Σ)⌞M; and by aestronglyMeasurable_indicator_iff (root namespace; M measurable) its indicator g is a.e.-strongly measurable for Hⁿ⌞Σ (note Measure.restrict_restrict gives (Hⁿ⌞Σ)⌞M = Hⁿ⌞(M ∩ Σ)).
6. Transfer to D. Put G(v) := g(Φ(v)).
 (a) Integrality. Let N' ⊇ N₀ be a Borel Hⁿ-null set (toMeasurable). By MB(i) with A := D and the Borel function 1_{N'}: ∫⁻_D 1_{N'}(Φ(v)) dv ≤ ∫⁻_{Σ} 1_{N'} dHⁿ = Hⁿ(Σ ∩ N') = 0. The function v ↦ 1_{N'}(Φ(v)) is AE-measurable for Lⁿ⌞D (Φ is continuous on D, ContinuousOn.aemeasurable, and N' is measurable), so lintegral_eq_zero_iff' gives Φ(v) ∉ N' for Lⁿ-a.e. v ∈ D. Hence for Lⁿ-a.e. v ∈ D: Φ(v) ∈ Σ ∖ N₀, so G(v) ∈ ℤ and |G(v)| ≤ θ(Φ(v))·1_M(Φ(v)). This is the integrality conclusion ∀ᵐ v ∂(volume.restrict D), ∃ m : ℤ, G v = m.
 (b) Measurability. Φ is AE-measurable for Lⁿ⌞D (continuous on D). For every Borel S ⊆ ℝ^{n+k}, Φ_#(Lⁿ⌞D)(S) = ∫⁻_D 1_S(Φ(v)) dv (lintegral_map' applied to the measurable indicator 1_S; Φ⁻¹(S) itself need not be measurable because u is arbitrary off D) ≤ ∫⁻_Σ 1_S dHⁿ = Hⁿ(Σ ∩ S) (MB(i) with A := D and g := 1_S). Hence Φ_#(Lⁿ⌞D) ≤ Hⁿ⌞Σ, in particular Φ_#(Lⁿ⌞D) ≪ Hⁿ⌞Σ; therefore g is a.e.-strongly measurable for Φ_#(Lⁿ⌞D) (AEStronglyMeasurable.mono_measure) and G = g∘Φ is a.e.-strongly measurable for Lⁿ⌞D (AEStronglyMeasurable.comp_aemeasurable), hence also for Lⁿ⌞K' for every K' ⊆ D.
 (c) Local integrability. Let v₀ ∈ D and choose t with ‖v₀‖ < t < s; K' := B̄_t(0) ⊆ D is a compact neighbourhood of v₀. Φ(K') is compact (Φ is continuous on K') and Φ(K') ⊆ Σ ⊆ C ⊆ U. Using (a), MB(i) with A := K' and the Borel function θ·1_M, and R.locallyIntegrable_mult: ∫⁻_{K'} |G| dv ≤ ∫⁻_{K'} θ(Φ(v))·1_M(Φ(v)) dv ≤ ∫⁻_{Φ(K')} θ·1_M dHⁿ = ∫⁻_{M ∩ Φ(K')} θ dHⁿ < ∞ (lintegral_indicator, Measure.restrict_restrict). With (b), G is integrable on the neighbourhood K' of v₀. As v₀ ∈ D was arbitrary, LocallyIntegrableOn G D volume (equivalently, since D is open, G is integrable on every compact subset of D: locallyIntegrableOn_iff).
7. Representation. Let ω ∈ TestFormOn U n with tsupport ω ⊆ C. Then
 T(ω) = ∫_M θ·ξ_R(ω) dHⁿ (R.Represents T, IMRep.action)
 = ∫_{M∩C} θ·ξ_R(ω) dHⁿ (the integrand vanishes on M ∖ C: for x ∉ C we have x ∉ tsupport ω because tsupport ω ⊆ C, so ω(x) = 0 (image_eq_zero_of_notMem_tsupport) and ξ_R(x)(0) = 0; MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero with the measurable set M and M ∩ C ⊆ M)
 = ∫_{M∩Σ} θ·ξ_R(ω) dHⁿ (M ∩ Σ ⊆ M ∩ C and Hⁿ((M ∩ C) ∖ (M ∩ Σ)) = 0 by (*), so the two sets are Hⁿ-a.e. equal and the restricted measures coincide, Measure.restrict_congr_set)
 = ∫_{M∩Σ} g·ξ(ω) dHⁿ (by 5(a) the integrands agree on Y, and (M ∩ Σ) ∖ Y ⊆ N₁ is null; setIntegral_congr_ae with the measurable set M ∩ Σ)
 = ∫_Σ g·ξ(ω) dHⁿ (by 5(b) the integrand g(x)·ξ(x)(ω(x)) vanishes on Σ ∖ (M ∩ Σ); MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero with the measurable set Σ).
 Each equality is an equality of integrands Hⁿ-a.e. on the domain or an equality of restricted measures, so it holds for Bochner integrals without any integrability hypothesis. This is the representation conclusion T ω = ∫ x in Σ, g x * ξ x (ω x) ∂μHE[n].
Steps 6(c), 6(a) and 7 are the three conjuncts of the statement. ∎

## Key steps

1. DEC makes C = {‖Pr x‖ < s, ‖Q x‖ < h} open; Σ = spt μ ∩ C ⊆ C is Borel.
2. μ((spt μ)ᶜ) = 0 and θ ≥ 1 on M give Hⁿ((M ∩ C) ∖ Σ) = 0.
3. AT identifies the approximate tangent plane of M at a.e. x ∈ M ∩ Σ with range DΦ; SG and ξ(β) = 1 give ξ_R = ε·ξ with ε = ξ_R(β) = ±1.
4. g := 1_M·θ·ξ_R(β) is integer-valued Hⁿ-a.e. on Σ with |g| ≤ θ1_M and a.e.-strongly measurable for Hⁿ⌞Σ; MB(i) (Φ_#(Lⁿ⌞D) ≤ Hⁿ⌞Σ) transfers integrality, measurability and local integrability to G = g∘Φ.
5. Chain of a.e./restriction identities: T(ω) = ∫_M θξ_R(ω) = ∫_{M∩C} = ∫_{M∩Σ} θξ_R(ω) = ∫_{M∩Σ} gξ(ω) = ∫_Σ gξ(ω) dHⁿ, valid without integrability hypotheses.

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
