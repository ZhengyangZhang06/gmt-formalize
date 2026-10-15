# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.graph_orientation_jacobian-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3 and 7 of the parent proof (the Jacobian JΦ, the orientation ξ_Σ with IsUnitOrientationOf and continuity, and the key identity 7(c) α(DΦ(v)e₁, …, DΦ(v)eₙ) = JΦ(v)·ξ_Σ(Φ(v))(α)). Deviation (simplification): instead of a Gram–Schmidt frame (whose continuity would have to be proved), ξ is defined by the key identity itself, ξ(Φ(v))(α) := J(v)⁻¹·α(b(v)); an orthonormal frame is then needed only pointwise, to verify the unit-orientation property. The integral area identity of the parent's step 8 is NOT part of this child: the parent applies the library area formula (Poincare.SimonGMT.Chapter02.integral_area_formula_of_injective_derivative, outside the frozen import closure) together with conclusion (c) and Poincare.SimonGMT.Chapter02.areaJacobianAt_eq_sqrt_det_adjoint_comp.
Notation used throughout: ℝ^m means Euclid m = EuclideanSpace ℝ (Fin m); e₁, …, eₙ is the standard basis of ℝⁿ (EuclideanSpace.single i 1); ι : ℝⁿ → ℝ^{n+k} and ι' : ℝ^k → ℝ^{n+k} are linear isometries with ⟨ιv, ι'w⟩ = 0 for all v, w; ι* is the adjoint of ι; D := B_s(0) ⊆ ℝⁿ (open ball); Φ(v) := z + ιv + ι'u(v); Σ := Φ(D); Pr(x) := ι*(x − z); F(v) := DΦ(v) := fderiv ℝ Φ v; bᵢ(v) := F(v)eᵢ and b(v) := (b₁(v), …, bₙ(v)); A(v) := F(v)*∘F(v), i.e. (fderiv ℝ Φ v).adjoint ∘L fderiv ℝ Φ v, an endomorphism of ℝⁿ; J(v) := √(det A(v)) (ContinuousLinearMap.det, Real.sqrt). "n-covector" means an element of Covector (Euclid (n+k)) n (a continuous alternating n-linear map ℝ^{n+k} → ℝ); MultiVector (n+k) n is the space of continuous linear functionals on n-covectors.
Formalization note: unless this child is split further it is a machine leaf (one theorem appended to the frozen GMT/Ch07/Submission.lean, no new import or helper declaration); all lemmas cited are in the import closure of GMT.Ch07.Submission.
1. Adjoint identities. Since ι is an isometry, ⟨ι*ιv, v'⟩ = ⟨ιv, ιv'⟩ = ⟨v, v'⟩ for all v' (ContinuousLinearMap.adjoint_inner_left, LinearIsometry.inner_map_map), so ι*ι = id; by orthogonality ⟨ι*ι'w, v'⟩ = ⟨ι'w, ιv'⟩ = 0, so ι*ι' = 0. Hence Pr(Φ(v)) = ι*ιv + ι*ι'u(v) = v for every v ∈ ℝⁿ, and Pr is continuous (affine).
2. Derivative. D is open and u is C¹ on D, so u is differentiable at every v ∈ D and F(v) = ι + ι'∘Du(v) (derivative of z + ι(·) + ι'(u(·)), chain rule). Therefore ι*∘F(v) = id + ι*ι'∘Du(v) = id; so F(v) is injective, ι*bᵢ(v) = eᵢ for every i, and L_v := range F(v) has dimension n (LinearMap.finrank_range_of_inj). The map v ↦ F(v) is continuous on D (ContDiffOn.continuousOn_fderiv_of_isOpen, 1 ≤ 1).
3. Linear algebra at a fixed v ∈ D. Write L := L_v and bⱼ := bⱼ(v). Since F(v) is injective and e is a basis, b = (b₁, …, bₙ) is a linearly independent family of n vectors in the n-dimensional space L, hence a basis of L. Choose an orthonormal basis τ = (τ₁, …, τₙ) of L indexed by Fin n (stdOrthonormalBasis ℝ L reindexed along finrank L = n; regard τᵢ ∈ ℝ^{n+k}). Since bⱼ ∈ L, bⱼ = Σᵢ 𝒜ᵢⱼτᵢ with 𝒜ᵢⱼ := ⟨τᵢ, bⱼ⟩ (OrthonormalBasis.sum_repr, repr_apply_apply); 𝒜 is the change-of-basis matrix τ.toBasis.toMatrix b, and det 𝒜 = det_τ(b) ≠ 0 because b is a basis: with the basis 𝔟 := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.map (LinearEquiv.ofInjective F(v) (injectivity)) of L (whose vectors are the bⱼ), (τ.toBasis.isUnit_det 𝔟).ne_zero.
 (i) For every n-covector α, α(b) = det(𝒜)·α(τ). Indeed the restriction α_L(c₁, …, cₙ) := α(c₁, …, cₙ) (cᵢ ∈ L; α composed with the inclusion L → ℝ^{n+k} in every slot) is an alternating n-linear form on the n-dimensional space L, so α_L = α_L(τ)·det_τ (AlternatingMap.eq_smul_basis_det for the basis τ of L); evaluating at (b₁, …, bₙ) ∈ Lⁿ gives α(b) = α(τ)·det_τ(b) and det_τ(b) = det(τ.toMatrix b) = det 𝒜 (Module.Basis.det_apply).
 (ii) Since τ is an orthonormal basis of L and bᵢ, bⱼ ∈ L, ⟨bᵢ, bⱼ⟩ = Σ_l ⟨τ_l, bᵢ⟩⟨τ_l, bⱼ⟩ = Σ_l 𝒜_{li}𝒜_{lj} (OrthonormalBasis.sum_inner_mul_inner), i.e. the Gram matrix Γ := (⟨bᵢ, bⱼ⟩)ᵢⱼ equals 𝒜ᵀ𝒜, so det Γ = (det 𝒜)² (Matrix.det_mul, Matrix.det_transpose).
 (iii) The matrix of A(v) in the standard orthonormal basis of ℝⁿ has entries ⟨eᵢ, A(v)eⱼ⟩ = ⟨F(v)eᵢ, F(v)eⱼ⟩ = ⟨bᵢ, bⱼ⟩ (ContinuousLinearMap.adjoint_inner_right), so det A(v) = det Γ (unfold ContinuousLinearMap.det, then LinearMap.det_toMatrix with (EuclideanSpace.basisFun (Fin n) ℝ).toBasis, LinearMap.toMatrix_apply, ContinuousLinearMap.adjoint_inner_right, EuclideanSpace.inner_single_left). Hence det A(v) = (det 𝒜)² > 0, J(v) = √(det A(v)) = |det 𝒜| > 0.
4. Continuity of J. v ↦ A(v) is continuous on D (v ↦ F(v) is continuous, the adjoint is a linear isometric equivalence, and composition of continuous linear maps is jointly continuous), det is continuous (ContinuousLinearMap.continuous_det), and √ is continuous; so J is continuous and positive on D (step 3(iii)), and J⁻¹ is continuous on D.
5. Definitions. Let ev(c) ∈ MultiVector (n+k) n be evaluation at a family c ∈ (ℝ^{n+k})ⁿ, ev(c)(α) := α(c) (ContinuousAlternatingMap.apply ℝ (Euclid (n+k)) ℝ c, or LinearMap.mkContinuous with the bound |α(c)| ≤ ‖α‖·∏ᵢ‖cᵢ‖ from ContinuousAlternatingMap.le_opNorm). The map c ↦ ev(c) is continuous: by ContinuousAlternatingMap.norm_image_sub_le, |α(c) − α(c')| ≤ ‖α‖·n·max(‖c‖, ‖c'‖)^{n−1}·‖c − c'‖ for every α, so ‖ev(c) − ev(c')‖ ≤ n·max(‖c‖, ‖c'‖)^{n−1}·‖c − c'‖ (ContinuousLinearMap.opNorm_le_bound). Define ξ(x) := J(Pr x)⁻¹·ev(b(Pr x)) if Pr x ∈ D and ξ(x) := 0 otherwise. Let δ be the standard determinant n-form on ℝⁿ, δ(c₁, …, cₙ) := det of the matrix with columns cⱼ, i.e. the basis determinant (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det made into a continuous alternating map: e.g. AlternatingMap.mkContinuous with the Leibniz bound |δ(c)| ≤ (card of the permutation group)·∏ⱼ‖cⱼ‖ (|cᵢⱼ| ≤ ‖cⱼ‖), or the volume form of the standard orientation, o.volumeForm.mkContinuous 1 with Orientation.abs_volumeForm_apply_le, or directly continuity of c ↦ det(basis matrix of c) via Continuous.matrix_det (automatic continuity of multilinear maps on finite-dimensional spaces, MultilinearMap.continuous_of_finiteDimensional, is NOT in the import closure). In every case δ(e₁, …, eₙ) = 1. Let β₀ := δ∘ι* (ContinuousAlternatingMap.compContinuousLinearMap δ ι*), the constant n-covector β₀(w₁, …, wₙ) = δ(ι*w₁, …, ι*wₙ), and β(x) := J(Pr x)·β₀ if Pr x ∈ D, β(x) := 0 otherwise.
6. Continuity on Σ. O := Pr⁻¹(D) is open and contains Σ (Pr Φ(v) = v ∈ D). On O, x ↦ b(Pr x) = (F(Pr x)eᵢ)ᵢ and x ↦ J(Pr x)^{±1} are continuous (steps 2, 4 and continuity of Pr), so ξ = (J∘Pr)⁻¹·(ev∘b∘Pr) and β = (J∘Pr)·β₀ are continuous on O (products of continuous scalar functions with continuous vector-valued functions; ContinuousOn.congr with the defining formulas, which hold on O). Hence ξ and β are ContinuousOn Σ.
7. (a) ξ(x)(β(x)) = 1 on Σ. For x = Φ(v) ∈ Σ we have Pr x = v ∈ D, so, using ι*bᵢ(v) = eᵢ (step 2), ξ(x)(β(x)) = J(v)⁻¹·β(x)(b(v)) = J(v)⁻¹·J(v)·δ(ι*b₁(v), …, ι*bₙ(v)) = δ(e₁, …, eₙ) = 1 (Module.Basis.det_self).
8. (c) The Jacobian identity. For v ∈ D, Pr Φ(v) = v ∈ D, so J(v)·ξ(Φ(v))(α) = J(v)·J(v)⁻¹·α(b(v)) = α(b(v)) for every n-covector α (J(v) > 0). This is the frozen conclusion α(fun i => fderiv ℝ Φ v (EuclideanSpace.single i 1)) = √(det((fderiv ℝ Φ v).adjoint ∘L fderiv ℝ Φ v))·ξ(Φ v)(α).
9. (b) Unit orientation. Fix v ∈ D, with L, τ, 𝒜 as in step 3. Put σ := det(𝒜)/J(v) ∈ {1, −1} (step 3(iii)). By step 3(i), ξ(Φ(v))(α) = J(v)⁻¹·α(b(v)) = σ·α(τ) for every α. τ is an orthonormal family in ℝ^{n+k} (inner products in L are those of ℝ^{n+k}) with span(range τ) = L = range F(v). Hence IsUnitOrientationOf (ξ(Φ(v))) (range F(v)) holds, with the first disjunct (∀ α, ξ(Φ v)(α) = α(τ)) if σ = 1 and the second (∀ α, ξ(Φ v)(α) = −α(τ)) if σ = −1.
Steps 6–9 give the five conjuncts of the statement (continuity of ξ and of β on Σ, (a), (b), (c)). ∎

## Key steps

1. DΦ(v) = ι + ι'∘Du(v) is injective with ι*∘DΦ(v) = id and depends continuously on v ∈ D.
2. At each v: b(v) is a basis of L = range DΦ(v); with an orthonormal basis τ of L and 𝒜 = coordinates of b, α(b) = det(𝒜)·α(τ) and det(DΦ*DΦ) = det Gram(b) = (det 𝒜)² > 0.
3. J := √det(DΦ*DΦ) is continuous and positive on D; define ξ(x) := J(Pr x)⁻¹·ev(b(Pr x)) and β(x) := J(Pr x)·(δ∘ι*) on Pr⁻¹(D).
4. ξ and β are continuous on Pr⁻¹(D) ⊇ Σ; ξ(β) = δ(ι*b) = δ(e) = 1 on Σ.
5. J(v)·ξ(Φ v)(α) = α(b(v)) by definition, and ξ(Φ v) = (det 𝒜/J)·(α ↦ α(τ)) = ±(α ↦ α(τ)) is a unit orientation of range DΦ(v).

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
