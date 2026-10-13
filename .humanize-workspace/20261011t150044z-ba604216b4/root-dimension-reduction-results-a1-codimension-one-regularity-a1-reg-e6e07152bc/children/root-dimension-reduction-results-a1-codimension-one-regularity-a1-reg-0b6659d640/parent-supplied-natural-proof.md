# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.graph_chart-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.graph_chart-a1.local_inverse_c2-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent step 4, first item: "By the C² inverse function theorem there are an open V₀ with z₀ ∈ V₀ ⊆ V and an open O ∋ 0 such that φ : V₀ → O is bijective with C² inverse." The parent cites Mathlib's ContDiffAt.to_localInverse. That lemma (Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean) is not in the import closure of GMT.Ch07.Submission and gives smoothness of the inverse only at the single point φ(z₀). The neighbourhood statement is therefore derived here from the strict-derivative inverse function theorem (HasStrictFDerivAt.toOpenPartialHomeomorph, InverseFunctionTheorem/FDeriv.lean) and the pointwise smoothness of inverses (OpenPartialHomeomorph.contDiffAt_symm, ContDiff/Operations.lean), both in the import closure. No sibling is used.

Proof.
1. (Calculus on V.) V is open and φ is C² on V. Hence for every z ∈ V: φ is C² at z (ContDiffOn.contDiffAt), φ is differentiable at z with HasFDerivAt φ (Dφ(z)) z, and z ↦ Dφ(z) is continuous on V (ContDiffOn.continuousOn_fderiv_of_isOpen, as 1 ≤ 2).
2. (Injective endomorphisms are invertible.) Let L : ℝ^d → ℝ^d be an injective continuous linear map. Since ℝ^d is finite-dimensional, L is surjective (LinearMap.injective_iff_surjective), hence a linear equivalence, and every linear map between finite-dimensional spaces is continuous. So there is a continuous linear equivalence E_L with (E_L : ℝ^d →L ℝ^d) = L.
3. (The open set where Dφ is invertible.) The set Inj of injective continuous linear endomorphisms of ℝ^d is open (ContinuousLinearMap.isOpen_injective, finite dimension). By step 1, V' := V ∩ (Dφ)⁻¹(Inj) is open (ContinuousOn.isOpen_inter_preimage). By hypothesis z₀ ∈ V'.
4. (Inverse function theorem at z₀.) Let E₀ := E_{Dφ(z₀)} (step 2). φ is C² at z₀ with derivative E₀, hence has strict derivative E₀ at z₀ (ContDiffAt.hasStrictFDerivAt, since 2 ≠ 0). The inverse function theorem (HasStrictFDerivAt.toOpenPartialHomeomorph) gives an open partial homeomorphism Φ of ℝ^d with Φ(z) = φ(z) for all z, z₀ ∈ source(Φ), source(Φ) and target(Φ) open, Φ(source) ⊆ target, Φ⁻¹(target) ⊆ source, Φ⁻¹(Φ(z)) = z for z ∈ source, Φ(Φ⁻¹(y)) = y for y ∈ target, and Φ⁻¹ continuous on target.
5. (Definitions.) Put V₀ := source(Φ) ∩ V', O := target(Φ) ∩ (Φ⁻¹)⁻¹(V₀) and g := Φ⁻¹. V₀ is open, z₀ ∈ V₀ and V₀ ⊆ V' ⊆ V. O is open because Φ⁻¹ is continuous on the open set target(Φ) and V₀ is open (ContinuousOn.isOpen_inter_preimage).
6. (Bijection.)
 (a) For y ∈ O: g(y) ∈ V₀ by the definition of O, and φ(g(y)) = Φ(Φ⁻¹(y)) = y because y ∈ target(Φ).
 (b) For z ∈ V₀: z ∈ source(Φ), so φ(z) = Φ(z) ∈ target(Φ) and g(φ(z)) = Φ⁻¹(Φ(z)) = z ∈ V₀. Hence φ(z) ∈ O and g(φ(z)) = z.
7. (g is C² on O.) Let y ∈ O and z := g(y) ∈ V₀ ⊆ V'. Then Dφ(z) is injective, so by step 2 it equals a continuous linear equivalence E_z; by step 1, HasFDerivAt φ E_z z and φ is C² at z. Since y ∈ target(Φ), Φ = φ and Φ⁻¹(y) = z, the smoothness of inverses (OpenPartialHomeomorph.contDiffAt_symm) shows that g = Φ⁻¹ is C² at y. As y ∈ O was arbitrary, g is C² on O. ∎

Formalization note (verified). The following Lean proof was compiled against the frozen import closure of GMT/Ch07/Submission.lean (Lean 4.35.0-rc3, Mathlib 25730c7c) as a single appended declaration inside namespace GMT.Ch07 before main_theorem; #print axioms gives propext, Classical.choice, Quot.sound; it passes the runtime leaf-delta check (check_source_delta). It may be used verbatim:

theorem Submission.codim1_rdo_gc_local_inverse_c2 : ∀ (d : ℕ) (φ : Euclid d → Euclid d) (V : Set (Euclid d)) (z₀ : Euclid d), IsOpen V → z₀ ∈ V → ContDiffOn ℝ 2 φ V → Injective (fderiv ℝ φ z₀) → ∃ (V₀ O : Set (Euclid d)) (g : Euclid d → Euclid d), IsOpen V₀ ∧ IsOpen O ∧ z₀ ∈ V₀ ∧ V₀ ⊆ V ∧ ContDiffOn ℝ 2 g O ∧ MapsTo g O V₀ ∧ (∀ y ∈ O, φ (g y) = y) ∧ ∀ z ∈ V₀, φ z ∈ O ∧ g (φ z) = z := by
  intro d φ V z₀ hV hz₀ hφ hinj
  have hcont : ContinuousOn (fderiv ℝ φ) V := hφ.continuousOn_fderiv_of_isOpen hV (by norm_num)
  have equivOf : ∀ L : Euclid d →L[ℝ] Euclid d, Injective L →
      ∃ E : Euclid d ≃L[ℝ] Euclid d, (E : Euclid d →L[ℝ] Euclid d) = L := by
    intro L hL
    have hsurj : Surjective L := LinearMap.injective_iff_surjective.mp hL
    exact ⟨(LinearEquiv.ofBijective (L : Euclid d →ₗ[ℝ] Euclid d) ⟨hL, hsurj⟩).toContinuousLinearEquiv, by ext; rfl⟩
  set V' := V ∩ (fderiv ℝ φ) ⁻¹' {L | Injective L} with hV'eq
  have hV' : IsOpen V' := hcont.isOpen_inter_preimage hV ContinuousLinearMap.isOpen_injective
  have hz₀' : z₀ ∈ V' := ⟨hz₀, hinj⟩
  obtain ⟨E₀, hE₀⟩ := equivOf _ hinj
  have hdiff : ∀ z ∈ V, HasFDerivAt φ (fderiv ℝ φ z) z := fun z hz =>
    ((hφ.contDiffAt (hV.mem_nhds hz)).differentiableAt (by norm_num)).hasFDerivAt
  have hstrict : HasStrictFDerivAt φ (E₀ : Euclid d →L[ℝ] Euclid d) z₀ := by
    rw [hE₀]; exact (hφ.contDiffAt (hV.mem_nhds hz₀)).hasStrictFDerivAt (by norm_num)
  set Φ := hstrict.toOpenPartialHomeomorph φ with hΦeq
  have hΦcoe : ∀ z, Φ z = φ z := fun z => rfl
  have hV₀ : IsOpen (Φ.source ∩ V') := Φ.open_source.inter hV'
  refine ⟨Φ.source ∩ V', Φ.target ∩ Φ.symm ⁻¹' (Φ.source ∩ V'), Φ.symm, hV₀,
    Φ.continuousOn_symm.isOpen_inter_preimage Φ.open_target hV₀,
    ⟨hstrict.mem_toOpenPartialHomeomorph_source, hz₀'⟩, fun z hz => hz.2.1, ?_,
    fun y hy => hy.2, fun y hy => by rw [← hΦcoe]; exact Φ.right_inv hy.1, fun z hz => ?_⟩
  · intro y hy
    have hz : Φ.symm y ∈ V' := hy.2.2
    obtain ⟨E, hE⟩ := equivOf _ hz.2
    apply ContDiffAt.contDiffWithinAt
    apply Φ.contDiffAt_symm hy.1
    · rw [hE]; exact hdiff _ hz.1
    · exact hφ.contDiffAt (hV.mem_nhds hz.1)
  · have h1 : Φ.symm (Φ z) = z := Φ.left_inv hz.1
    rw [← hΦcoe]
    exact ⟨⟨Φ.map_source hz.1, by rw [Set.mem_preimage, h1]; exact hz⟩, h1⟩

## Key steps

1. Dφ is continuous on V; injective endomorphisms of ℝ^d are continuous linear equivalences and form an open set, so V' = {z ∈ V : Dφ(z) injective} is open and contains z₀.
2. φ has strict derivative Dφ(z₀) at z₀; HasStrictFDerivAt.toOpenPartialHomeomorph gives an open partial homeomorphism Φ = φ with z₀ in its source.
3. V₀ := source ∩ V', O := target ∩ (Φ⁻¹)⁻¹(V₀), g := Φ⁻¹ give the bijection φ : V₀ → O with inverse g.
4. OpenPartialHomeomorph.contDiffAt_symm at each y ∈ O (Dφ invertible at g(y) ∈ V') makes g C² on O.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `python3 scans of dag.json: accepted lean_statements containing tangentSpace, IsEmbeddedSubmanifold, IsOrientation, IsUnitOrientationOf, Matrix.det, .det, InjOn, fderiv; lean_name lookups chart_tangentSpace_eq_range_fderiv, dsmc_chart_tangentSpace_eq_range, dsmc_chart_inverse_continuity, dsmc_chart_range_subset_tangentSpace, dgoj_unitOrientation_of_injective, dgoj_exists_continuous_covector_eval, dgoj_exists_det_covector, dgoj_covector_eq_det_mul_of_mem_span, dgoj_det_adjoint_comp_eq_det_sq, dpf_exists_orthonormal_frame_det_gram, rsdic_unitOrientation_eq_or_eq_neg, dor_ims_unitOrientation_dual, dgcr_graph_orientation_jacobian, regcomp_unit_orientation_pairing, unit_orientations_common_unit_covector; collision check for the five codim1_rdo_gc_* names`
- `grep in snapshot mathlib: to_localInverse, toOpenPartialHomeomorph, contDiffAt_symm, isOpen_injective, isometryOfOrthonormal, coe_toBasis, constr_range, norm_image_sub_le, ContinuousAlternatingMap.apply`
- `grep -rln 'toOpenPartialHomeomorph|localInverse|InverseFunctionTheorem|contDiffAt_symm' simongmt (--include=*.lean); import lines of simongmt Chapter03/Rectifiable.lean and Chapter06/{Mass,CurrentLocalEquality,AffineCurrentPushforward}.lean`
- `lean -DautoImplicit=false /tmp/gc-split-check/Probe.lean and Probe2.lean (#print Covector, MultiVector; #check ContDiffAt.to_localInverse, HasStrictFDerivAt.toOpenPartialHomeomorph, OpenPartialHomeomorph.contDiffAt_symm, ContDiffAt.hasStrictFDerivAt', ContinuousLinearMap.isOpen_injective, ContDiffOn.continuousOn_fderiv_of_isOpen, Convex.isPreconnected, ContinuousAlternatingMap.map_update_smul, LinearMap.det_toMatrix)`
- `lean -DautoImplicit=false /tmp/gc-split-check/Types.lean (all 12 child types plus the parent assembly; #print axioms)`
- `lean -DautoImplicit=false /tmp/gc-split-check/{Prove124b,Prove1,Prove3,Prove5}.lean (new child proofs against stubs of their prerequisites)`
- `git show <commit>:GMT/Ch07/Submission.lean for fe95347b, 9c8432cb, 44afba4d, 8f402cb9, 05029c89, 93ec31ab, 73310ec9; git merge-base --is-ancestor 8f402cb9 44afba4d; lean -DautoImplicit=false /tmp/gc-split-check/FullCheck.lean with #print axioms`
- `python3: _recursive_lean.leaf_verification.check_source_delta on each new proof and the assembly; _recursive_lean.lean_contract.validate_lean_statement on all 12 types; acyclicity and byte-identity of reused types against dag.json`
- `sed -n of /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py (_decompose, _existing_lean_name_problem, _solve_children, _install_parent_supplied_child_handoff, _overlay_accepted_children, _accepted_checkpoint), __init__.py limits, swarm-project.json (max_depth 6, max_children 12, max_nodes 1000), verifier/gmt-compare.py header`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Basis/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-e6e07152bc/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-e6e07152bc/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ch-f0862c44ef/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ch-751a76913b/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-ea8963379b/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-orientati-ce923d2f7f/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-integer-combination-a1-orientation-sign-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-unit-or-24edf309fb/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/ConstancyNormalCharts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/gc-split-check/Types.lean`
- `/tmp/gc-split-check/Prove124b.lean`
- `/tmp/gc-split-check/Prove3.lean`
- `/tmp/gc-split-check/Prove5.lean`
- `/tmp/gc-split-check/FullCheck.lean`

Pins match:
- manifest project b4d606db and Mathlib 25730c7c equal workspace HEAD and .lake/packages/mathlib; simongmt is 2b366308;
- the snapshot Contract.lean, workspace Contract.lean and Submission.lean share sha256 e4148e7f9503aa28….

Library (import closure of GMT.Ch07.Submission):
- Present: HasStrictFDerivAt.toOpenPartialHomeomorph (InverseFunctionTheorem/FDeriv.lean:117), OpenPartialHomeomorph.contDiffAt_symm (ContDiff/Operations.lean:881), ContinuousLinearMap.isOpen_injective (Normed/Module/FiniteDimension.lean:263), LinearMap.isometryOfOrthonormal (InnerProductSpace/Orthonormal.lean:330), Module.Basis.constr_range (Basis/Defs.lean:547), ContinuousAlternatingMap.map_update_smul.
- Missing: ContDiffAt.to_localInverse (InverseFunctionTheorem/ContDiff.lean). #check reports an unknown constant; SimonGMT uses it only in Chapter08/ConstancyNormalCharts.lean, which the contract does not import. It also gives C² only at the image point, so the neighbourhood inverse function theorem becomes the new child local_inverse_c2.

DAG (683 nodes):
- 7 accepted declarations are reused with byte-identical frozen types and non-empty candidate commits: dsmc_chart_tangentSpace_eq_range 44afba4d, dsmc_chart_range_subset_tangentSpace 8f402cb9 (an ancestor of 44afba4d), dgoj_exists_continuous_covector_eval 05029c89, dpf_exists_orthonormal_frame_det_gram 93ec31ab, dgoj_covector_eq_det_mul_of_mem_span 73310ec9, rsdic_unitOrientation_eq_or_eq_neg fe95347b, dor_ims_unitOrientation_dual 9c8432cb.
- The runtime allows reusing accepted checkpoints with an identical type (_existing_lean_name_problem, _accepted_checkpoint) and merges prerequisite candidate commits (_overlay_accepted_children).
- The five codim1_rdo_gc_* names occur nowhere in dag.json.
- No accepted node gives a neighbourhood C² inverse function theorem, the Gram-matrix form of the unit-orientation lemma (dgoj_unitOrientation_of_injective uses det(F*∘F)), or the orientation normal form of step 1.

Lean:
- All 12 child types elaborate after import GMT.Ch07.Submission in the contract scope.
- FullCheck.lean compiles; it contains the frozen Submission, the accepted reused proofs taken from their candidate commits, the 5 new child proofs and the parent assembly.
- #print axioms for Submission.codim1_rdo_graph_chart and all five new children gives [propext, Classical.choice, Quot.sound].
- Each new proof and the assembly pass check_source_delta, and every type passes validate_lean_statement.
