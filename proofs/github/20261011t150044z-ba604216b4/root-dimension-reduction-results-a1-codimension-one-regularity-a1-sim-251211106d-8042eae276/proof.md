# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_charts-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_charts-a1.local_inverse_cr-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the inverse function theorem steps of the parent proof (step 2: "φ₁ maps V₀ C¹-diffeomorphically onto D"; step 3: "By the C^r inverse function theorem φ' maps an open set V'' ∋ v₀ (V'' ⊆ V') C^r-diffeomorphically onto an open set D''"), i.e. the inverse function theorem as used in Simon Ch. 2, 4.4. It is the C^r analogue of the accepted lemmas codim1_zsl_gc_local_inverse (r = 1) and codim1_rdo_gc_local_inverse_c2 (r = 2); their argument works verbatim for every r ≥ 1. No dependencies.
1. (Regularity of φ.) Since V is open and r ≥ 1 (so r ≠ 0 and 1 ≤ r as exponents in WithTop ℕ∞), φ is C^r at every z ∈ V (ContDiffOn.contDiffAt), hence differentiable there with HasFDerivAt φ (Dφ(z)) z (ContDiffAt.differentiableAt); and z ↦ Dφ(z) is continuous on V (ContDiffOn.continuousOn_fderiv_of_isOpen).
2. (Injective endomorphisms are isomorphisms.) If L : ℝ^d → ℝ^d is an injective continuous linear map, then L is surjective (finite dimension, LinearMap.injective_iff_surjective), so L = E_L for the continuous linear equivalence E_L := (LinearEquiv.ofBijective L ⟨injective, surjective⟩).toContinuousLinearEquiv.
3. (An open set of good points.) The set ℐ of injective continuous linear maps ℝ^d → ℝ^d is open (ContinuousLinearMap.isOpen_injective; ℝ^d is finite-dimensional). As Dφ is continuous on the open set V, V' := V ∩ (Dφ)⁻¹(ℐ) is open (ContinuousOn.isOpen_inter_preimage), and z₀ ∈ V' by hypothesis.
4. (Inverse function theorem at z₀.) Let E₀ be the equivalence of step 2 with E₀ = Dφ(z₀). Since φ is C^r at z₀ and r ≠ 0, φ has strict derivative E₀ at z₀ (ContDiffAt.hasStrictFDerivAt). The strict-derivative inverse function theorem (HasStrictFDerivAt.toOpenPartialHomeomorph) gives an open partial homeomorphism Φ of ℝ^d whose underlying function is φ, with z₀ ∈ Φ.source. Thus Φ.source and Φ.target are open, Φ maps Φ.source into Φ.target, Φ.symm maps Φ.target into Φ.source, Φ.symm(Φ(z)) = z for z ∈ Φ.source, Φ(Φ.symm(a)) = a for a ∈ Φ.target, and Φ.symm is continuous on Φ.target.
5. (Choice of V₀, O, χ.) Put V₀ := Φ.source ∩ V', O := Φ.target ∩ Φ.symm⁻¹(V₀) and χ := Φ.symm. V₀ is open, z₀ ∈ V₀ (steps 3 and 4), and V₀ ⊆ V' ⊆ V. O is open because Φ.symm is continuous on the open set Φ.target. By definition χ maps O into V₀, and for a ∈ O ⊆ Φ.target we have φ(χ(a)) = Φ(Φ.symm(a)) = a.
6. (φ maps V₀ into O and χ∘φ = id on V₀.) Let z ∈ V₀ ⊆ Φ.source. Then Φ(z) ∈ Φ.target and Φ.symm(Φ(z)) = z ∈ V₀, so φ(z) = Φ(z) ∈ O and χ(φ(z)) = z.
7. (χ is C^r on O.) Let a ∈ O and z := χ(a) ∈ V₀ ⊆ V'. By step 3, Dφ(z) is injective, so by step 2 Dφ(z) = E for some continuous linear equivalence E, and HasFDerivAt Φ E z by step 1 (Φ = φ). Moreover φ is C^r at z because z ∈ V and V is open. Since a ∈ Φ.target and z = Φ.symm(a), OpenPartialHomeomorph.contDiffAt_symm shows that χ = Φ.symm is C^r at a; in particular C^r within O at a. Hence χ is C^r on O.
8. (Conclusion.) V₀, O and χ have all the stated properties. ∎

## Key steps

1. Dφ is continuous on V and injective endomorphisms of ℝ^d are continuous linear equivalences, so V' = V ∩ {z : Dφ(z) injective} is an open neighbourhood of z₀.
2. The strict-derivative inverse function theorem gives an open partial homeomorphism Φ = φ with z₀ ∈ Φ.source.
3. Take V₀ = Φ.source ∩ V', O = Φ.target ∩ Φ.symm⁻¹(V₀), χ = Φ.symm: χ(O) ⊆ V₀, φ∘χ = id on O, φ(V₀) ⊆ O and χ∘φ = id on V₀.
4. At every a ∈ O, Dφ(χ(a)) is invertible and φ is C^r at χ(a), so OpenPartialHomeomorph.contDiffAt_symm makes χ C^r at a.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `sed -n 210,240p GMT/Ch07/Contract.lean (IsEmbeddedSubmanifold, tangentSpace)`
- `grep -rn 'toOpenPartialHomeomorph|contDiffAt_symm|ContinuousLinearEquiv.isOpen|ContinuousLinearMap.isOpen_injective|continuousOn_fderiv_of_isOpen|contDiffOn_infty|exists_leftInverse_of_injective|injective_iff_surjective|restrOpen|symm_image_target_eq_source|ContinuousOn.isOpen_inter_preimage|IsCompact.image_of_continuousOn|ContDiffAt.differentiableAt|ContDiffAt.hasStrictFDerivAt|ContDiffOn.comp' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `python3 scans of dag.json: selected node; parent hypercone_plane children and decomposition-v1.json; lean_statements mentioning charts, IsEmbeddedSubmanifold, ≃L and local inverses (codim1_zsl_gc_local_inverse, codim1_rdo_gc_local_inverse_c2, dtc_bc_lr_local_inverse, dor_lmb_ret_nc_local_inverse, dgce_left_inverse_chart_embedded, dtc_bc_lr_chart_image_nhds, dor_lmb_ret_chart_localization, dsmc_chart_inverse_continuity)`
- `git show <candidate>:GMT/Ch07/Submission.lean for chart_tangentSpace_eq_range_fderiv (d626082a69a0), dtc_bc_lr_chart_image_nhds (fe444362e7b3), dor_lmb_ret_chart_localization, dgce_left_inverse_chart_embedded, dsmc_chart_inverse_continuity, codim1_rdo_gc_local_inverse_c2 (bdc225a7f750); declared types compared with dag.json; grep sorry/axiom`
- `grep -c codim1_hcp_sc_ dag.json (0); grep -rln codim1_hcp_sc_ nodes/ GMT/ simongmt (none); git for-each-ref (2625 objects) | xargs git grep -l codim1_hcp_sc_ -- 'GMT/*.lean' (none)`
- `runtime.py of flow gmt-claude-252c8df06c56: _decompose (max_depth), _existing_lean_name_problem, _solve_children, _install_parent_supplied_child_handoff, _accepted_checkpoint, _reference_use_problem; store.py ensure`
- `book/chapter-02.txt lines 846-905 (Simon Ch. 2 §4: 4.1 local representation, 4.2 open map onto the image, 4.3 tangent space, 4.4 local graphical representation via the inverse function theorem)`
- `lean -DautoImplicit=false /tmp/sc-split/check/{Types,Proofs,Inst,FromJson}.lean (LEAN_PATH = .lake/build/lib/lean plus every package's .lake/build/lib/lean)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/OpenPartialHomeomorph/IsImage.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/OpenPartialHomeomorph/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Basis/VectorSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/ContinuousOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-6231a88a5f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-b5d5990773/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-retract-4303b6673f/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-252c8df06c56/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-252c8df06c56/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/sc-split/check/Types.lean`
- `/tmp/sc-split/check/Proofs.lean`
- `/tmp/sc-split/check/Inst.lean`
- `/tmp/sc-split/check/FromJson.lean`

Pins match. The snapshot manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib. The snapshot Contract.lean and the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).

Library. The snapshot Mathlib has everything the children need:
- the C^r inverse function theorem: ContDiffAt.toOpenPartialHomeomorph (InverseFunctionTheorem/ContDiff.lean:31) and HasStrictFDerivAt.toOpenPartialHomeomorph (FDeriv.lean:117);
- inverse regularity: OpenPartialHomeomorph.contDiffAt_symm (ContDiff/Operations.lean:881);
- openness of injective maps and of invertible maps: ContinuousLinearMap.isOpen_injective (FiniteDimension.lean:263) and ContinuousLinearEquiv.isOpen (BoundedLinearMaps.lean:543);
- ContDiffOn.continuousOn_fderiv_of_isOpen (Defs.lean:916), contDiffOn_infty (Defs.lean:548), ContDiffOn.comp (Comp.lean:125), restrOpen and symm_image_target_eq_source;
- LinearMap.exists_leftInverse_of_injective (VectorSpace.lean:240) and LinearMap.injective_iff_surjective (FiniteDimensional/Basic.lean:308).
Simon Ch. 2, 4.1–4.4 (chapter-02.txt 846–905) is the source of 4.2, 4.3 and 4.4.

DAG reuse. chart_tangentSpace_eq_range_fderiv (d626082a69a0) and dtc_bc_lr_chart_image_nhds (fe444362e7b3) are accepted, and their candidate declarations have the DAG types. The runtime reuses accepted nodes by identical name and type. Accepted C¹/C² local inverses exist (codim1_zsl_gc_local_inverse, codim1_rdo_gc_local_inverse_c2); their proof generalizes verbatim to the new C^r child. dgce_left_inverse_chart_embedded needs a ball domain and gives no π∘Dg = id, so it is not used. The 4 codim1_hcp_sc_ names are free everywhere.

Lean. All child types elaborate. The selected frozen type and all 4 new children are fully proved in Proofs.lean, with only the two reused accepted declarations as non-standard axioms. Inline casts and instances were checked by rfl (Inst.lean).
