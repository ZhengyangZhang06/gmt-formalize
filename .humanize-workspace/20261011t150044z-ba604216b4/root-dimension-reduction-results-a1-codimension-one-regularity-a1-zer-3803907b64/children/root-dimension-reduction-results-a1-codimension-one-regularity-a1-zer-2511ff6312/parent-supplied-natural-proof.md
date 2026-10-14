# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_chart-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_chart-a1.local_inverse-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 6 of the supplied proof of the selected node graph_chart (the inverse function theorem applied to Φ = ι*(ψ − x)), stated for an arbitrary C¹ map φ : ℝ^d → ℝ^d; the sibling child local_graph applies it to Φ. Standard inverse function theorem (as used by Simon Ch. 2, §4); Mathlib: HasStrictFDerivAt.toOpenPartialHomeomorph and OpenPartialHomeomorph.contDiffAt_symm.
1. (Pointwise regularity.) V is open and φ is C¹ on V, so for every z ∈ V, φ is C¹ at z (ContDiffOn.contDiffAt, V ∈ 𝓝 z), hence differentiable at z with derivative Dφ(z) = fderiv ℝ φ z (ContDiffAt.differentiableAt, 1 ≠ 0); and z ↦ Dφ(z) is continuous on V (ContDiffOn.continuousOn_fderiv_of_isOpen, 1 ≤ 1).
2. (Dφ(z₀) is invertible.) Dφ(z₀) is an injective linear endomorphism of the finite-dimensional space ℝ^d, hence bijective, and it is the underlying map of a continuous linear equivalence L₀ : ℝ^d ≃L ℝ^d (LinearEquiv.ofInjectiveEndo followed by LinearEquiv.toContinuousLinearEquiv; every linear map between finite-dimensional spaces is continuous).
3. (The set where the derivative is invertible.) Let G ⊆ L(ℝ^d, ℝ^d) be the set of operators that are coercions of continuous linear equivalences; G is open (ContinuousLinearEquiv.isOpen). Put V₁ := V ∩ (Dφ)^{−1}(G). Since V is open and Dφ is continuous on V (step 1), V₁ is open (ContinuousOn.isOpen_inter_preimage); and z₀ ∈ V₁ by step 2.
4. (Inverse function theorem.) φ is C¹ at z₀, so it has strict derivative Dφ(z₀) = L₀ at z₀ (ContDiffAt.hasStrictFDerivAt). The inverse function theorem (HasStrictFDerivAt.toOpenPartialHomeomorph) gives an open partial homeomorphism e of ℝ^d whose underlying function is φ, with z₀ ∈ source(e) (HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source). Restrict e to the open set V₁ (OpenPartialHomeomorph.restrOpen): this gives an open partial homeomorphism e' whose underlying function is still φ, with source(e') = source(e) ∩ V₁, so z₀ ∈ source(e') ⊆ V₁. Put V₀ := source(e'), O := target(e') and χ := e'.symm (the inverse, a function defined on all of ℝ^d).
5. (Elementary properties.) V₀ and O are open (open_source, open_target); z₀ ∈ V₀; V₀ ⊆ V₁ ⊆ V; χ maps O into V₀ (mapsTo_symm); φ(χ(a)) = a for a ∈ O (right_inv); and for z ∈ V₀, φ(z) ∈ O (map_source) and χ(φ(z)) = z (left_inv).
6. (χ is C¹ on O.) Let a ∈ O. Then χ(a) ∈ V₀ ⊆ V₁, so χ(a) ∈ V and Dφ(χ(a)) is the coercion of a continuous linear equivalence L; thus φ has derivative L at χ(a) and φ is C¹ at χ(a) (step 1). By the inverse-function lemma for open partial homeomorphisms (OpenPartialHomeomorph.contDiffAt_symm, applied to e' with a ∈ target(e')), χ is C¹ at a, hence C¹ within O at a. As a ∈ O was arbitrary, χ is C¹ on O.
7. Steps 4–6 give V₀, O and χ with all the stated properties. ∎

Formal check (scratch validation by the decomposition author; not part of the frozen contract). The tactic proof below, for `theorem Submission.codim1_zsl_gc_local_inverse : <exactly the frozen lean_statement> := by`, compiled with Lean v4.35.0-rc3 and Mathlib 25730c7c after `import GMT.Ch07.Submission`, with the contract's `open`s inside `namespace GMT.Ch07`, using the default maxHeartbeats (it also compiles under maxHeartbeats 60000), no helper declaration and no set_option. It needs no other declaration: it was compiled on its own (#print axioms: propext, Classical.choice, Quot.sound) and again inside an integration file containing all five new children, the actual proofs of the five reused declarations (taken from their candidate commits) and the assembly of the selected theorem, whose #print axioms gave propext, Classical.choice, Quot.sound.
```lean
  intro d φ V z₀ hV hz₀ hφ hinj
  -- the derivative at `z₀` is invertible (injective endomorphism of a finite-dimensional space)
  let L₀ : Euclid d ≃L[ℝ] Euclid d :=
    (LinearEquiv.ofInjectiveEndo
      ((fderiv ℝ φ z₀ : Euclid d →L[ℝ] Euclid d) : Euclid d →ₗ[ℝ] Euclid d)
      hinj).toContinuousLinearEquiv
  have hL₀ : (L₀ : Euclid d →L[ℝ] Euclid d) = fderiv ℝ φ z₀ := by
    ext x; rfl
  have hcd : ∀ z ∈ V, ContDiffAt ℝ 1 φ z := fun z hz => hφ.contDiffAt (hV.mem_nhds hz)
  have hcont : ContinuousOn (fderiv ℝ φ) V := hφ.continuousOn_fderiv_of_isOpen hV le_rfl
  -- the open set where `φ` has invertible derivative
  let V₁ : Set (Euclid d) :=
    V ∩ fderiv ℝ φ ⁻¹' range ((↑) : (Euclid d ≃L[ℝ] Euclid d) → Euclid d →L[ℝ] Euclid d)
  have hV₁ : IsOpen V₁ := hcont.isOpen_inter_preimage hV ContinuousLinearEquiv.isOpen
  have hz₀V₁ : z₀ ∈ V₁ := ⟨hz₀, L₀, hL₀⟩
  have hstrict : HasStrictFDerivAt φ (L₀ : Euclid d →L[ℝ] Euclid d) z₀ := by
    rw [hL₀]
    exact (hcd z₀ hz₀).hasStrictFDerivAt one_ne_zero
  -- inverse function theorem, restricted to `V₁`
  obtain ⟨e, he, hz₀e, hsrc⟩ : ∃ e : OpenPartialHomeomorph (Euclid d) (Euclid d),
      ⇑e = φ ∧ z₀ ∈ e.source ∧ e.source ⊆ V₁ :=
    ⟨(hstrict.toOpenPartialHomeomorph φ).restrOpen V₁ hV₁, rfl,
      ⟨hstrict.mem_toOpenPartialHomeomorph_source, hz₀V₁⟩, inter_subset_right⟩
  subst he
  refine ⟨e.source, e.target, e.symm, e.open_source, e.open_target, hz₀e,
    fun z hz => (hsrc hz).1, ?_, e.mapsTo_symm, fun a ha => e.right_inv ha,
    fun z hz => ⟨e.map_source hz, e.left_inv hz⟩⟩
  intro a ha
  obtain ⟨hV', L, hL⟩ := hsrc (e.map_target ha)
  have hd : HasFDerivAt e (L : Euclid d →L[ℝ] Euclid d) (e.symm a) := by
    rw [hL]
    exact ((hcd _ hV').differentiableAt one_ne_zero).hasFDerivAt
  exact (e.contDiffAt_symm ha hd (hcd _ hV')).contDiffWithinAt
```

## Key steps

1. Dφ is continuous on V and Dφ(z₀), an injective endomorphism of ℝ^d, is a continuous linear automorphism L₀.
2. V₁ := V ∩ {z : Dφ(z) invertible} is an open neighbourhood of z₀ (ContinuousLinearEquiv.isOpen).
3. The inverse function theorem (HasStrictFDerivAt.toOpenPartialHomeomorph) restricted to V₁ gives V₀ = source, O = target and χ = inverse.
4. At each a ∈ O, Dφ(χ(a)) is invertible and φ is C¹ there, so χ is C¹ at a (OpenPartialHomeomorph.contDiffAt_symm).

## Reference use

### local-project

Queries:
- `cat nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-3803907b64/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.md}`
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sed -n 1,457p GMT/Ch07/Contract.lean (Euclid, MultiVector, IsUnitOrientationOf, IsEmbeddedSubmanifold, tangentSpace, IsOrientation); sed -n 1,60p .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean (Covector = E [⋀^Fin n]→L[ℝ] ℝ)`
- `grep -n 'def check_source_delta' -A40 /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py; sed -n 3159,3200p runtime.py (_overlay_accepted_children merges candidate histories)`
- `python3 scan of dag.json: accepted nodes whose lean_statement mentions tangentSpace, IsUnitOrientationOf, Orthonormal or →ₗᵢ; the region_density_one-a1.graph_chart-a1 branch (codim1_rdo_gc_*, all decomposing, not reusable)`
- `python3: exact lean_statement of rsdic_unitOrientation_eq_or_eq_neg, dgcr_graph_orientation_jacobian, dsmc_chart_range_subset_tangentSpace, dsmc_chart_inverse_continuity, dorag_lip_orthonormal_coordinates and codim1_zsl_oriented_graph_chart from dag.json; comparison with the handoff and with decomposition-v2.json of the parent (identical)`
- `git show <candidate>:GMT/Ch07/Submission.lean for fe95347baaed, 62aa1f119348, 8f402cb9186d, 5e4b21584624, dd8fcf8bcea7; pairwise git merge-base --is-ancestor (none) and declaration sets (disjoint)`
- `grep -rl codim1_zsl_gc dag.json nodes/ GMT .lake/packages/simongmt/Poincare local-references/123e8435b4a2469b/project (no match); for r in $(git for-each-ref --format='%(objectname)' | sort -u): git grep -q -e codim1_zsl_gc $r -- 'GMT/*.lean' (1523 refs, 0 hits; positive control dgcr_graph_orientation_jacobian: 8 hits)`
- `rg -n in local-references/123e8435b4a2469b/mathlib/Mathlib: OpenPartialHomeomorph.contDiffAt_symm, toOpenPartialHomeomorph, ContinuousLinearEquiv.isOpen, ofInjectiveEndo, restrOpen, ContinuousAlternatingMap.apply, reflection_orthogonalComplement_singleton_eq_neg, reflection_mem_subspace_eq_self, reflection_reflection, Orthonormal.comp_linearIsometry, EuclideanSpace.orthonormal_single, LinearIsometry.adjoint_comp_self, finrank_span_eq_card, eq_of_le_of_finrank_eq, IsPreconnected.intermediate_value, ContinuousOn.clm_apply, map_update_smul, ContDiffOn.continuousOn_fderiv_of_isOpen, starProjection_eq_self_iff, norm_add_sq_real, mem_orthogonal_singleton_iff_inner_right, adjoint_inner_left`
- `lake env lean -DautoImplicit=false /tmp/gc-split/Types.lean (10 child types + selected type, exit 0)`
- `lake env lean -DautoImplicit=false /tmp/gc-split/Assembly.lean (children as axioms; #print axioms)`
- `lake env lean -DautoImplicit=false /tmp/gc-split/{oriented_frame,local_inverse,local_graph,graph_cylinder,orientation_along_graph}/Proof.lean; /tmp/gc-split/Combined.lean and Combined_hb60000.lean (all exit 0)`
- `lake env lean -DautoImplicit=false /tmp/gc-split/Integration.lean (real accepted proofs of the 5 reused declarations + 5 new proofs + assembly; exit 0; #print axioms: propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/OpenPartialHomeomorph/IsImage.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Reflection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/IntermediateValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-3803907b64/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-3803907b64/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0b42d13aab/decomposition-v2.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/tmp/gc-split/Types.lean`
- `/tmp/gc-split/Assembly.lean`
- `/tmp/gc-split/Combined_hb60000.lean`
- `/tmp/gc-split/Integration.lean`

Pins match. The snapshot manifest records project b4d606db and Mathlib 25730c7c, which equal workspace HEAD and .lake/packages/mathlib. The workspace Contract.lean and Submission.lean are byte-identical, and the frozen selected type in dag.json equals the handoff's.
Reuse. Five accepted declarations cover parts of the supplied proof, and each is reused with its byte-identical dag.json type:
- rsdic_unitOrientation_eq_or_eq_neg (fe95347baaed)
- dgcr_graph_orientation_jacobian (62aa1f119348)
- dsmc_chart_range_subset_tangentSpace (8f402cb9186d), parent steps 5 and 11
- dsmc_chart_inverse_continuity (5e4b21584624), parent step 8
- dorag_lip_orthonormal_coordinates (dd8fcf8bcea7), parent step 2
The similar codim1_rdo_gc_* nodes of the region_density_one graph_chart branch are only decomposing and have other types, so none is reused.
Names. The 5 new names codim1_zsl_gc_* have no match in dag.json, nodes/, GMT/, SimonGMT, the snapshot project, or GMT/*.lean at any of 1523 ref tips.
Mathlib. Every Mathlib lemma cited by the children exists in the snapshot, for example:
- OpenPartialHomeomorph.contDiffAt_symm (ContDiff/Operations.lean:881)
- HasStrictFDerivAt.toOpenPartialHomeomorph (InverseFunctionTheorem/FDeriv.lean:117)
- ContinuousLinearEquiv.isOpen (BoundedLinearMaps.lean:543)
- OpenPartialHomeomorph.restrOpen (OpenPartialHomeomorph/IsImage.lean:216)
- ContinuousAlternatingMap.apply (Alternating/Topology.lean:294)
- the reflection lemmas (Projection/Reflection.lean:81, 117, 150)
- LinearIsometry.adjoint_comp_self (Adjoint.lean:1066)
- IsPreconnected.intermediate_value (Order/IntermediateValue.lean:125)
Lean.
- All 10 child types and the selected type elaborate.
- The selected type follows from the 4 direct children with only standard axioms.
- Each new child has a compiled single-theorem proof under default heartbeats (also under 60000).
- The final integration with the real accepted proofs compiles; the selected theorem's axioms are propext, Classical.choice and Quot.sound.
