# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_chart-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_chart-a1.oriented_frame-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 1–3 of the supplied proof of the selected node graph_chart (Submission.codim1_zsl_oriented_graph_chart), with Q₀ := Q and ξ_N(x) := ξ. Orientations: Simon Ch. 6, 1.1 and 2.2. Uses the accepted declarations Submission.dorag_lip_orthonormal_coordinates (sibling key orthonormal_coordinates; it is parent step 2) and Submission.rsdic_unitOrientation_eq_or_eq_neg (sibling key orientation_sign).
Notation. P := n + 1 + k; e_j := EuclideanSpace.single j 1 ∈ ℝ^{n+1} (j ∈ Fin (n+1)), the standard orthonormal basis; for a family c : Fin (n+1) → ℝ^P and an (n+1)-covector α (a continuous alternating (n+1)-linear map ℝ^P → ℝ), α(c) is the value of α on c.
1. (dim Q = n + 1; parent step 1.) By hypothesis there is an orthonormal family τ : Fin (n+1) → ℝ^P with span(range τ) = Q (and a sign, not needed here). An orthonormal family is linearly independent (Orthonormal.linearIndependent), so finrank Q = finrank span(range τ) = card(Fin (n+1)) = n + 1 (finrank_span_eq_card, Fintype.card_fin).
2. (Orthonormal coordinates; parent step 2.) Apply Submission.dorag_lip_orthonormal_coordinates with n + 1 in place of n, the same k, and T₀ := Q; its hypothesis finrank Q = n + 1 is step 1, and Euclid ((n+1) + k) is literally Euclid (n + 1 + k). It gives linear isometries ι₀ : ℝ^{n+1} → ℝ^P and ι' : ℝ^k → ℝ^P with (a) ⟨ι₀v, ι'w⟩ = 0 for all v, w; (b) ι₀v ∈ Q for all v; (c) every y ∈ ℝ^P equals ι₀v + ι'w for some v, w; (d) p_Q(ι₀v + ι'w) = ι₀v for all v, w, where p_Q = Q.starProjection is the orthogonal projection onto Q.
3. (range ι₀ = Q.) The inclusion range ι₀ ⊆ Q is (b). Conversely, let q ∈ Q and write q = ι₀v + ι'w by (c). Since q ∈ Q, p_Q q = q (Submodule.starProjection_eq_self_iff), while p_Q q = ι₀v by (d). Hence q = ι₀v ∈ range ι₀.
4. (The orientation ζ₀ of the frame ι₀e; parent step 3.) Let τ₀ := (ι₀e_0, …, ι₀e_n). It is orthonormal, being the image of the orthonormal family (e_j) (EuclideanSpace.orthonormal_single) under the linear isometry ι₀ (Orthonormal.comp_linearIsometry). Its span is contained in Q by (b), and it has dimension n + 1 because τ₀ is linearly independent (finrank_span_eq_card); as finrank Q = n + 1 (step 1), span(range τ₀) = Q (Submodule.eq_of_le_of_finrank_eq). Let ζ₀ ∈ MultiVector P (n+1) be evaluation at τ₀, ζ₀(α) := α(τ₀): this is the continuous linear map ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ τ₀, and ζ₀(α) = α(τ₀) holds by definition. Thus IsUnitOrientationOf ζ₀ Q, witnessed by τ₀ with the + sign.
5. (Sign.) ζ₀ and ξ are unit orientations of the same subspace Q, so Submission.rsdic_unitOrientation_eq_or_eq_neg (with v := ζ₀, w := ξ) gives ξ = ζ₀ or ξ = −ζ₀.
6. (Case ξ = ζ₀.) Take ι := ι₀ and ι' from step 2. Orthogonality is (a), the decomposition is (c), range ι = Q is step 3, and ξ(α) = ζ₀(α) = α(ι₀e_0, …, ι₀e_n) for every α.
7. (Case ξ = −ζ₀.) Let K := (span{e_0})^⊥ ⊆ ℝ^{n+1} and let ρ := K.reflection, the reflection in the hyperplane K, a linear isometric equivalence of ℝ^{n+1}. Then ρ(e_0) = −e_0 (Submodule.reflection_orthogonalComplement_singleton_eq_neg); for j ≠ 0, ⟨e_0, e_j⟩ = 0, i.e. e_j ∈ K (Submodule.mem_orthogonal_singleton_iff_inner_right, EuclideanSpace.inner_single_left), so ρ(e_j) = e_j (Submodule.reflection_mem_subspace_eq_self); and ρ(ρ(v)) = v for all v (Submodule.reflection_reflection). Put ι := ι₀ ∘ ρ (a linear isometry, ι₀.comp ρ.toLinearIsometry) and keep ι'.
 (i) ⟨ιv, ι'w⟩ = ⟨ι₀(ρv), ι'w⟩ = 0 by (a).
 (ii) Given y ∈ ℝ^P, write y = ι₀v + ι'w by (c); then y = ι(ρv) + ι'w because ι(ρv) = ι₀(ρ(ρv)) = ι₀v.
 (iii) range ι = range ι₀ = Q, because ρ is surjective (Function.Surjective.range_comp) and by step 3.
 (iv) The family (ιe_0, …, ιe_n) is τ₀ with its 0-th entry replaced by (−1)·ι₀e_0, i.e. Function.update τ₀ 0 ((−1)·τ₀ 0): indeed ιe_0 = ι₀(−e_0) = −ι₀e_0 and ιe_j = ι₀e_j for j ≠ 0. By linearity of α in the 0-th slot (ContinuousAlternatingMap.map_update_smul, then Function.update_eq_self), α(ιe_0, …, ιe_n) = (−1)·α(τ₀) = −ζ₀(α) = ξ(α) for every α.
 Hence ι, ι' satisfy all four conclusions.
8. In both cases the required ι and ι' exist. ∎

Formal check (scratch validation by the decomposition author; not part of the frozen contract). The tactic proof below, for `theorem Submission.codim1_zsl_gc_oriented_frame : <exactly the frozen lean_statement> := by`, compiled with Lean v4.35.0-rc3 and Mathlib 25730c7c after `import GMT.Ch07.Submission`, with the contract's `open`s inside `namespace GMT.Ch07`, using the default maxHeartbeats (it also compiles under maxHeartbeats 60000), no helper declaration and no set_option. It was compiled once with Submission.dorag_lip_orthonormal_coordinates and Submission.rsdic_unitOrientation_eq_or_eq_neg stated as axioms with their exact frozen types, and again inside an integration file containing the actual proofs of those declarations (the accepted ones taken from their candidate commits, a sibling's from its own Formal check), all five new children and the assembly of the selected theorem, whose #print axioms gave propext, Classical.choice, Quot.sound.
```lean
  intro n k Q ξ hξ
  have hfin : Module.finrank ℝ Q = n + 1 := by
    obtain ⟨τ, hτ, hspan, -⟩ := hξ
    rw [← hspan, finrank_span_eq_card hτ.linearIndependent, Fintype.card_fin]
  obtain ⟨ι₀, ι', h_orth, h_mem, h_span, h_proj⟩ :=
    Submission.dorag_lip_orthonormal_coordinates (n + 1) k Q hfin
  have h_range : Set.range ι₀ = (Q : Set (Euclid (n + 1 + k))) := by
    ext q
    constructor
    · rintro ⟨v, rfl⟩
      exact h_mem v
    · intro hq
      obtain ⟨v, w, rfl⟩ := h_span q
      refine ⟨v, ?_⟩
      have h1 := h_proj v w
      rw [Submodule.starProjection_eq_self_iff.mpr hq] at h1
      exact h1.symm
  have h_on : Orthonormal ℝ (fun j : Fin (n + 1) => ι₀ (EuclideanSpace.single j (1 : ℝ))) :=
    (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin (n + 1))).comp_linearIsometry ι₀
  have h_spanQ :
      Submodule.span ℝ (Set.range (fun j : Fin (n + 1) => ι₀ (EuclideanSpace.single j (1 : ℝ)))) = Q := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact h_mem _
    · rw [finrank_span_eq_card h_on.linearIndependent, Fintype.card_fin, hfin]
  let ζ₀ : MultiVector (n + 1 + k) (n + 1) :=
    ContinuousAlternatingMap.apply ℝ (Euclid (n + 1 + k)) ℝ
      (fun j : Fin (n + 1) => ι₀ (EuclideanSpace.single j (1 : ℝ)))
  have hζ₀ : IsUnitOrientationOf ζ₀ Q :=
    ⟨fun j : Fin (n + 1) => ι₀ (EuclideanSpace.single j (1 : ℝ)), h_on, h_spanQ,
      Or.inl fun α => rfl⟩
  rcases Submission.rsdic_unitOrientation_eq_or_eq_neg (n + 1 + k) (n + 1) ζ₀ ξ Q hζ₀ hξ with h | h
  · refine ⟨ι₀, ι', h_orth, h_span, h_range, fun α => ?_⟩
    rw [h]
    rfl
  · let ρ : Euclid (n + 1) ≃ₗᵢ[ℝ] Euclid (n + 1) :=
      (ℝ ∙ EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ))ᗮ.reflection
    have hρρ : ∀ v, ρ (ρ v) = v := fun v => Submodule.reflection_reflection _ v
    have hρ0 : ρ (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) =
        -EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ) :=
      Submodule.reflection_orthogonalComplement_singleton_eq_neg _
    have hρj : ∀ j : Fin (n + 1), j ≠ 0 →
        ρ (EuclideanSpace.single j (1 : ℝ)) = EuclideanSpace.single j (1 : ℝ) := by
      intro j hj
      apply Submodule.reflection_mem_subspace_eq_self
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right, EuclideanSpace.inner_single_left]
      simp [Ne.symm hj]
    refine ⟨ι₀.comp ρ.toLinearIsometry, ι', fun v w => h_orth (ρ v) w, fun y => ?_, ?_,
      fun α => ?_⟩
    · obtain ⟨v, w, rfl⟩ := h_span y
      exact ⟨ρ v, w, by simp [hρρ]⟩
    · rw [LinearIsometry.coe_comp, LinearIsometryEquiv.coe_toLinearIsometry,
        ρ.surjective.range_comp, h_range]
    · have hfun : (fun j : Fin (n + 1) =>
            (ι₀.comp ρ.toLinearIsometry) (EuclideanSpace.single j (1 : ℝ))) =
          Function.update (fun j : Fin (n + 1) => ι₀ (EuclideanSpace.single j (1 : ℝ))) 0
            ((-1 : ℝ) • ι₀ (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ))) := by
        funext j
        by_cases hj : j = 0
        · subst hj
          rw [Function.update_self, LinearIsometry.coe_comp, Function.comp_apply,
            LinearIsometryEquiv.coe_toLinearIsometry, hρ0, map_neg, neg_one_smul]
        · rw [Function.update_of_ne hj, LinearIsometry.coe_comp, Function.comp_apply,
            LinearIsometryEquiv.coe_toLinearIsometry, hρj j hj]
      rw [hfun, ContinuousAlternatingMap.map_update_smul, Function.update_eq_self, h]
      simp [ζ₀]
```

## Key steps

1. finrank Q = n + 1, since the orthonormal (n+1)-frame τ of IsUnitOrientationOf spans Q.
2. dorag_lip_orthonormal_coordinates gives isometries ι₀, ι' (orthogonal, spanning, ι₀v ∈ Q, p_Q(ι₀v + ι'w) = ι₀v); hence range ι₀ = Q.
3. ζ₀ := evaluation at (ι₀e_0, …, ι₀e_n) is a unit orientation of Q, so orientation_sign gives ξ = ζ₀ or ξ = −ζ₀.
4. If ξ = ζ₀ take ι := ι₀; if ξ = −ζ₀ take ι := ι₀ ∘ ρ with ρ the reflection negating e_0, and multilinearity in slot 0 flips the sign.

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
