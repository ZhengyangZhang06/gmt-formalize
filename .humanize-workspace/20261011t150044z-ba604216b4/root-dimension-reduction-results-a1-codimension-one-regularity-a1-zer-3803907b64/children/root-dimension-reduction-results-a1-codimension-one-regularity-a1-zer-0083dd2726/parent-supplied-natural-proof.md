# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_chart-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_chart-a1.local_graph-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 4–8 of the supplied proof of the selected node graph_chart, for an arbitrary dimension d (the parent takes d = n + 1), with the parent's identification range ι = Q₀ = tangentSpace N x weakened to the inclusion tangentSpace N x ⊆ range ι, which is all that steps 5–7 use. Embedded submanifolds and T_xN: Simon Ch. 2, §4 (4.1). Uses the sibling child local_inverse (Submission.codim1_zsl_gc_local_inverse; parent step 6) and the accepted declarations Submission.dsmc_chart_range_subset_tangentSpace (key chart_range_tangent; the curve argument of parent step 5) and Submission.dsmc_chart_inverse_continuity (key chart_inverse_continuity; it is the sequential-compactness argument of parent step 8, packaged as a lemma).
Notation. A := ι* and A' := ι'* are the adjoints (ContinuousLinearMap.adjoint of ι.toContinuousLinearMap and of ι'.toContinuousLinearMap), continuous linear maps ℝ^{d+k} → ℝ^d and ℝ^{d+k} → ℝ^k.
0. (Adjoint identities.) For v, v' ∈ ℝ^d: ⟨A(ιv), v'⟩ = ⟨ιv, ιv'⟩ = ⟨v, v'⟩ (ContinuousLinearMap.adjoint_inner_left, LinearIsometry.inner_map_map), so A(ιv) = v (ext_inner_right). For w ∈ ℝ^k: ⟨A(ι'w), v'⟩ = ⟨ι'w, ιv'⟩ = 0 by orthogonality, so A(ι'w) = 0. In the same way A'(ι'w) = w and A'(ιv) = 0. Consequently, for every y ∈ ℝ^{d+k}, writing y = ιv + ι'w (hypothesis) gives Ay = v and A'y = w, hence y = ι(Ay) + ι'(A'y).
1. (Chart at x; parent step 4.) By IsEmbeddedSubmanifold 2 d N at x ∈ N there are an open V ⊆ ℝ^d, an open W ⊆ ℝ^{d+k} with x ∈ W, and ψ : ℝ^d → ℝ^{d+k} which is C² on V and injective on V, with ψ(V) = W ∩ N, V ∩ ψ^{−1}(K) compact for every compact K ⊆ W, and Dψ(z) injective for every z ∈ V. Since x ∈ W ∩ N = ψ(V), choose z₀ ∈ V with ψ(z₀) = x. Also ψ(V) ⊆ N. As 1 ≤ 2, ψ is C¹ on V (ContDiffOn.of_le), hence continuous on V and differentiable at every point of the open set V.
2. (range Dψ(z₀) ⊆ range ι; parent step 5.) By Submission.dsmc_chart_range_subset_tangentSpace (P := d + k, r := 2, the open set V, ψ, ψ(V) ⊆ N, z₀ ∈ V), every vector Dψ(z₀)h lies in tangentSpace N (ψ z₀) = tangentSpace N x, which is contained in range ι by hypothesis. So for every h ∈ ℝ^d there is v ∈ ℝ^d with Dψ(z₀)h = ιv.
3. (The map Φ; parent step 6.) Let Φ(z) := A(ψ(z) − x). Φ is C¹ on V (ψ − x is C¹ on V and A is continuous linear; ContinuousLinearMap.contDiff.comp_contDiffOn). By the chain rule Φ has derivative A ∘ Dψ(z₀) at z₀ (ψ is differentiable at z₀), so DΦ(z₀) = A ∘ Dψ(z₀). It is injective: if A(Dψ(z₀)h) = 0, write Dψ(z₀)h = ιv (step 2); then v = A(ιv) = 0 (step 0), so Dψ(z₀)h = ι0 = 0, and h = 0 because Dψ(z₀) is injective (step 1).
4. (Local inverse.) Apply local_inverse to Φ, V and z₀ (V open, z₀ ∈ V, Φ C¹ on V, DΦ(z₀) injective): there are open sets V₀, O ⊆ ℝ^d and χ : ℝ^d → ℝ^d with z₀ ∈ V₀ ⊆ V, χ C¹ on O, χ(O) ⊆ V₀, Φ(χ(a)) = a for a ∈ O, and Φ(z) ∈ O and χ(Φ(z)) = z for z ∈ V₀. Since Φ(z₀) = A(x − x) = 0 and z₀ ∈ V₀, we get 0 ∈ O and χ(0) = z₀.
5. (The graph function; parent step 7.) Define u(v) := A'(ψ(χ(v)) − x) for every v ∈ ℝ^d.
 (i) u is C¹ on O: ψ ∘ χ is C¹ on O (ContDiffOn.comp: χ is C¹ on O and maps O into V₀ ⊆ V, where ψ is C¹), and u is ψ ∘ χ followed by subtracting x and applying the continuous linear map A'.
 (ii) u(0) = A'(ψ(z₀) − x) = A'(0) = 0.
 (iii) Du(0) = 0: χ is differentiable at 0 (C¹ on the open set O ∋ 0) and ψ is differentiable at χ(0) = z₀ ∈ V, so by the chain rule Du(0) = A' ∘ Dψ(z₀) ∘ Dχ(0). For every h, Dψ(z₀)(Dχ(0)h) = ιv for some v (step 2), and A'(ιv) = 0 (step 0). Hence Du(0)h = 0 for all h, i.e. fderiv ℝ u 0 = 0.
 (iv) For v ∈ O: by step 0, ψ(χ(v)) − x = ι(A(ψ(χ(v)) − x)) + ι'(A'(ψ(χ(v)) − x)) = ι(Φ(χ(v))) + ι'(u(v)) = ιv + ι'u(v), using Φ(χ(v)) = v. Hence x + ιv + ι'u(v) = ψ(χ(v)) ∈ ψ(V) ⊆ N, because χ(v) ∈ V₀ ⊆ V.
6. (The radius s; parent step 8.) V₀ is open and contains z₀: choose ε > 0 with ball(z₀, ε) ⊆ V₀. W is open and contains x: choose r > 0 with ball(x, r) ⊆ W. Apply Submission.dsmc_chart_inverse_continuity to ψ on V (ψ is continuous on V and injective on V, ψ(V) ⊆ W, and V ∩ ψ^{−1}(K) is compact for every compact K ⊆ W) at z₀ ∈ V with this ε: there is δ > 0 such that every z ∈ V with |ψ(z) − ψ(z₀)| < δ satisfies |z − z₀| < ε. Put s := min(δ, r) > 0.
7. (Every nearby point of N lies on the graph.) Let y ∈ N with |y − x| < s. Then |y − x| < r, so y ∈ W and y ∈ W ∩ N = ψ(V): y = ψ(z) with z ∈ V. Since |ψ(z) − ψ(z₀)| = |y − x| < δ, we get |z − z₀| < ε, so z ∈ V₀. Put v := Φ(z); then v ∈ O and χ(v) = z (step 4), so y = ψ(χ(v)) = x + ιv + ι'u(v) by step 5(iv).
8. Steps 4–7 give O (open, 0 ∈ O), u and s with all the stated properties. ∎

Formal check (scratch validation by the decomposition author; not part of the frozen contract). The tactic proof below, for `theorem Submission.codim1_zsl_gc_local_graph : <exactly the frozen lean_statement> := by`, compiled with Lean v4.35.0-rc3 and Mathlib 25730c7c after `import GMT.Ch07.Submission`, with the contract's `open`s inside `namespace GMT.Ch07`, using the default maxHeartbeats (it also compiles under maxHeartbeats 60000), no helper declaration and no set_option. It was compiled once with Submission.codim1_zsl_gc_local_inverse, Submission.dsmc_chart_range_subset_tangentSpace and Submission.dsmc_chart_inverse_continuity stated as axioms with their exact frozen types, and again inside an integration file containing the actual proofs of those declarations (the accepted ones taken from their candidate commits, a sibling's from its own Formal check), all five new children and the assembly of the selected theorem, whose #print axioms gave propext, Classical.choice, Quot.sound.
```lean
  intro d k N x ι ι' hN hx horth hdecomp htan
  -- Step 0: left inverses of `ι`, `ι'` (the adjoints)
  obtain ⟨A, hAι, hAι'⟩ : ∃ A : Euclid (d + k) →L[ℝ] Euclid d,
      (∀ v, A (ι v) = v) ∧ (∀ w, A (ι' w) = 0) := by
    refine ⟨ContinuousLinearMap.adjoint ι.toContinuousLinearMap, fun v => ?_, fun w => ?_⟩
    · refine ext_inner_right ℝ fun v' => ?_
      rw [ContinuousLinearMap.adjoint_inner_left, LinearIsometry.coe_toContinuousLinearMap,
        LinearIsometry.inner_map_map]
    · refine ext_inner_right ℝ fun v' => ?_
      rw [ContinuousLinearMap.adjoint_inner_left, LinearIsometry.coe_toContinuousLinearMap,
        inner_zero_left, real_inner_comm]
      exact horth v' w
  obtain ⟨A', hA'ι, hA'ι'⟩ : ∃ A' : Euclid (d + k) →L[ℝ] Euclid k,
      (∀ v, A' (ι v) = 0) ∧ (∀ w, A' (ι' w) = w) := by
    refine ⟨ContinuousLinearMap.adjoint ι'.toContinuousLinearMap, fun v => ?_, fun w => ?_⟩
    · refine ext_inner_right ℝ fun w' => ?_
      rw [ContinuousLinearMap.adjoint_inner_left, LinearIsometry.coe_toContinuousLinearMap,
        inner_zero_left]
      exact horth v w'
    · refine ext_inner_right ℝ fun w' => ?_
      rw [ContinuousLinearMap.adjoint_inner_left, LinearIsometry.coe_toContinuousLinearMap,
        LinearIsometry.inner_map_map]
  have hdec : ∀ y, y = ι (A y) + ι' (A' y) := by
    intro y
    obtain ⟨v, w, rfl⟩ := hdecomp y
    simp only [map_add, hAι, hAι', hA'ι, hA'ι', add_zero, zero_add]
  -- Step 1: a chart at `x`
  obtain ⟨V, W, ψ, hVo, hWo, hxW, hψ, hinj, himg, hprop, hfinj⟩ := hN x hx
  obtain ⟨z₀, hz₀V, hψz₀⟩ : x ∈ ψ '' V := by rw [himg]; exact ⟨hxW, hx⟩
  have hψN : ψ '' V ⊆ N := by rw [himg]; exact inter_subset_right
  -- Step 2: the range of `Dψ(z₀)` lies in `range ι`
  have hrange : Set.range (fderiv ℝ ψ z₀) ⊆ Set.range ι := by
    have h := Submission.dsmc_chart_range_subset_tangentSpace (d + k) 2 d N V ψ (by norm_num)
      hVo hψ hψN z₀ hz₀V
    rw [hψz₀] at h
    exact h.trans htan
  -- Step 3: `Φ z = A (ψ z - x)` has injective derivative at `z₀`
  have hψ1 : ContDiffOn ℝ 1 ψ V := hψ.of_le (by norm_num)
  have hψdiff : ∀ z ∈ V, DifferentiableAt ℝ ψ z := fun z hz =>
    (hψ1.differentiableOn_one z hz).differentiableAt (hVo.mem_nhds hz)
  have hΦC : ContDiffOn ℝ 1 (fun z => A (ψ z - x)) V :=
    A.contDiff.comp_contDiffOn (hψ1.sub contDiffOn_const)
  have hΦd : HasFDerivAt (fun z => A (ψ z - x)) (A.comp (fderiv ℝ ψ z₀)) z₀ :=
    A.hasFDerivAt.comp z₀ ((hψdiff z₀ hz₀V).hasFDerivAt.sub_const x)
  have hΦinj : Injective (fderiv ℝ (fun z => A (ψ z - x)) z₀) := by
    rw [hΦd.fderiv, injective_iff_map_eq_zero]
    intro h hh
    obtain ⟨v, hv⟩ := hrange (Set.mem_range_self h)
    rw [ContinuousLinearMap.comp_apply, ← hv, hAι] at hh
    apply hfinj z₀ hz₀V
    rw [← hv, hh, map_zero, map_zero]
  -- Step 4: local inverse `χ` of `Φ`
  obtain ⟨V₀, O, χ, hV₀o, hOo, hz₀V₀, hV₀V, hχC, hχmaps, hΦχ, hχΦ⟩ :=
    Submission.codim1_zsl_gc_local_inverse d (fun z => A (ψ z - x)) V z₀ hVo hz₀V hΦC hΦinj
  have hΦχ' : ∀ a ∈ O, A (ψ (χ a) - x) = a := hΦχ
  have hχΦ' : ∀ z ∈ V₀, A (ψ z - x) ∈ O ∧ χ (A (ψ z - x)) = z := hχΦ
  have hΦz₀ : A (ψ z₀ - x) = 0 := by rw [hψz₀, sub_self, map_zero]
  have h0O : (0 : Euclid d) ∈ O := hΦz₀ ▸ (hχΦ' z₀ hz₀V₀).1
  have hχ0 : χ 0 = z₀ := hΦz₀ ▸ (hχΦ' z₀ hz₀V₀).2
  -- Step 5: the graph identity
  have hkey : ∀ v ∈ O, ψ (χ v) = x + ι v + ι' (A' (ψ (χ v) - x)) := by
    intro v hv
    have h1 := hdec (ψ (χ v) - x)
    rw [hΦχ' v hv] at h1
    rw [add_assoc, ← h1, add_sub_cancel]
  -- Step 6: the radius `s`
  obtain ⟨ε, hε, hεball⟩ := Metric.isOpen_iff.mp hV₀o z₀ hz₀V₀
  obtain ⟨r, hr, hrball⟩ := Metric.isOpen_iff.mp hWo x hxW
  obtain ⟨δ, hδ, hδprop⟩ := Submission.dsmc_chart_inverse_continuity (d + k) d V W ψ
    hψ1.continuousOn hinj (by rw [himg]; exact inter_subset_left) hprop z₀ hz₀V ε hε
  refine ⟨O, fun v => A' (ψ (χ v) - x), min δ r, hOo, h0O, lt_min hδ hr, ?_, ?_, ?_, ?_, ?_⟩
  · exact A'.contDiff.comp_contDiffOn
      ((hψ1.comp hχC (hχmaps.mono_right hV₀V)).sub contDiffOn_const)
  · show A' (ψ (χ 0) - x) = 0
    rw [hχ0, hψz₀, sub_self, map_zero]
  · have hχd : HasFDerivAt χ (fderiv ℝ χ 0) 0 :=
      ((hχC.differentiableOn_one 0 h0O).differentiableAt (hOo.mem_nhds h0O)).hasFDerivAt
    have hψd : HasFDerivAt ψ (fderiv ℝ ψ (χ 0)) (χ 0) :=
      (hψdiff (χ 0) (hχ0 ▸ hz₀V)).hasFDerivAt
    have hud : HasFDerivAt (fun v => A' (ψ (χ v) - x))
        (A'.comp ((fderiv ℝ ψ (χ 0)).comp (fderiv ℝ χ 0))) 0 :=
      A'.hasFDerivAt.comp 0 ((hψd.comp 0 hχd).sub_const x)
    rw [hud.fderiv]
    ext1 h
    obtain ⟨v, hv⟩ := hrange (Set.mem_range_self (fderiv ℝ χ 0 h))
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hχ0, ← hv, hA'ι,
      zero_apply]
  · intro v hv
    show x + ι v + ι' (A' (ψ (χ v) - x)) ∈ N
    rw [← hkey v hv]
    exact hψN (mem_image_of_mem ψ (hV₀V (hχmaps hv)))
  · intro y hy hys
    have hyW : y ∈ W := hrball (mem_ball.mpr (lt_of_lt_of_le hys (min_le_right _ _)))
    obtain ⟨z, hzV, rfl⟩ : y ∈ ψ '' V := by rw [himg]; exact ⟨hyW, hy⟩
    have hzV₀ : z ∈ V₀ := hεball (mem_ball.mpr (hδprop z hzV
      (by rw [hψz₀]; exact lt_of_lt_of_le hys (min_le_left _ _))))
    refine ⟨A (ψ z - x), (hχΦ' z hzV₀).1, ?_⟩
    exact (congrArg ψ (hχΦ' z hzV₀).2).symm.trans (hkey _ (hχΦ' z hzV₀).1)
```

## Key steps

1. Adjoint identities ι*ι = id, ι*ι' = 0, ι'*ι = 0, ι'*ι' = id, and y = ιι*y + ι'ι'*y.
2. Chart ψ at x with ψ(z₀) = x; range Dψ(z₀) ⊆ T_xN ⊆ range ι (dsmc_chart_range_subset_tangentSpace).
3. Φ := ι*(ψ − x) has injective DΦ(z₀) = ι*Dψ(z₀); local_inverse gives V₀, O ∋ 0 and χ with χ(0) = z₀.
4. u := ι'*(ψ∘χ − x) is C¹ on O with u(0) = 0, Du(0) = ι'*Dψ(z₀)Dχ(0) = 0, and ψ(χ(v)) = x + ιv + ι'u(v) ∈ N for v ∈ O.
5. Properness (dsmc_chart_inverse_continuity) gives s > 0 with N ∩ ball(x, s) ⊆ ψ(V₀) = {x + ιv + ι'u(v) : v ∈ O}.

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
