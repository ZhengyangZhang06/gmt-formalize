# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.lipschitz_approx-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.lipschitz_approx-a1.projection_continuity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 8 of the parent proof ("x ↦ P_x is continuous on M (in chart coordinates P_{G_l(a)} = DG_l(a)(DG_l(a)*DG_l(a))^{-1}DG_l(a)*)"). Sibling child used: graph_chart (Submission.codim1_hcp_lsa_c1_graph_chart). Notation: P_x := starProjection of span(tangentSpace M x); A* is the adjoint.

1. (Localization.) Fix x₀ ∈ M; it suffices to prove that x ↦ P_x is continuous within M at x₀. Child graph_chart at x₀ gives pr, G, r, W, Λ with W open, x₀ ∈ W, G C¹ on B_r(0), M ∩ W = G(B_r(0)), pr(G(a) − x₀) = a, pr∘DG(a) = id and tangentSpace M (G a) = range DG(a) for a ∈ B_r(0).
2. (The derivative field.) A(a) := DG(a). Since G is C¹ on the open ball, a ↦ A(a) is continuous on B_r(0) (ContDiffOn.continuousOn_fderiv_of_isOpen). A(a) is injective for a ∈ B_r(0): A(a)u = A(a)v implies u = pr(A(a)u) = pr(A(a)v) = v.
3. (Gram operator.) Γ(a) := A(a)*A(a), a linear endomorphism of ℝ^m. It is injective: if Γ(a)h = 0 then ‖A(a)h‖² = ⟨Γ(a)h, h⟩ = 0, so A(a)h = 0 and h = 0 (step 2). Hence Γ(a) is bijective, i.e. a unit of the complete normed algebra L(ℝ^m) (ContinuousLinearMap.isUnit_iff_bijective).
4. (Projection formula.) For a ∈ B_r(0) let Q(a) := A(a)∘Γ(a)⁻¹∘A(a)* (Γ(a)⁻¹ = Ring.inverse Γ(a)). Since tangentSpace M (G a) = range A(a) is already a linear subspace, span(tangentSpace M (G a)) = range A(a). For u ∈ ℝ^P, Q(a)u ∈ range A(a), and for every w = A(a)h ∈ range A(a): ⟨u − Q(a)u, A(a)h⟩ = ⟨A(a)*u − Γ(a)Γ(a)⁻¹A(a)*u, h⟩ = 0. By the characterization of the orthogonal projection (Submodule.eq_starProjection_of_mem_of_inner_eq_zero), P_{G(a)}u = Q(a)u. Thus P_{G(a)} = Q(a).
5. (Continuity of Q.) On B_r(0): a ↦ A(a) is continuous (step 2); a ↦ A(a)* is continuous (the adjoint is a linear isometry); compositions of continuous operator-valued maps are continuous (ContinuousOn.clm_comp), so a ↦ Γ(a) is continuous; inversion is continuous at every unit (NormedRing.inverse_continuousAt), so a ↦ Γ(a)⁻¹ is continuous on B_r(0); hence Q is continuous on B_r(0).
6. (Transport to M ∩ W.) For x ∈ M ∩ W we have x = G(a) with a ∈ B_r(0), and then a = pr(G(a) − x₀) = pr(x − x₀). Hence pr(x − x₀) ∈ B_r(0) and P_x = Q(pr(x − x₀)) for all x ∈ M ∩ W (step 4). The map x ↦ pr(x − x₀) is continuous and maps M ∩ W into B_r(0), so x ↦ Q(pr(x − x₀)) is continuous on M ∩ W, and so is x ↦ P_x.
7. (Conclusion.) W is an open neighbourhood of x₀, so M ∩ W ∈ 𝓝[M] x₀ and continuity within M ∩ W at x₀ gives continuity within M at x₀ (ContinuousWithinAt.mono_of_mem_nhdsWithin). As x₀ ∈ M was arbitrary, x ↦ P_x is continuous on M. ∎

Formal check (scratch validation by the decomposition author; not part of the frozen contract). The tactic proof below of `theorem Submission.codim1_hcp_lsa_tangent_projection_continuousOn : <exactly the frozen lean_statement> := by`, after `import GMT.Ch07.Submission` inside `namespace GMT.Ch07` with the contract's opens and with the sibling Submission.codim1_hcp_lsa_c1_graph_chart present with its frozen type, compiled with Lean v4.35.0-rc3 / Mathlib 25730c7c; #print axioms: propext, Classical.choice, Quot.sound and that sibling.
```lean
  intro P m M hM x₀ hx₀
  obtain ⟨pr, G, r, W, Λ, hr, hWo, hpW, hpr, hG0, hGc, hGL, hMW, hleft, hderiv, htan⟩ :=
    Submission.codim1_hcp_lsa_c1_graph_chart P m M x₀ hM hx₀
  set A : Euclid m → (Euclid m →L[ℝ] Euclid P) := fun a => fderiv ℝ G a with hA
  have hAc : ContinuousOn A (ball 0 r) := hGc.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  -- the Gram operator `Γ a = A aᴴ ∘ A a`
  set Γ : Euclid m → (Euclid m →L[ℝ] Euclid m) := fun a =>
    (ContinuousLinearMap.adjoint (A a)).comp (A a) with hΓ
  have hAinj : ∀ a ∈ ball (0 : Euclid m) r, Function.Injective (A a) := by
    intro a ha u v huv
    have := congrArg pr huv
    have h1 := congrArg (fun L => L u) (hderiv a ha)
    have h2 := congrArg (fun L => L v) (hderiv a ha)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h1 h2
    rw [← h1, ← h2]; exact this
  have hΓunit : ∀ a ∈ ball (0 : Euclid m) r, IsUnit (Γ a) := by
    intro a ha
    rw [ContinuousLinearMap.isUnit_iff_bijective]
    have hinj : Function.Injective (Γ a) := by
      intro u v huv
      have h0 : Γ a (u - v) = 0 := by rw [map_sub, huv, sub_self]
      have h1 : inner ℝ (Γ a (u - v)) (u - v) = ‖A a (u - v)‖ ^ 2 := by
        simp only [hΓ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
        exact real_inner_self_eq_norm_sq _
      rw [h0, inner_zero_left] at h1
      have h2 : A a (u - v) = 0 := by
        have : ‖A a (u - v)‖ = 0 := by nlinarith [norm_nonneg (A a (u - v))]
        exact norm_eq_zero.1 this
      have h3 : u - v = 0 := hAinj a ha (by rw [h2, map_zero])
      exact sub_eq_zero.1 h3
    exact ⟨hinj, (LinearMap.injective_iff_surjective (f := ((Γ a : Euclid m →L[ℝ] Euclid m) :
      Euclid m →ₗ[ℝ] Euclid m))).1 hinj⟩
  -- the projection formula `P_{G a} = A a ∘ (Γ a)⁻¹ ∘ A aᴴ`
  set Q : Euclid m → (Euclid P →L[ℝ] Euclid P) := fun a =>
    (A a).comp ((Ring.inverse (Γ a)).comp (ContinuousLinearMap.adjoint (A a))) with hQ
  have hQeq : ∀ a ∈ ball (0 : Euclid m) r,
      (Submodule.span ℝ (tangentSpace M (G a))).starProjection = Q a := by
    intro a ha
    have hspan : Submodule.span ℝ (tangentSpace M (G a)) =
        LinearMap.range ((A a : Euclid m →L[ℝ] Euclid P) : Euclid m →ₗ[ℝ] Euclid P) := by
      apply le_antisymm
      · rw [Submodule.span_le, htan a ha]
        rintro _ ⟨y, rfl⟩
        exact ⟨y, rfl⟩
      · rintro _ ⟨y, rfl⟩
        apply Submodule.subset_span
        rw [htan a ha]
        exact ⟨y, rfl⟩
    have hinvr : Γ a * Ring.inverse (Γ a) = 1 := Ring.mul_inverse_cancel _ (hΓunit a ha)
    ext1 u
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
    · rw [hspan]
      exact ⟨_, rfl⟩
    · intro w hw
      rw [hspan] at hw
      obtain ⟨h, rfl⟩ := hw
      simp only [hQ, ContinuousLinearMap.coe_coe]
      rw [inner_sub_left, ← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.adjoint_inner_left]
      have : ContinuousLinearMap.adjoint (A a) ((A a).comp ((Ring.inverse (Γ a)).comp
          (ContinuousLinearMap.adjoint (A a))) u) = ContinuousLinearMap.adjoint (A a) u := by
        have h4 := congrArg (fun L : Euclid m →L[ℝ] Euclid m => L (ContinuousLinearMap.adjoint (A a) u)) hinvr
        simpa [hΓ, ContinuousLinearMap.mul_apply] using h4
      rw [this, sub_self]
  -- continuity of `Q` on the ball
  have hQc : ContinuousOn Q (ball 0 r) := by
    have hadj : ContinuousOn (fun a => ContinuousLinearMap.adjoint (A a)) (ball 0 r) :=
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Euclid m) (F := Euclid P)).continuous.comp_continuousOn hAc
    have hΓc : ContinuousOn Γ (ball 0 r) := hadj.clm_comp hAc
    have hinv : ContinuousOn (fun a => Ring.inverse (Γ a)) (ball 0 r) := by
      intro a ha
      obtain ⟨u, hu⟩ := hΓunit a ha
      have := NormedRing.inverse_continuousAt u
      rw [hu] at this
      exact this.comp_continuousWithinAt (hΓc a ha)
    exact hAc.clm_comp (hinv.clm_comp hadj)
  -- transport to `M ∩ W`
  have hPQ : ∀ x ∈ M ∩ W, (Submodule.span ℝ (tangentSpace M x)).starProjection = Q (pr (x - x₀)) := by
    intro x hx
    rw [hMW] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [hleft a ha]
    exact hQeq a ha
  have hcont : ContinuousOn (fun x => Q (pr (x - x₀))) (M ∩ W) := by
    refine hQc.comp (by fun_prop) fun x hx => ?_
    have hx' := hx
    rw [hMW] at hx'
    obtain ⟨a, ha, rfl⟩ := hx'
    rw [hleft a ha]; exact ha
  have hcont' : ContinuousOn (fun x => (Submodule.span ℝ (tangentSpace M x)).starProjection) (M ∩ W) :=
    hcont.congr hPQ
  exact (hcont' x₀ ⟨hx₀, hpW⟩).mono_of_mem_nhdsWithin (inter_mem_nhdsWithin M (hWo.mem_nhds hpW))
```

Integration check: this proof was also compiled together with the proofs of all eight new sibling children and the assembly of the parent theorem in a single file (only the four reused accepted declarations taken as axioms); the file compiled without errors or `sorry`.

## Key steps

1. Near x₀ use a graph chart: x = G(a) with a = pr(x − x₀), and T_xM = range DG(a), where DG is continuous and injective.
2. Gram formula: P_{G(a)} = A(A*A)⁻¹A* with A = DG(a), by the orthogonality characterization of the projection.
3. a ↦ A(a)(A(a)*A(a))⁻¹A(a)* is continuous, because the adjoint is an isometry and inversion is continuous at units.
4. Compose with x ↦ pr(x − x₀) on M ∩ W and localize.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; sha256sum GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `sed -n 1,457p GMT/Ch07/Contract.lean (Euclid, IsEmbeddedSubmanifold, tangentSpace, μHE usage)`
- `python3 scans of dag.json: selected node (depth 5, max_depth 6), parent hypercone_plane and its decomposition-v1.json, accepted nodes whose statements mention Lipschitz/mollif/convol/graph chart/starProjection/tangentSpace, lean_name collision scan for codim1_hcp_lsa_*`
- `runtime.py: _decompose (max_depth), _existing_lean_name_problem (reuse of accepted declarations by identical name and type)`
- `git show <candidate>:GMT/Ch07/Submission.lean for 93f7ea7a3650 (codim1_rdo_gc_local_inverse_c2, dsmc_chart_inverse_continuity), d25d2377 (codim1_zsl_pc_mollify_indicator_l1), and the handoffs of codim1_zsl_gc_local_inverse and dsmc_chart_inverse_continuity`
- `grep -rn in local-references/123e8435b4a2469b/mathlib/Mathlib: euclideanHausdorffMeasure, ae_differentiableWithinAt_of_mem, LipschitzWith.ae_differentiableAt, measurable_fderiv, tangentConeAt, HasFDerivWithinAt.unique_on, mem_tangentConeAt_of_seq, hasFDerivAt_convolution_left, contDiff_convolution_left, ae_convolution_tendsto_right_of_locallyIntegrable, LocallyLipschitzOn.exists_lipschitzOnWith_of_compact, LocallyLipschitzOn.mul, exists_isSubordinate, exists_contDiff_support_eq_eq_one_iff, sq_sum_le_card_mul_sum_sq, measurePreserving_sub_left`
- `lean #check probes in the GMT.Ch07.Submission import closure (Imp*.lean, Inst5.lean): SmoothPartitionOfUnity.exists_isSubordinate, ContDiffBump API, ContDiffBump.normed (missing), VitaliFamily.ae_tendsto_average_norm_sub, Besicovitch.tendsto_filterAt, tendsto_integral_smul_of_tendsto_average_norm_sub, aestronglyMeasurable_iUnion_iff, Submodule.eq_starProjection_of_mem_of_inner_eq_zero, NormedRing.inverse_continuousAt, instances HasContDiffBump/HasBesicovitchCovering (Euclid m)`
- `lean -DautoImplicit=false /tmp/lsa-split/check/{TypesAll,Assembly,N1,N2,N3,N4,N5,N6,N7,N8,Integration}.lean (LEAN_PATH = .lake/build/lib/lean plus every package's .lake/build/lib/lean)`
- `git for-each-ref | xargs git grep -l codim1_hcp_lsa -- 'GMT/*.lean' (no match); grep codim1_hcp_lsa dag.json (0); grep -rn codim1_hcp_lsa simongmt (no match)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-e9797ac1a5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-b5d5990773/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-2511ff6312/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ch-0f11358db9/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-252c8df06c56/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/TangentCone/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Uniform.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/tmp/lsa-split/check/TypesAll.lean`
- `/tmp/lsa-split/check/Assembly.lean`
- `/tmp/lsa-split/check/Integration.lean`

Pins match: manifest project b4d606db and Mathlib 25730c7c equal workspace HEAD and .lake/packages/mathlib, and the snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…). The node has depth 5 with max_depth 6, so the children are leaves. Reuse: four accepted declarations (chart_tangentSpace_eq_range_fderiv, dimred_rpd_embedded_locally_closed, codim1_zsl_gc_local_inverse, dsmc_chart_inverse_continuity) are taken with byte-identical frozen types. The C² graph-chart and tangent-projection lemmas (codim1_rdo_gc_graph_over_tangent, submanifold_tangentProjection_c1_extension, dor_lmb_ret_tangent_projection) do not apply to C¹ M. No C¹ graph chart, Rademacher-on-M, tangent-projection continuity or L²-gradient mollification lemma exists in the DAG, SimonGMT or the snapshot, and the 8 codim1_hcp_lsa_ names are unused everywhere. Mathlib in the Submission import closure provides Rademacher (LipschitzOnWith.ae_differentiableWithinAt_of_mem), measurable_fderiv, HasFDerivWithinAt.unique_on with mem_tangentConeAt_of_seq, LipschitzOnWith.hausdorffMeasure_image_le with EuclideanSpace.euclideanHausdorffMeasure_eq_volume, convolution smoothness, ContDiffBump, Besicovitch Lebesgue differentiation, SmoothPartitionOfUnity and exists_contDiff_support_eq_eq_one_iff. It lacks ContDiffBump.normed, ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable and sq_sum_le_card_mul_sum_sq; the mollify proof rebuilds the first two by hand, and the assembly uses Finset.sum_mul_sq_le_sq_mul_sq. Lean: all 12 child types elaborate. The selected type is kernel-checked from the child types as axioms. Every new child is proved from exactly its declared siblings. The integrated file (8 proofs plus assembly, only the 4 reused declarations as axioms) compiles without errors or sorry.
