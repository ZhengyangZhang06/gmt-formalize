# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_coarea-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_coarea-a1.chart_patch-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent step 4 (one patch: Φ := ψ∘Ψ, Ŷ := Θ(Y_q) = B ∩ Ψ^{−1}(Y_q), ψ(Y_q) = Φ(Ŷ) and ψ(Y_q ∩ F^{−1}(s)) = Φ(Ŷ ∩ {w(0) = s})) together with the hypothesis check of step 6 (⟨u, DΦ(w)e_l⟩ = DF(y)DΨ(w)e_l = ∂_l(F∘Ψ)(w)); the patch identity itself is the sibling param_coarea. Departure: as in straightening_cover the straightened coordinate is the first one (F(Ψ(w)) = w(0)), and the patch is described as S := B ∩ Ψ^{−1}(Z) for an arbitrary Borel Z ⊆ V ∩ Ψ(B).

Conventions: ℝ^k = Euclid k = EuclideanSpace ℝ (Fin k); e_k := EuclideanSpace.single k 1 is the k-th standard basis vector; for v ∈ ℝ^{n+1}, v(0) = v 0 (Lean `v.ofLp 0`) is its 0-th coordinate, while e_k always denotes a basis vector; DΦ(w) := fderiv ℝ Φ w; Hᵏ := μHE[k]; |v| := ‖v‖ and |v|ₑ := ‖v‖ₑ = ofReal ‖v‖; all integrals are lower integrals in [0, ∞].

1. (Differentiability.) Ψ is differentiable at every w ∈ B and ψ at every y ∈ V (C¹ on open sets: ContDiffOn.differentiableOn and IsOpen.mem_nhds).
2. (S is Borel.) Let S := B ∩ Ψ^{−1}(Z) and let Ψ̃ equal Ψ on B and 0 off B. Ψ is continuous on the open (Borel) set B, so Ψ̃ is Borel (ContinuousOn.measurable_piecewise), and S = B ∩ Ψ̃^{−1}(Z) is Borel.
3. (Φ := ψ∘Ψ on S.) Let w ∈ S; then Ψ(w) ∈ Z ⊆ V. By the chain rule Φ is differentiable at w with DΦ(w) = Dψ(Ψ(w))∘DΨ(w); it is injective since Dψ(Ψ(w)) is injective (Ψ(w) ∈ V) and DΨ(w) is bijective. Φ is injective on S: Φ(a) = Φ(b) gives Ψ(a) = Ψ(b) (ψ injective on V) and then a = b (Ψ injective on B).
4. (D(F∘Ψ) is the first coordinate on B.) Let w ∈ B. On the open neighbourhood B of w, F∘Ψ coincides with the continuous linear map π_0 : v ↦ v(0) (EuclideanSpace.proj 0), so D(F∘Ψ)(w) = π_0 (Filter.EventuallyEq.fderiv_eq; a continuous linear map is its own derivative). F is differentiable everywhere and Ψ at w, so by the chain rule DF(Ψ(w))(DΨ(w)e) = e(0) for every e ∈ ℝ^{n+1}.
5. (Hypotheses of param_coarea.) Let w ∈ S and y := Ψ(w) ∈ Z. (a) By hypothesis G(ψ(y)) = Dψ(y)v for some v; DΨ(w) is surjective, so v = DΨ(w)u for some u, and G(Φ(w)) = Dψ(y)(DΨ(w)u) = DΦ(w)u ∈ DΦ(w)(ℝ^{n+1}). (b) For every e: ⟨G(Φ(w)), DΦ(w)e⟩ = ⟨G(ψ(y)), Dψ(y)(DΨ(w)e)⟩ = DF(y)(DΨ(w)e) = e(0), by the hypothesis on G and step 4.
6. (Apply param_coarea.) By param_coarea with Φ, S, G and φ (hypotheses: steps 2, 3, 5): t ↦ ∫_{Φ(S ∩ {w : w(0) = t})} φ dHⁿ is a.e.-measurable and ∫_ℝ ∫_{Φ(S ∩ {w(0) = t})} φ dHⁿ dt = ∫_{Φ(S)} |G|ₑ·φ dH^{n+1}.
7. (Back to the chart.) Ψ(S) = Z: Ψ(S) ⊆ Z by definition; if y ∈ Z ⊆ Ψ(B) then y = Ψ(w) with w ∈ B, and w ∈ S. Hence Φ(S) = ψ(Ψ(S)) = ψ(Z). For t ∈ ℝ, Ψ(S ∩ {w(0) = t}) = Z ∩ F^{−1}(t), because F(Ψ(w)) = w(0) for w ∈ B (same two inclusions). Hence Φ(S ∩ {w(0) = t}) = ψ(Z ∩ F^{−1}(t)).
8. Substituting step 7 into step 6 gives both claims. ∎

Formal check (scratch validation by the decomposition author; not part of the frozen contract). The tactic proof below, for `theorem Submission.dor_lmbsf_pc_chart_patch_coarea : <exactly the frozen lean_statement> := by`, compiled with Lean v4.35.0-rc3 and Mathlib 25730c7c as a single theorem inserted into GMT/Ch07/Submission.lean (namespace GMT.Ch07, frozen imports only) after the declarations of its dependencies (codim1_lura_gram_area_formula, dor_lmbsf_pc_gram_det_succ_eq, dor_lmbsf_pc_slice_area_tonelli, dor_lmbsf_pc_param_coarea), with no helper declaration and no set_option; it also compiles under maxHeartbeats 70000, and the controller's leaf gate (leaf_verification.check_source_delta) accepts the insertion. #print axioms of the assembled selected theorem reports propext, Classical.choice and Quot.sound.
```lean
  have h3 := Submission.dor_lmbsf_pc_param_coarea
  intro P n V B Z ψ F Ψ G hV hψ hψinj hψreg hF hB hΨ hΨinj hΨbij hFΨ hZ hZV hZB hG φ hφ
  have hΨd : ∀ w ∈ B, DifferentiableAt ℝ Ψ w := fun w hw =>
    (hΨ.differentiableOn one_ne_zero w hw).differentiableAt (hB.mem_nhds hw)
  have hψd : ∀ y ∈ V, DifferentiableAt ℝ ψ y := fun y hy =>
    (hψ.differentiableOn one_ne_zero y hy).differentiableAt (hV.mem_nhds hy)
  set S : Set (Euclid (n + 1)) := B ∩ Ψ ⁻¹' Z with hSdef
  have hSm : MeasurableSet S := by
    classical
    have hpw : Measurable (B.piecewise Ψ (fun _ => 0)) :=
      hΨ.continuousOn.measurable_piecewise continuousOn_const hB.measurableSet
    have : S = B ∩ (B.piecewise Ψ (fun _ => 0)) ⁻¹' Z := by
      ext w
      constructor
      · rintro ⟨hw, hwZ⟩
        exact ⟨hw, by simpa [Set.piecewise_eq_of_mem _ _ _ hw] using hwZ⟩
      · rintro ⟨hw, hwZ⟩
        exact ⟨hw, by simpa [Set.piecewise_eq_of_mem _ _ _ hw] using hwZ⟩
    rw [this]
    exact hB.measurableSet.inter (hpw hZ)
  set Φ : Euclid (n + 1) → Euclid P := ψ ∘ Ψ with hΦdef
  have hSZ : ∀ w ∈ S, Ψ w ∈ Z := fun w hw => hw.2
  have hΦd : ∀ w ∈ S, DifferentiableAt ℝ Φ w := fun w hw =>
    (hψd _ (hZV (hSZ w hw))).comp w (hΨd w hw.1)
  have hΦD : ∀ w ∈ S, fderiv ℝ Φ w = (fderiv ℝ ψ (Ψ w)).comp (fderiv ℝ Ψ w) := fun w hw =>
    fderiv_comp w (hψd _ (hZV (hSZ w hw))) (hΨd w hw.1)
  have hΦinjD : ∀ w ∈ S, Injective (fderiv ℝ Φ w) := by
    intro w hw
    rw [hΦD w hw]
    exact (hψreg _ (hZV (hSZ w hw))).comp (hΨbij w hw.1).1
  have hΦinj : InjOn Φ S := by
    intro a ha b hb hab
    exact hΨinj ha.1 hb.1 (hψinj (hZV (hSZ a ha)) (hZV (hSZ b hb)) hab)
  have hDFΨ : ∀ w ∈ B, ∀ e : Euclid (n + 1), fderiv ℝ F (Ψ w) (fderiv ℝ Ψ w e) = e 0 := by
    intro w hw e
    have h1 : fderiv ℝ (F ∘ Ψ) w = fderiv ℝ (EuclideanSpace.proj (0 : Fin (n + 1)) : Euclid (n + 1) → ℝ) w := by
      apply Filter.EventuallyEq.fderiv_eq
      filter_upwards [hB.mem_nhds hw] with v hv
      simp [hFΨ v hv]
    have h2 : fderiv ℝ (F ∘ Ψ) w = (fderiv ℝ F (Ψ w)).comp (fderiv ℝ Ψ w) :=
      fderiv_comp w ((hF.differentiable one_ne_zero) _) (hΨd w hw)
    rw [h2, ContinuousLinearMap.fderiv] at h1
    have := congrArg (fun L : Euclid (n + 1) →L[ℝ] ℝ => L e) h1
    simpa using this
  have hGΦ : ∀ w ∈ S, G (Φ w) ∈ LinearMap.range (fderiv ℝ Φ w : Euclid (n + 1) →ₗ[ℝ] Euclid P) ∧
      ∀ e : Euclid (n + 1), inner ℝ (G (Φ w)) (fderiv ℝ Φ w e) = e 0 := by
    intro w hw
    obtain ⟨⟨v, hv⟩, hinner⟩ := hG (Ψ w) (hSZ w hw)
    refine ⟨?_, ?_⟩
    · obtain ⟨u, hu⟩ := (hΨbij w hw.1).2 v
      refine ⟨u, ?_⟩
      have hv' : fderiv ℝ ψ (Ψ w) v = G (ψ (Ψ w)) := hv
      change fderiv ℝ Φ w u = G (Φ w)
      rw [hΦD w hw, ContinuousLinearMap.comp_apply, hu, hv']
      rfl
    · intro e
      rw [hΦD w hw, ContinuousLinearMap.comp_apply]
      change inner ℝ (G (ψ (Ψ w))) _ = _
      rw [hinner, hDFΨ w hw.1 e]
  obtain ⟨hmeas, heq⟩ := h3 P n Φ S G hSm hΦd hΦinjD hΦinj hGΦ φ hφ
  have himg : Φ '' S = ψ '' Z := by
    rw [hΦdef, image_comp]
    congr 1
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩; exact hw.2
    · intro hy
      obtain ⟨w, hw, rfl⟩ := hZB hy
      exact ⟨w, ⟨hw, hy⟩, rfl⟩
  have himgt : ∀ t : ℝ, Φ '' (S ∩ {w | w 0 = t}) = ψ '' (Z ∩ F ⁻¹' {t}) := by
    intro t
    rw [hΦdef, image_comp]
    congr 1
    ext y
    constructor
    · rintro ⟨w, ⟨⟨hwB, hwZ⟩, hwt⟩, rfl⟩
      refine ⟨hwZ, ?_⟩
      simp only [mem_preimage, mem_singleton_iff, hFΨ w hwB]
      exact hwt
    · rintro ⟨hy, hFy⟩
      obtain ⟨w, hw, rfl⟩ := hZB hy
      refine ⟨w, ⟨⟨hw, hy⟩, ?_⟩, rfl⟩
      simp only [mem_preimage, mem_singleton_iff, hFΨ w hw] at hFy
      exact hFy
  simp only [himgt] at hmeas heq
  rw [himg] at heq
  exact ⟨hmeas, heq⟩
```

## Key steps

1. S := B ∩ Ψ^{-1}(Z) is Borel; Φ := ψ∘Ψ is differentiable on S with DΦ = Dψ(Ψ)∘DΨ injective, and Φ is injective on S.
2. F∘Ψ equals the first-coordinate projection on the open set B, so DF(Ψ(w))∘DΨ(w) = (e ↦ e(0)).
3. Hence G∘Φ lies in range DΦ (DΨ surjective) and ⟨G(Φ(w)), DΦ(w)e⟩ = e(0) on S.
4. param_coarea for (Φ, S, G), and Φ(S) = ψ(Z), Φ(S ∩ {w(0) = t}) = ψ(Z ∩ F^{-1}(t)).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; python3 read of <snapshot>/project/lake-manifest.json; git rev-parse HEAD and git -C .lake/packages/{mathlib,simongmt} rev-parse HEAD`
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `grep -n '^theorem' simongmt Chapter02/{WeightedArea,CoareaLinear,CoareaProjection,CoareaLinearAlgebra}.lean; cat Chapter02/{Area,AreaParametrization,WeightedArea,CoareaProjection,CoareaLinear}.lean; sed AreaApproximation.lean, AreaCritical.lean`
- `grep -rln 'coarea|Coarea|co-area' simongmt/Poincare/SimonGMT (only the Chapter02 linear and projection co-area files plus mentions in Chapter03; no nonlinear co-area formula)`
- `Lean probe after import GMT.Ch07.Submission in the contract scope: #check weighted_area_formula_of_injective_derivative, areaJacobianAt, LinearMap.normDet, Matrix.gram, ContDiffAt.toOpenPartialHomeomorph (unknown); lintegral_image_eq_lintegral_abs_det_fderiv_mul, HasStrictFDerivAt.toOpenPartialHomeomorph, OpenPartialHomeomorph.contDiffAt_symm, volume_preserving_piFinSuccAbove, PiLp.volume_preserving_ofLp, Measurable.lintegral_prod_right', lintegral_iUnion, lintegral_tsum, MeasurableSet.image_of_continuousOn_injOn, ContinuousOn.measurable_piecewise, measurable_fderiv, Matrix.det_succ_row_zero, TopologicalSpace.isOpen_iUnion_countable, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn (available)`
- `grep -rnE 'theorem (adjugate_fin_succ_eq_det_submatrix|adjugate_mul |isOpen_iUnion_countable|Countable.exists_eq_range|eq_self_or_eq_succAbove|surjective_of_injective|Filter.EventuallyEq.fderiv_eq|measurable_fderiv |MeasurableSet.image_of_continuousOn_injOn|lintegral_iUnion |lintegral_tsum|Measurable.lintegral_prod_right'|ContinuousOn.measurable_piecewise|normDet_sq_eq_det_gram|lintegral_prod |lintegral_indicator )' <snapshot>/mathlib/Mathlib; grep 'volume_preserving_piFinSuccAbove|PiLp.volume_preserving_ofLp|PiLp.volume_preserving_toLp' <snapshot>/mathlib/Mathlib`
- `python3 -I scans of dag.json (1527 nodes): regex 'co-?area|Gram|straighten|implicit function|inverse function|Tonelli|areaJacobianAt|normDet|level set' over statements; accepted nodes matching 'Fin.cons|insertNth|piFinSuccAbove|∫⁻ t, ∫⁻|HasStrictFDerivAt|Pairwise|disjoint'; status and candidate_commit of codim1_lura_gram_area_formula, codim1_zsl_gc_local_inverse, codim1_lura_lintegral_image_eq_tsum_pieces, dtc_bc_lr_local_inverse; lean_name collision check for dor_lmbsf_pc_* (none); cross-parent reuse edges (562)`
- `git grep dor_lmbsf_pc_ over all refs (no match); git show 58ab3bbd:GMT/Ch07/Submission.lean (the proof base is the bare frozen contract)`
- `git show d5ba41d6:GMT/Ch07/Submission.lean and git show 013681e4:GMT/Ch07/Submission.lean, then lake env lean with #print axioms (propext, Classical.choice, Quot.sound); git log -1 d5ba41d6 (frozen-import leaf gate)`
- `read _recursive_lean/leaf_verification.py (check_source_delta), parent_verification.py, runtime.py (_existing_lean_name_problem, reuse of accepted children by lean_name), verifier/gmt-compare.py (contract_scope, child_modules), verifier/lean_contract.py`
- `lake env lean /tmp/pc-decomp/v1/{Types,Assembly,Leaves1,Leaves2,Leaves3}.lean, /tmp/pc-decomp/v2/Combined.lean, /tmp/pc-decomp/v2/cmp/*_Challenge.lean, /tmp/pc-decomp/v3/{Submission,SubmissionHB}.lean; python3 check_source_delta on each new leaf insertion`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaParametrization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/CoareaProjection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinearAlgebra.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Adjugate.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-ec35f2137a/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-db95546c3f/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-2511ff6312/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-5d8d9c70c5/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-rectifiab-d698709751/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-15bd82d86f30/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-15bd82d86f30/_recursive_lean/runtime.py`
- `/tmp/pc-decomp/v1/Types.lean`
- `/tmp/pc-decomp/v1/Assembly.lean`
- `/tmp/pc-decomp/v2/Combined.lean`
- `/tmp/pc-decomp/v3/Submission.lean`

Pins match. The snapshot manifest gives project b4d606d and Mathlib 25730c7c; its lake-manifest gives simongmt 2b366308. Workspace HEAD and .lake/packages agree. Snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical.

What exists. Snapshot Mathlib has every library fact the children use:
- adjugate_mul and adjugate_fin_succ_eq_det_submatrix (LinearAlgebra/Matrix/Adjugate.lean:268, 366);
- volume_preserving_piFinSuccAbove (Constructions/Pi.lean:818);
- PiLp.volume_preserving_ofLp and PiLp.volume_preserving_toLp (Haar/InnerProductSpace.lean:134, 139);
- Measurable.lintegral_prod_right' and lintegral_prod (Measure/Prod.lean:123, 1009);
- lintegral_indicator and lintegral_iUnion (Lebesgue/Basic.lean:510, 597), and lintegral_tsum (Lebesgue/Add.lean:362);
- ContinuousOn.measurable_piecewise (BorelSpace/Basic.lean:523) and MeasurableSet.image_of_continuousOn_injOn (Polish/Basic.lean:821);
- measurable_fderiv (FDeriv/Measurable.lean:378) and Filter.EventuallyEq.fderiv_eq (FDeriv/Congr.lean:260);
- Fin.eq_self_or_eq_succAbove (Fin/Tuple/Basic.lean:841) and LinearMap.surjective_of_injective (FiniteDimensional/Basic.lean:291);
- TopologicalSpace.isOpen_iUnion_countable (Topology/Bases.lean:932) and Set.Countable.exists_eq_range (Set/Countable.lean:149).

What is missing. SimonGMT has no nonlinear co-area formula; Chapter02 has only the linear and projection co-area formulas. Its weighted area formula (WeightedArea.lean:76, 120), normDet and areaJacobianAt are not available under the frozen imports, and leaf proofs may not add imports (leaf_verification.check_source_delta). The child types therefore use Gram determinants.

DAG. Two accepted declarations are reused with byte-identical types: codim1_lura_gram_area_formula (candidate d5ba41d6) and codim1_zsl_gc_local_inverse (candidate 013681e4). Fresh compiles of both print only propext, Classical.choice and Quot.sound, and runtime._existing_lean_name_problem permits sharing accepted nodes. The six new dor_lmbsf_pc_* names occur in no dag.json node and in no ref. The related nodes dtc_bc_lc_sl_chart_coarea, dimred_cs_sos_spine_coarea and dtc_bc_lc_sl_coarea are unaccepted and have different types.

Lean. All 8 child types pass validate_lean_statement, and their gmt-compare challenge modules elaborate. The integrated /tmp/pc-decomp/v3/Submission.lean proves the exact frozen selected type from the reused proofs and from prototype proofs of all six new children, with axioms propext, Classical.choice and Quot.sound. Each new prototype passes check_source_delta and fits in 70000 heartbeats.
