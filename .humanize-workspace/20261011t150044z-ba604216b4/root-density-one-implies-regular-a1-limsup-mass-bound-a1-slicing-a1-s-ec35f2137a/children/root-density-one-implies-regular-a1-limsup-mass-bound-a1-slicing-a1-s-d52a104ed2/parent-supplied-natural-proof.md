# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_coarea-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_coarea-a1.straightening_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent step 2 (local straightening of F by the inverse function theorem near each point with ∇F ≠ 0, and a countable subcover by Lindelöf). Departures: (i) instead of keeping coordinate i in place (Θ(y)_l = y_l for l ≠ i, Θ(y)_i = F(y) in the supplied proof), F is put in the first coordinate and the remaining coordinates follow, Θ(y) = (F(y), y(i.succAbove 0), …, y(i.succAbove (n−1))), so every patch is straightened to the first coordinate, the convention of slice_tonelli and param_coarea; (ii) no box is needed: a patch is the open target O of the inverse function theorem, and the parent assembly forms the disjoint patches Y_q itself (via `disjointed`).

Conventions: ℝ^k = Euclid k = EuclideanSpace ℝ (Fin k); e_k := EuclideanSpace.single k 1 is the k-th standard basis vector; for v ∈ ℝ^{n+1}, v(0) = v 0 (Lean `v.ofLp 0`) is its 0-th coordinate, while e_k always denotes a basis vector; DΦ(w) := fderiv ℝ Φ w; Hᵏ := μHE[k]; |v| := ‖v‖ and |v|ₑ := ‖v‖ₑ = ofReal ‖v‖; all integrals are lower integrals in [0, ∞].

1. (A good coordinate.) Let y₀ ∈ ℝ^{n+1} with DF(y₀) ≠ 0. There is i ∈ {0, …, n} with DF(y₀)e_i ≠ 0: otherwise DF(y₀)v = Σ_j v_j·DF(y₀)e_j = 0 for every v (v = Σ_j v_j e_j), i.e. DF(y₀) = 0.
2. (The straightening map.) Let L : ℝ^{n+1} → ℝ^{n+1}, L(y) := (0, y(i.succAbove 0), …, y(i.succAbove (n−1))) = WithLp.toLp 2 (Fin.cons 0 (k ↦ y(i.succAbove k))); L is linear (check coordinatewise, Fin.cases), hence a continuous linear map. Let Θ(y) := F(y)·e_0 + L(y). Then Θ(y)(0) = F(y) and Θ(y)(k+1) = y(i.succAbove k). Θ is C¹ (F is C¹ and L is linear) with DΘ(y)h = (DF(y)h)·e_0 + L(h) (HasFDerivAt.smul_const, HasFDerivAt.add).
3. (DΘ(y₀) is injective.) Let DΘ(y₀)h = 0. Coordinate k+1 gives h(i.succAbove k) = 0 for every k < n. Every index j is i or i.succAbove k for some k (Fin.eq_self_or_eq_succAbove), so h = h(i)·e_i. Coordinate 0 gives 0 = DF(y₀)h = h(i)·DF(y₀)e_i, so h(i) = 0 by step 1, i.e. h = 0. As DΘ(y₀) is linear, it is injective.
4. (Local inverse.) Apply the sibling local_inverse with d := n + 1, φ := Θ, V := ℝ^{n+1} (open, contains y₀, Θ is C¹ on it) and z₀ := y₀. It gives open sets V₀ ∋ y₀ and O and a map χ, C¹ on O, with χ(O) ⊆ V₀, Θ(χ(a)) = a for a ∈ O, and Θ(z) ∈ O and χ(Θ(z)) = z for z ∈ V₀.
5. (Properties of (O, χ).) (a) χ is injective on O: χ(a) = χ(b) gives a = Θ(χ(a)) = Θ(χ(b)) = b. (b) χ(O) = V₀: ⊆ holds by step 4; if z ∈ V₀ then z = χ(Θ(z)) with Θ(z) ∈ O. So χ(O) is open and contains y₀. (c) For a ∈ O: F(χ(a)) = Θ(χ(a))(0) = a(0). (d) For a ∈ O: χ is differentiable at a (C¹ on the open set O), Θ is differentiable at χ(a), and Θ∘χ = id on the neighbourhood O of a, so D(Θ∘χ)(a) = D(id)(a) = id (Filter.EventuallyEq.fderiv_eq). By the chain rule DΘ(χ(a))∘Dχ(a) = id, so Dχ(a) is injective, and an injective linear endomorphism of the finite-dimensional space ℝ^{n+1} is surjective (LinearMap.surjective_of_injective); so Dχ(a) is bijective.
 Thus every y₀ in O' := {y : DF(y) ≠ 0} has data (B_{y₀}, Ψ_{y₀}) := (O, χ) with B_{y₀} open, Ψ_{y₀} C¹ and injective on B_{y₀}, DΨ_{y₀}(w) bijective and F(Ψ_{y₀}(w)) = w(0) for w ∈ B_{y₀}, and N_{y₀} := Ψ_{y₀}(B_{y₀}) open with y₀ ∈ N_{y₀}.
6. (Countable subfamily.) Choose such data for every y ∈ O'. The sets N_y (y ∈ O') are open and ℝ^{n+1} is second countable, so there is a countable T ⊆ O' with ⋃_{y∈T} N_y = ⋃_{y∈O'} N_y (TopologicalSpace.isOpen_iUnion_countable). Since y ∈ N_y for y ∈ O', O' ⊆ ⋃_{y∈T} N_y.
7. (Enumeration.) If T ≠ ∅, write T = {y_q : q ∈ ℕ} (Set.Countable.exists_eq_range) and put (B_q, Ψ_q) := (B_{y_q}, Ψ_{y_q}); every required property holds by step 5, and O' ⊆ ⋃_{y∈T} N_y = ⋃_q Ψ_q(B_q) by step 6. If T = ∅, then O' ⊆ ⋃_{y∈T} N_y = ∅; put B_q := ∅ and Ψ_q := id: ∅ is open, id is C¹ and injective on ∅, the pointwise conditions are vacuous, id(∅) = ∅ is open, and O' = ∅ ⊆ ⋃_q Ψ_q(B_q). ∎

Formal check (scratch validation by the decomposition author; not part of the frozen contract). The tactic proof below, for `theorem Submission.dor_lmbsf_pc_straightening_cover : <exactly the frozen lean_statement> := by`, compiled with Lean v4.35.0-rc3 and Mathlib 25730c7c as a single theorem inserted into GMT/Ch07/Submission.lean (namespace GMT.Ch07, frozen imports only) after the declarations of its dependencies (codim1_zsl_gc_local_inverse), with no helper declaration and no set_option; it also compiles under maxHeartbeats 70000, and the controller's leaf gate (leaf_verification.check_source_delta) accepts the insertion. #print axioms of the assembled selected theorem reports propext, Classical.choice and Quot.sound.
```lean
  have hR3 := Submission.codim1_zsl_gc_local_inverse
  intro n F hF
  classical
  have hFd : Differentiable ℝ F := hF.differentiable one_ne_zero
  -- pointwise straightening
  have hloc : ∀ y₀ : Euclid (n + 1), fderiv ℝ F y₀ ≠ 0 →
      ∃ (B : Set (Euclid (n + 1))) (Ψ : Euclid (n + 1) → Euclid (n + 1)), IsOpen B ∧
        ContDiffOn ℝ 1 Ψ B ∧ InjOn Ψ B ∧ (∀ w ∈ B, Bijective (fderiv ℝ Ψ w)) ∧
        (∀ w ∈ B, F (Ψ w) = w 0) ∧ IsOpen (Ψ '' B) ∧ y₀ ∈ Ψ '' B := by
    intro y₀ hy₀
    have hexp : ∀ v : Euclid (n + 1), v = ∑ j, v j • EuclideanSpace.single j (1 : ℝ) := by
      intro v; ext j; simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]
    obtain ⟨i, hi⟩ : ∃ i : Fin (n + 1), fderiv ℝ F y₀ (EuclideanSpace.single i 1) ≠ 0 := by
      by_contra! h
      apply hy₀
      ext1 v
      rw [hexp v, map_sum]
      simp [h]
    -- the linear part `y ↦ (0, y ∘ i.succAbove)`
    let Llin : Euclid (n + 1) →ₗ[ℝ] Euclid (n + 1) :=
      { toFun := fun y => WithLp.toLp 2 (Fin.cons 0 (fun k => y (i.succAbove k)) : Fin (n + 1) → ℝ)
        map_add' := by
          intro y z; ext j; refine Fin.cases ?_ (fun k => ?_) j <;> simp
        map_smul' := by
          intro c y; ext j; refine Fin.cases ?_ (fun k => ?_) j <;> simp }
    let L : Euclid (n + 1) →L[ℝ] Euclid (n + 1) := LinearMap.toContinuousLinearMap Llin
    have hL0 : ∀ y, L y 0 = 0 := fun y => by simp [L, Llin]
    have hLs : ∀ y (k : Fin n), L y k.succ = y (i.succAbove k) := fun y k => by simp [L, Llin]
    let e0 : Euclid (n + 1) := EuclideanSpace.single 0 1
    let Θ : Euclid (n + 1) → Euclid (n + 1) := fun y => F y • e0 + L y
    have hΘ0 : ∀ y, Θ y 0 = F y := fun y => by simp [Θ, e0, hL0]
    have hΘc : ContDiff ℝ 1 Θ := (hF.smul contDiff_const).add L.contDiff
    have hΘD : ∀ y, fderiv ℝ Θ y = (fderiv ℝ F y).smulRight e0 + L := by
      intro y
      have h1 : HasFDerivAt (fun y => F y • e0) ((fderiv ℝ F y).smulRight e0) y :=
        (hFd y).hasFDerivAt.smul_const e0
      exact (h1.add L.hasFDerivAt).fderiv
    have hinj0 : Injective (fderiv ℝ Θ y₀) := by
      rw [hΘD y₀]
      have hker : ∀ h : Euclid (n + 1), ((fderiv ℝ F y₀).smulRight e0 + L) h = 0 → h = 0 := by
        intro h hh
        have hc0 := congrArg (fun v : Euclid (n + 1) => v 0) hh
        have hcs : ∀ k : Fin n, h (i.succAbove k) = 0 := by
          intro k
          have := congrArg (fun v : Euclid (n + 1) => v k.succ) hh
          simpa [e0, hLs, Fin.succ_ne_zero] using this
        have hhi : h = h i • EuclideanSpace.single i (1 : ℝ) := by
          ext j
          rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
          · simp
          · simp [hcs k, Fin.succAbove_ne]
        have hDF : fderiv ℝ F y₀ h = 0 := by simpa [e0, hL0] using hc0
        rw [hhi, map_smul, smul_eq_mul] at hDF
        have hi0 : h i = 0 := by
          rcases mul_eq_zero.mp hDF with h' | h'
          · exact h'
          · exact absurd h' hi
        rw [hhi, hi0, zero_smul]
      intro h1 h2 h12
      have := hker (h1 - h2) (by rw [map_sub, h12, sub_self])
      exact sub_eq_zero.mp this
    obtain ⟨V₀, O, χ, hV₀, hO, hy₀V₀, -, hχ, hχmaps, hΘχ, hχΘ⟩ :=
      hR3 (n + 1) Θ univ y₀ isOpen_univ (mem_univ _) hΘc.contDiffOn hinj0
    have hχd : ∀ a ∈ O, DifferentiableAt ℝ χ a := fun a ha =>
      (hχ.differentiableOn one_ne_zero a ha).differentiableAt (hO.mem_nhds ha)
    have himg : χ '' O = V₀ := by
      apply Subset.antisymm
      · rintro _ ⟨a, ha, rfl⟩; exact hχmaps ha
      · intro z hz; exact ⟨Θ z, (hχΘ z hz).1, (hχΘ z hz).2⟩
    refine ⟨O, χ, hO, hχ, ?_, ?_, ?_, ?_, ?_⟩
    · intro a ha b hb hab
      rw [← hΘχ a ha, ← hΘχ b hb, hab]
    · intro a ha
      have hid : fderiv ℝ (Θ ∘ χ) a = ContinuousLinearMap.id ℝ (Euclid (n + 1)) := by
        rw [Filter.EventuallyEq.fderiv_eq (f₁ := Θ ∘ χ) (f := id) ?_, fderiv_id]
        filter_upwards [hO.mem_nhds ha] with b hb using hΘχ b hb
      rw [fderiv_comp a (hΘc.differentiable one_ne_zero _) (hχd a ha)] at hid
      have hli : Function.LeftInverse (fderiv ℝ Θ (χ a)) (fderiv ℝ χ a) := fun u => by
        simpa using DFunLike.congr_fun hid u
      have hinj : Injective (fderiv ℝ χ a) := hli.injective
      exact ⟨hinj, LinearMap.surjective_of_injective
        (f := (fderiv ℝ χ a : Euclid (n + 1) →ₗ[ℝ] Euclid (n + 1))) hinj⟩
    · intro a ha
      rw [← hΘ0, hΘχ a ha]
    · rw [himg]; exact hV₀
    · rw [himg]; exact hy₀V₀
  let O' : Set (Euclid (n + 1)) := {y | fderiv ℝ F y ≠ 0}
  choose! Bf Ψf hBf hΨf hinjf hbijf hFf hopenf hmemf using hloc
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun y : O' => Ψf y '' Bf y) (fun y => hopenf y y.2)
  by_cases hT : T.Nonempty
  · obtain ⟨e, he⟩ := hTc.exists_eq_range hT
    refine ⟨fun q => Bf (e q), fun q => Ψf (e q), fun q => hBf _ (e q).2, fun q => hΨf _ (e q).2,
      fun q => hinjf _ (e q).2, fun q => hbijf _ (e q).2, fun q => hFf _ (e q).2,
      fun q => hopenf _ (e q).2, ?_⟩
    intro y hy
    have h1 : y ∈ ⋃ z : O', Ψf z '' Bf z := mem_iUnion.mpr ⟨⟨y, hy⟩, hmemf y hy⟩
    rw [← hTU] at h1
    obtain ⟨z, hzT, hz⟩ := mem_iUnion₂.mp h1
    rw [he] at hzT
    obtain ⟨q, rfl⟩ := hzT
    exact mem_iUnion.mpr ⟨q, hz⟩
  · refine ⟨fun _ => ∅, fun _ => id, fun _ => isOpen_empty, fun _ => contDiff_id.contDiffOn,
      fun _ => injOn_empty _, fun _ _ h => absurd h (notMem_empty _),
      fun _ _ h => absurd h (notMem_empty _), fun _ => by simp, ?_⟩
    intro y hy
    have h1 : y ∈ ⋃ z : O', Ψf z '' Bf z := mem_iUnion.mpr ⟨⟨y, hy⟩, hmemf y hy⟩
    rw [← hTU] at h1
    obtain ⟨z, hzT, -⟩ := mem_iUnion₂.mp h1
    exact absurd ⟨z, hzT⟩ hT
```

## Key steps

1. At y₀ with DF(y₀) ≠ 0 pick i with DF(y₀)e_i ≠ 0 and set Θ(y) = F(y)e_0 + (0, y∘i.succAbove).
2. DΘ(y₀) is injective: coordinates k+1 force h = h_i e_i and coordinate 0 forces h_i = 0.
3. local_inverse gives (V₀, O, χ); then χ is injective on O, χ(O) = V₀ is an open neighbourhood of y₀, F∘χ = first coordinate on O, and Dχ is bijective by the chain rule.
4. Second countability selects countably many such charts covering {DF ≠ 0}; enumerate them (or use empty charts if none).

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
