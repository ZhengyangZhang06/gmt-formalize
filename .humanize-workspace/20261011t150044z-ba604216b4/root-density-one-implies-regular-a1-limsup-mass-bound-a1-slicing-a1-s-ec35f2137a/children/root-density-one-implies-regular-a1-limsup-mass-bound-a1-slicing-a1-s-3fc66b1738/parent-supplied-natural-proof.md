# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_coarea-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_coarea-a1.slice_tonelli-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent steps 5 (area formula for every slice parametrization Φ_s) and 7 (Tonelli through the volume-preserving splitting ℝ^{n+1} ≅ ℝ × ℝⁿ), with the distinguished coordinate i = 0, so that ins_0(z, s) = (s, z), drop_0(w) = (w(1), …, w(n)), and the parent's factor JΦ_s(z) is J'(ins_s(z)) below. Departure: the parametrization Φ and the Borel set S are arbitrary (no box B = D × I is needed); the slice of S at a level t is empty when no point of S has first coordinate t.

Conventions: ℝ^k = Euclid k = EuclideanSpace ℝ (Fin k); e_k := EuclideanSpace.single k 1 is the k-th standard basis vector; for v ∈ ℝ^{n+1}, v(0) = v 0 (Lean `v.ofLp 0`) is its 0-th coordinate, while e_k always denotes a basis vector; DΦ(w) := fderiv ℝ Φ w; Hᵏ := μHE[k]; |v| := ‖v‖ and |v|ₑ := ‖v‖ₑ = ofReal ‖v‖; all integrals are lower integrals in [0, ∞]. J'(w) := (det[⟨DΦ(w)e_{i+1}, DΦ(w)e_{j+1}⟩]_{i,j=0}^{n−1})^{1/2} (Real.sqrt). For t ∈ ℝ and z ∈ ℝⁿ let ins_t(z) := (t, z_0, …, z_{n−1}) = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp z)) ∈ ℝ^{n+1}, and let ι : ℝⁿ → ℝ^{n+1}, ι(z) := (0, z_0, …, z_{n−1}). ι is linear and continuous (finite dimension), injective (coordinates 1, …, n of ι(z) are those of z), and ι(e'_k) = e_{k+1} for the standard basis vectors e'_k of ℝⁿ. Since ins_t(z) = ins_t(0) + ι(z), ins_t is continuous and injective and has derivative ι at every point (HasFDerivAt.const_add).

1. (J' is Borel.) On the space of continuous linear maps ℝ^{n+1} → ℝ^P, L ↦ (det[⟨L e_{i+1}, L e_{j+1}⟩])^{1/2} is continuous: the entries are inner products of evaluations, the determinant is a polynomial in the entries, Real.sqrt is continuous. w ↦ DΦ(w) is Borel for every map Φ (measurable_fderiv). Hence J' is Borel.
2. (The integrand H.) Φ is continuous at every point of S (it is differentiable there), so Φ is continuous on S, and the function Φ̃ equal to Φ on S and to 0 off S is Borel (ContinuousOn.measurable_piecewise, S Borel). Put H := 1_S·ofReal(J')·(φ∘Φ) : ℝ^{n+1} → [0, ∞]. Since H = 1_S·ofReal(J')·(φ∘Φ̃) and φ is Borel, H is Borel.
3. (One slice.) Fix t ∈ ℝ. S_t := ins_t^{−1}(S) ⊆ ℝⁿ is Borel (ins_t is continuous). Put Φ_t := Φ∘ins_t.
 (a) Φ(S ∩ {w : w(0) = t}) = Φ_t(S_t): if w ∈ S and w(0) = t, then w = ins_t(z) for z := (w(1), …, w(n)) (compare coordinates, Fin.cases), so z ∈ S_t and Φ(w) = Φ_t(z); conversely ins_t(z)(0) = t.
 (b) For z ∈ S_t, Φ is differentiable at ins_t(z) ∈ S, so by the chain rule Φ_t is differentiable at z with DΦ_t(z) = DΦ(ins_t(z))∘ι, which is injective as a composition of injective maps.
 (c) Φ_t is injective on S_t: Φ_t(y) = Φ_t(z) with y, z ∈ S_t gives ins_t(y) = ins_t(z) (Φ injective on S), hence ι(y) = ι(z) and y = z.
 (d) By the sibling gram_area_formula with m := n, f := Φ_t, s := S_t and weight φ: ∫_{Φ_t(S_t)} φ dHⁿ = ∫_{S_t} ofReal(J_t(z))·φ(Φ_t(z)) dz with J_t(z) = (det[⟨DΦ_t(z)e'_k, DΦ_t(z)e'_l⟩])^{1/2}. By (b) and ι(e'_k) = e_{k+1}, DΦ_t(z)e'_k = DΦ(ins_t(z))e_{k+1}, so J_t(z) = J'(ins_t(z)).
 (e) Since 1_{S_t}(z) = 1_S(ins_t(z)) (lintegral_indicator, S_t Borel), (a) and (d) give, for every t ∈ ℝ: ∫_{Φ(S ∩ {w(0) = t})} φ dHⁿ = ∫_{ℝⁿ} H(ins_t(z)) dz.
4. (Volume-preserving splitting.) E : ℝ × ℝⁿ → ℝ^{n+1}, E(t, z) := ins_t(z), is the composition of (id × WithLp.ofLp) : ℝ × ℝⁿ → ℝ × (Fin n → ℝ) (measure preserving by PiLp.volume_preserving_ofLp and MeasurePreserving.prod), of the inverse of MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0, which maps (t, g) to Fin.cons t g (measure preserving by volume_preserving_piFinSuccAbove), and of WithLp.toLp 2 (measure preserving by PiLp.volume_preserving_toLp). So E is measure preserving from the product Lebesgue measure on ℝ × ℝⁿ to Lebesgue measure on ℝ^{n+1}; in particular H∘E is Borel.
5. (Claim (a).) By Tonelli's measurability statement (Measurable.lintegral_prod_right'; Lebesgue measure on ℝⁿ is s-finite), t ↦ ∫_{ℝⁿ} H(E(t, z)) dz is Borel. By step 3(e) it equals t ↦ ∫_{Φ(S ∩ {w(0) = t})} φ dHⁿ, which is therefore Borel, hence a.e.-measurable.
6. (Claim (b).) ∫_ℝ ∫_{Φ(S ∩ {w(0) = t})} φ dHⁿ dt = ∫_ℝ ∫_{ℝⁿ} H(E(t, z)) dz dt (step 3(e)) = ∫_{ℝ×ℝⁿ} H∘E (Tonelli, lintegral_prod) = ∫_{ℝ^{n+1}} H dw (E measure preserving and H Borel, MeasurePreserving.lintegral_comp) = ∫_S ofReal(J'(w))·φ(Φ(w)) dw (lintegral_indicator, S Borel). ∎

Formal check (scratch validation by the decomposition author; not part of the frozen contract). The tactic proof below, for `theorem Submission.dor_lmbsf_pc_slice_area_tonelli : <exactly the frozen lean_statement> := by`, compiled with Lean v4.35.0-rc3 and Mathlib 25730c7c as a single theorem inserted into GMT/Ch07/Submission.lean (namespace GMT.Ch07, frozen imports only) after the declarations of its dependencies (codim1_lura_gram_area_formula), with no helper declaration and no set_option; it also compiles under maxHeartbeats 70000, and the controller's leaf gate (leaf_verification.check_source_delta) accepts the insertion. #print axioms of the assembled selected theorem reports propext, Classical.choice and Quot.sound.
```lean
  have hR := Submission.codim1_lura_gram_area_formula
  intro P n Φ S hS hd hinj hInj φ hφ
  classical
  -- the slice embeddings `z ↦ (t, z)` and their common linear part `ι`
  let ins : ℝ → Euclid n → Euclid (n + 1) := fun t z =>
    WithLp.toLp 2 (Fin.cons t (WithLp.ofLp z) : Fin (n + 1) → ℝ)
  let ιlin : Euclid n →ₗ[ℝ] Euclid (n + 1) :=
    { toFun := fun z => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp z) : Fin (n + 1) → ℝ)
      map_add' := by
        intro y z; ext j; refine Fin.cases ?_ (fun k => ?_) j <;> simp
      map_smul' := by
        intro c y; ext j; refine Fin.cases ?_ (fun k => ?_) j <;> simp }
  let ι : Euclid n →L[ℝ] Euclid (n + 1) := LinearMap.toContinuousLinearMap ιlin
  have hins : ∀ t z, ins t z = ins t 0 + ι z := by
    intro t z; ext j; refine Fin.cases ?_ (fun k => ?_) j <;> simp [ins, ι, ιlin]
  have hinsD : ∀ t z, HasFDerivAt (ins t) ι z := by
    intro t z
    have : ins t = fun z => ins t 0 + ι z := funext (hins t)
    rw [this]
    exact ι.hasFDerivAt.const_add _
  have hιe : ∀ k : Fin n, ι (EuclideanSpace.single k 1) = EuclideanSpace.single k.succ 1 := by
    intro k; ext j; refine Fin.cases ?_ (fun l => ?_) j <;> simp [ι, ιlin, Pi.single_apply]
  -- slice Jacobian and integrand
  let J' : Euclid (n + 1) → ℝ := fun w => Real.sqrt (Matrix.det (Matrix.of fun i j : Fin n =>
    inner ℝ (fderiv ℝ Φ w (EuclideanSpace.single i.succ 1)) (fderiv ℝ Φ w (EuclideanSpace.single j.succ 1))))
  have hJ'm : Measurable J' := by
    have hc : Continuous (fun L : Euclid (n + 1) →L[ℝ] Euclid P => Real.sqrt (Matrix.det
        (Matrix.of fun i j : Fin n => inner ℝ (L (EuclideanSpace.single i.succ 1))
          (L (EuclideanSpace.single j.succ 1))))) := by
      refine Real.continuous_sqrt.comp (Continuous.matrix_det ?_)
      refine continuous_pi fun k => continuous_pi fun l => ?_
      exact (continuous_id.clm_apply continuous_const).inner (continuous_id.clm_apply continuous_const)
    exact hc.measurable.comp (measurable_fderiv ℝ Φ)
  let H : Euclid (n + 1) → ℝ≥0∞ := S.indicator (fun w => ENNReal.ofReal (J' w) * φ (Φ w))
  have hΦc : ContinuousOn Φ S := fun w hw => (hd w hw).continuousAt.continuousWithinAt
  have hHm : Measurable H := by
    have hpw : Measurable (S.piecewise Φ (fun _ => 0)) :=
      hΦc.measurable_piecewise continuousOn_const hS
    have : H = S.indicator (fun w => ENNReal.ofReal (J' w) * φ (S.piecewise Φ (fun _ => 0) w)) := by
      ext w
      by_cases hw : w ∈ S
      · simp [H, hw, Set.piecewise_eq_of_mem]
      · simp [H, hw]
    rw [this]
    exact ((hJ'm.ennreal_ofReal).mul (hφ.comp hpw)).indicator hS
  -- the inner integral, slice by slice
  have hinner : ∀ t : ℝ, ∫⁻ x in Φ '' (S ∩ {w | w 0 = t}), φ x ∂μHE[n] = ∫⁻ z, H (ins t z) := by
    intro t
    let St : Set (Euclid n) := ins t ⁻¹' S
    have hinsc : Continuous (ins t) := by
      have : ins t = fun z => ins t 0 + ι z := funext (hins t)
      rw [this]; exact continuous_const.add ι.continuous
    have hSt : MeasurableSet St := hinsc.measurable hS
    have himg : Φ '' (S ∩ {w | w 0 = t}) = (Φ ∘ ins t) '' St := by
      rw [image_comp]
      congr 1
      ext w
      constructor
      · rintro ⟨hwS, hwt⟩
        refine ⟨WithLp.toLp 2 (Fin.tail (WithLp.ofLp w)), ?_, ?_⟩
        · have : ins t (WithLp.toLp 2 (Fin.tail (WithLp.ofLp w))) = w := by
            ext j; refine Fin.cases ?_ (fun k => ?_) j
            · simpa [ins] using hwt.symm
            · simp [ins, Fin.tail]
          show ins t _ ∈ S
          rw [this]; exact hwS
        · ext j; refine Fin.cases ?_ (fun k => ?_) j
          · simpa [ins] using hwt.symm
          · simp [ins, Fin.tail]
      · rintro ⟨z, hz, rfl⟩
        exact ⟨hz, by simp [ins]⟩
    have hdt : ∀ z ∈ St, DifferentiableAt ℝ (Φ ∘ ins t) z := fun z hz =>
      (hd _ hz).comp z (hinsD t z).differentiableAt
    have hDt : ∀ z ∈ St, fderiv ℝ (Φ ∘ ins t) z = (fderiv ℝ Φ (ins t z)).comp ι := fun z hz =>
      ((hd _ hz).hasFDerivAt.comp z (hinsD t z)).fderiv
    have hιinj : Injective ι := by
      intro y z hyz
      ext k
      have := congrArg (fun v : Euclid (n + 1) => v k.succ) hyz
      simpa [ι, ιlin] using this
    have hinjt : ∀ z ∈ St, Injective (fderiv ℝ (Φ ∘ ins t) z) := by
      intro z hz
      rw [hDt z hz]
      exact (hinj _ hz).comp hιinj
    have hInjt : InjOn (Φ ∘ ins t) St := by
      intro y hy z hz hyz
      have h1 : ins t y = ins t z := hInj hy hz hyz
      have h2 : ι y = ι z := by
        rw [hins t y, hins t z] at h1; exact add_left_cancel h1
      exact hιinj h2
    rw [himg, (hR n P (Φ ∘ ins t)).2 St hSt hdt hinjt hInjt φ, ← lintegral_indicator hSt]
    congr 1
    ext z
    by_cases hz : z ∈ St
    · have hz' : ins t z ∈ S := hz
      simp only [indicator_of_mem hz, H, indicator_of_mem hz', hDt z hz, J',
        ContinuousLinearMap.comp_apply, hιe, comp_apply]
    · have hz' : ins t z ∉ S := hz
      simp only [indicator_of_notMem hz, H, indicator_of_notMem hz']
  -- the volume-preserving splitting `ℝ × ℝⁿ ≃ ℝⁿ⁺¹`
  have he : MeasurePreserving (fun p : ℝ × Euclid n => ins p.1 p.2) volume volume := by
    have h1 : MeasurePreserving (Prod.map (id : ℝ → ℝ) (WithLp.ofLp : Euclid n → (Fin n → ℝ)))
        (volume : Measure (ℝ × Euclid n)) (volume : Measure (ℝ × (Fin n → ℝ))) :=
      (MeasurePreserving.id volume).prod (PiLp.volume_preserving_ofLp (Fin n))
    have h2 := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
    have h3 := PiLp.volume_preserving_toLp (Fin (n + 1))
    have h := h3.comp (h2.comp h1)
    convert h using 1
    funext p
    simp [ins, MeasurableEquiv.piFinSuccAbove_symm_apply]
    rfl
  have hHe : Measurable (fun p : ℝ × Euclid n => H (ins p.1 p.2)) := hHm.comp he.measurable
  refine ⟨?_, ?_⟩
  · simp_rw [hinner]
    exact hHe.lintegral_prod_right'.aemeasurable
  · simp_rw [hinner]
    rw [← lintegral_indicator hS]
    change ∫⁻ t, ∫⁻ z, H (ins t z) = ∫⁻ w, H w
    rw [← he.lintegral_comp hHm]
    exact (lintegral_prod _ hHe.aemeasurable).symm
```

## Key steps

1. J' is Borel (continuous function of the Borel map DΦ); H := 1_S·ofReal(J')·φ∘Φ is Borel via the piecewise extension of Φ|_S.
2. For each t, the slice Φ(S ∩ {w(0) = t}) is Φ_t(S_t) with Φ_t = Φ∘ins_t, S_t = ins_t^{-1}(S), DΦ_t(z) = DΦ(ins_t z)∘ι injective, Φ_t injective on S_t.
3. gram_area_formula with m = n and ι(e'_k) = e_{k+1}: the slice integral equals ∫_{ℝⁿ} H(ins_t z) dz for every t.
4. E(t, z) = ins_t(z) is measure preserving ℝ × ℝⁿ → ℝ^{n+1} (ofLp, piFinSuccAbove 0, toLp).
5. Tonelli gives Borel measurability in t and ∫_ℝ ∫ H(E(t,z)) dz dt = ∫ H = ∫_S ofReal(J')·φ∘Φ.

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
