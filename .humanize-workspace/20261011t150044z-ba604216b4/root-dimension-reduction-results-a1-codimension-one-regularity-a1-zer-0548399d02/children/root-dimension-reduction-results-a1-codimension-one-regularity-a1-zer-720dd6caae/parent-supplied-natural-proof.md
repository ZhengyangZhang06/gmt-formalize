# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1.mollify_field-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Supplied proof of the parent node, step 3, first half: by Fubini and evenness of ρ_ε, ∫(ρ_ε ⋆ u_i) div ψ = ∫u_i·(ρ_ε ⋆ div ψ); ρ_ε ⋆ div ψ = div(ρ_ε ⋆ ψ) by HasCompactSupport.hasFDerivAt_convolution_right and ContinuousLinearMap.integral_comp_comm; tsupport ψ_ε ⊆ tsupport ρ_ε + tsupport ψ; |ψ_ε| ≤ 1.
See also Simon Ch. 2, 2.5: the display ∫u^(σ) div g = ∫φ_σ⋆u div g = ∫u φ_σ⋆div g = ∫u div(φ_σ⋆g), and |φ_σ⋆g| ≤ φ_σ⋆|g| (chapter-02.txt lines 573–592).
Deviation: ρ is not assumed even, so the reflected kernel ρ̌(z) := ρ(−z) is used and ψ' := ρ̌ ⋆ ψ. For even ρ this is the parent's ρ_ε ⋆ ψ.
No sibling child is used.

Notation. u := 1_F; G(v) := div ψ(v) = trace Dψ(v); ρ̌(z) := ρ(−z); convolution (a ⋆ φ)(w) := ∫ a(t)φ(w − t) dt, which is Mathlib's convolution with the bilinear map lsmul.

0. (Kernel.) ρ vanishes outside closedBall(0, ε), so ρ and ρ̌ have compact support. Both are C^∞, ≥ 0 and integrable, and ∫ρ̌ = ∫ρ = 1, because Lebesgue measure is invariant under z ↦ −z (integral_neg_eq_self).
1. (Definition.) ψ'(w) := (ρ̌ ⋆ ψ)(w) = ∫ ρ̌(t)ψ(w − t) dt = ∫ ρ(z)ψ(w + z) dz.
2. (Smoothness.) ψ' is C^∞: it is the convolution of the C^∞ compactly supported ρ̌ with the continuous, hence locally integrable, ψ (HasCompactSupport.contDiff_convolution_left).
3. (Support.) tsupport ψ is a closed subset of the open ball B_r, so tsupport ψ ⊆ B_{r₁} for some r₁ < r (exists_lt_subset_ball).
   Suppose ψ'(w) ≠ 0. Then the integrand t ↦ ρ̌(t)ψ(w − t) is not identically 0, so some t has ρ̌(t) ≠ 0 and ψ(w − t) ≠ 0. The first gives |t| ≤ ε, the second |w − t| < r₁, so |w| ≤ |w − t| + |t| ≤ r₁ + ε.
   So support ψ' ⊆ closedBall(0, r₁ + ε). This set is closed, hence tsupport ψ' ⊆ closedBall(0, r₁ + ε) ⊆ B_{r+ε}, and ψ' has compact support (closed and bounded).
4. (Bound.) |ψ'(w)| ≤ ∫ ρ̌(t)|ψ(w − t)| dt ≤ ∫ρ̌ = 1.
5. (Derivative and divergence.) ψ is C¹ with compact support and ρ̌ is locally integrable, so Dψ'(w) = ∫ ρ̌(t)Dψ(w − t) dt (HasCompactSupport.hasFDerivAt_convolution_right). This is a convolution with values in linear maps.
   The trace is a continuous linear functional on the finite-dimensional space of linear maps (LinearMap.toContinuousLinearMap). The integrand t ↦ ρ̌(t)Dψ(w − t) is integrable, being continuous with compact support (HasCompactSupport.convolutionExists_right). So the trace commutes with the integral (ContinuousLinearMap.integral_comp_comm). Substituting t = −z:
   div ψ'(w) = ∫ ρ̌(t)G(w − t) dt = ∫ ρ(z)G(w + z) dz.
6. (Fubini.) Let Γ(v, z) := ρ(z)u(v − z)G(v) on ℝ^m × ℝ^m. It is measurable, and |Γ(v, z)| ≤ |G(v)|ρ(z), a product of integrable functions (G is continuous with compact support; Integrable.mul_prod). So Γ is integrable on the product, and by Fubini (integral_prod)
   ∫_v (∫_z ρ(z)u(v − z) dz)·G(v) dv = ∬ Γ.
   The shear (v, z) ↦ (v + z, z) preserves the product Lebesgue measure (measurePreserving_add_prod), so ∬Γ = ∬Γ(w + z, z) dw dz. Moreover Γ(w + z, z) = u(w)·ρ(z)G(w + z). Integrating first in z and using step 5:
   ∬ Γ(w + z, z) = ∫_w u(w)(∫_z ρ(z)G(w + z) dz) dw = ∫_w u(w)·div ψ'(w) dw = ∫_F div ψ'.
7. Steps 2–6 show that ψ' has all the required properties. ∎
Edge cases. If r ≤ 0 or m = 0 then ψ = 0 and ψ' = 0; the argument covers both.

Appendix (Lean proof, kernel-checked). Compiled with the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c) inside namespace GMT.Ch07 of a file importing GMT.Ch07.Submission, with the contract's opens. It is one declaration with no helper declaration and no set_option. #print axioms gives propext, Classical.choice and Quot.sound.
Note: the trace is made opaque through an obtain; a plain let unfolds LinearMap.trace and times out in rw.

theorem Submission.codim1_zsl_pc_mollify_test_field : ∀ (m : ℕ) (F : Set (Euclid m)) (ρ : Euclid m → ℝ) (ψ : Euclid m → Euclid m) (r ε : ℝ), MeasurableSet F → ContDiff ℝ (⊤ : ℕ∞) ρ → (∀ z, 0 ≤ ρ z) → (∀ z, ε < ‖z‖ → ρ z = 0) → ∫ z, ρ z = 1 → ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ ball (0 : Euclid m) r → (∀ v, ‖ψ v‖ ≤ 1) → ∃ ψ' : Euclid m → Euclid m, ContDiff ℝ (⊤ : ℕ∞) ψ' ∧ HasCompactSupport ψ' ∧ tsupport ψ' ⊆ ball (0 : Euclid m) (r + ε) ∧ (∀ v, ‖ψ' v‖ ≤ 1) ∧ ∫ v, (∫ z, ρ z * F.indicator (fun _ => (1 : ℝ)) (v - z)) * LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ v).toLinearMap = ∫ w in F, LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ' w).toLinearMap := by
  intro m F ρ ψ r ε hF hρ hρ0 hρε hρ1 hψ hψcs hψr hψ1
  -- basic facts about `ρ` and its reflection `ρ'`
  have hρc : Continuous ρ := hρ.continuous
  have hρcs : HasCompactSupport ρ :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Euclid m) ε)
      (fun z hz => hρε z (by simpa using hz))
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρcs
  set ρ' : Euclid m → ℝ := fun z => ρ (-z) with hρ'_def
  have hρ'c : Continuous ρ' := hρc.comp continuous_neg
  have hρ'cs : HasCompactSupport ρ' :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Euclid m) ε)
      (fun z hz => hρε (-z) (by simpa using hz))
  have hρ'smooth : ContDiff ℝ (⊤ : ℕ∞) ρ' := hρ.comp contDiff_neg
  have hρ'i : Integrable ρ' := hρ'c.integrable_of_hasCompactSupport hρ'cs
  have hρ'1 : ∫ z, ρ' z = 1 := by
    rw [show (∫ z, ρ' z) = ∫ z, ρ (-z) from rfl, integral_neg_eq_self ρ volume]
    exact hρ1
  -- the trace as a continuous linear map
  obtain ⟨Tr, hTr⟩ : ∃ Tr : (Euclid m →L[ℝ] Euclid m) →L[ℝ] ℝ, ∀ A : Euclid m →L[ℝ] Euclid m,
      Tr A = LinearMap.trace ℝ (Euclid m) A.toLinearMap :=
    ⟨LinearMap.toContinuousLinearMap
      ((LinearMap.trace ℝ (Euclid m)) ∘ₗ (ContinuousLinearMap.coeLM ℝ)), fun A => rfl⟩
  -- the mollified field `ψ' = ρ' ⋆ ψ`
  set L : ℝ →L[ℝ] Euclid m →L[ℝ] Euclid m := ContinuousLinearMap.lsmul ℝ ℝ with hL
  set ψ' : Euclid m → Euclid m := convolution ρ' ψ L volume with hψ'_def
  have hψ'apply : ∀ w, ψ' w = ∫ t, ρ' t • ψ (w - t) := by
    intro w
    rw [hψ'_def, convolution_def]
    simp [L]
  -- support
  obtain ⟨r₁, hr₁r, hr₁⟩ := exists_lt_subset_ball (isClosed_tsupport ψ) hψr
  have hsupp : support ψ' ⊆ closedBall 0 (r₁ + ε) := by
    intro w hw
    rw [Function.mem_support, hψ'apply] at hw
    by_contra hcon
    apply hw
    have hzero : ∀ t, ρ' t • ψ (w - t) = 0 := by
      intro t
      by_cases h1 : ρ' t = 0
      · simp [h1]
      by_cases h2 : ψ (w - t) = 0
      · simp [h2]
      exfalso
      apply hcon
      have ht : ‖t‖ ≤ ε := by
        by_contra h
        push Not at h
        exact h1 (hρε (-t) (by rwa [norm_neg]))
      have hwt : w - t ∈ ball (0 : Euclid m) r₁ := hr₁ (subset_tsupport ψ h2)
      rw [mem_ball_zero_iff] at hwt
      rw [mem_closedBall_zero_iff]
      calc ‖w‖ = ‖(w - t) + t‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - t‖ + ‖t‖ := norm_add_le _ _
        _ ≤ r₁ + ε := by linarith
    simp [hzero]
  have htsupp : tsupport ψ' ⊆ closedBall 0 (r₁ + ε) := closure_minimal hsupp isClosed_closedBall
  -- derivative of `ψ'` and its trace
  have hderiv : ∀ w, fderiv ℝ ψ' w =
      convolution ρ' (fderiv ℝ ψ) (ContinuousLinearMap.precompR (Euclid m) L) volume w := fun w =>
    (hψcs.hasFDerivAt_convolution_right L hρ'i.locallyIntegrable
      (hψ.of_le (by exact_mod_cast le_top)) w).fderiv
  have hG' : ∀ w, LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ' w).toLinearMap =
      ∫ z, ρ z * LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ (w + z)).toLinearMap := by
    intro w
    have hint : Integrable (fun t => ρ' t • fderiv ℝ ψ (w - t)) :=
      (hψcs.fderiv (𝕜 := ℝ)).convolutionExists_right (ContinuousLinearMap.precompR (Euclid m) L)
        hρ'i.locallyIntegrable (hψ.continuous_fderiv (by simp)) w
    have h1 : fderiv ℝ ψ' w = ∫ t, ρ' t • fderiv ℝ ψ (w - t) := by
      rw [hderiv w, convolution_def]
      congr 1
    rw [← hTr, h1, ← ContinuousLinearMap.integral_comp_comm Tr hint,
      ← integral_neg_eq_self
        (fun z => ρ z * LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ (w + z)).toLinearMap) volume]
    congr 1
    funext t
    rw [map_smul, smul_eq_mul, hTr, ← sub_eq_add_neg]
  refine ⟨ψ', ?_, ?_, ?_, ?_, ?_⟩
  · exact hρ'cs.contDiff_convolution_left L hρ'smooth hψ.continuous.locallyIntegrable
  · exact (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) htsupp
  · exact htsupp.trans (closedBall_subset_ball (by linarith))
  · intro v
    rw [hψ'apply]
    refine (norm_integral_le_of_norm_le hρ'i (ae_of_all _ fun t => ?_)).trans hρ'1.le
    rw [norm_smul, Real.norm_of_nonneg (hρ0 _)]
    exact mul_le_of_le_one_right (hρ0 _) (hψ1 _)
  · -- Fubini
    set u : Euclid m → ℝ := F.indicator (fun _ => (1 : ℝ)) with hu
    set G : Euclid m → ℝ :=
      fun v => LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ v).toLinearMap with hG
    have hGeq : G = Tr ∘ fderiv ℝ ψ := by
      funext v
      simp only [G, Function.comp_apply, hTr]
    have hGc : Continuous G := by
      rw [hGeq]; exact Tr.continuous.comp (hψ.continuous_fderiv (by simp))
    have hGcs : HasCompactSupport G := by
      rw [hGeq]; exact (hψcs.fderiv (𝕜 := ℝ)).comp_left (map_zero Tr)
    have hGi : Integrable G := hGc.integrable_of_hasCompactSupport hGcs
    have hum : Measurable u := measurable_const.indicator hF
    have hu01 : ∀ x, 0 ≤ u x ∧ u x ≤ 1 := fun x => by
      by_cases hx : x ∈ F <;> simp [u, hx]
    set g : Euclid m × Euclid m → ℝ := fun p => ρ p.2 * u (p.1 - p.2) * G p.1 with hg
    have hgm : Measurable g :=
      ((hρc.measurable.comp measurable_snd).mul
        (hum.comp (measurable_fst.sub measurable_snd))).mul (hGc.measurable.comp measurable_fst)
    have hgi : Integrable g (volume.prod volume) := by
      refine Integrable.mono' (hGi.norm.mul_prod hρi) hgm.aestronglyMeasurable
        (ae_of_all _ fun p => ?_)
      have h1 := hu01 (p.1 - p.2)
      have h2 := hρ0 p.2
      simp only [g, Real.norm_eq_abs, abs_mul, abs_of_nonneg h2, abs_of_nonneg h1.1]
      nlinarith [mul_nonneg (mul_nonneg h2 (abs_nonneg (G p.1))) (sub_nonneg.mpr h1.2)]
    have hT : MeasurePreserving (fun p : Euclid m × Euclid m => (p.1 + p.2, p.2))
        (volume.prod volume) (volume.prod volume) := measurePreserving_add_prod volume volume
    have hgTi : Integrable (fun p : Euclid m × Euclid m => g (p.1 + p.2, p.2))
        (volume.prod volume) :=
      (hT.integrable_comp hgm.aestronglyMeasurable).mpr hgi
    have hgT : ∫ p, g (p.1 + p.2, p.2) ∂(volume.prod volume) =
        ∫ p, g p ∂(volume.prod volume) := by
      have := integral_map (μ := volume.prod volume) hT.measurable.aemeasurable
        (f := g) (by rw [hT.map_eq]; exact hgm.aestronglyMeasurable)
      rw [hT.map_eq] at this
      exact this.symm
    have hLHS : ∫ v, (∫ z, ρ z * u (v - z)) * G v = ∫ p, g p ∂(volume.prod volume) := by
      rw [integral_prod g hgi]
      congr 1
      funext v
      rw [← integral_mul_const]
    have hRHS : ∫ w in F, LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ' w).toLinearMap =
        ∫ p, g (p.1 + p.2, p.2) ∂(volume.prod volume) := by
      rw [integral_prod _ hgTi, ← integral_indicator hF]
      congr 1
      funext w
      have h1 : ∀ z, g (w + z, z) = u w * (ρ z * G (w + z)) := fun z => by
        simp only [g, add_sub_cancel_right]
        ring
      dsimp only
      simp only [h1]
      rw [integral_const_mul, ← hG' w]
      by_cases hw : w ∈ F <;> simp [u, hw]
    exact hLHS.trans (hgT.symm.trans hRHS.symm)

## Key steps

1. ψ' := ρ̌ ⋆ ψ with ρ̌(z) = ρ(−z) is C^∞, as a convolution with a C^∞ compactly supported kernel.
2. tsupport ψ ⊆ B_{r₁} with r₁ < r, so support ψ' ⊆ closedBall(0, r₁ + ε) ⊆ B_{r+ε}; and |ψ'| ≤ ∫ρ̌|ψ| ≤ 1.
3. Dψ' = ρ̌ ⋆ Dψ and the trace commutes with the integral: div ψ'(w) = ∫ρ(z) div ψ(w + z) dz.
4. Fubini with the measure-preserving shear (v, z) ↦ (v + z, z): ∫(ρ⋆1_F) div ψ = ∫1_F(w)∫ρ(z) div ψ(w + z) dz dw = ∫_F div ψ'.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; grep -A4 '"simongmt"' local-references/123e8435b4a2469b/project/lake-manifest.json`
- `sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n 'theorem (IsCompact.tendsto_subseq|isCompact_univ_pi|measure_limsup_atTop_eq_zero|ae_eventually_notMem|tendsto_measure_iInter_atTop|lintegral_lintegral_swap|volume_pi_Ico|addHaar_closedBall |lintegral_liminf_le |integral_eq_sub_of_hasDerivAt |integral_comp_comm|exists_lt_subset_ball|tendsto_lintegral_of_dominated_convergence |measurable_to_countable'|preimage_floor_singleton|_root_.HasCompactSupport.hasFDerivAt_convolution_right|_root_.HasCompactSupport.contDiff_convolution_left|toDual_symm_apply|support_eq|tsupport_eq|one_of_mem_closedBall)' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n 'exists_thickening_subset_open|trace_eq_sum_inner|integral_neg_eq_self|volume_preserving_ofLp|_root_.MeasurableSet.exists_isCompact_sdiff_lt|_root_.MeasurableSet.exists_isOpen_sdiff_lt|Int.measurable_floor|hasFDerivAt_apply' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n -i 'kolmogorov|rellich|BoundedVariation|perimeter|caccioppoli' -l local-references/123e8435b4a2469b/mathlib/Mathlib; rg -n -i 'compactness|BV|perimeter' local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean; rg -n -i 'theorem .*compact|TendstoLocallyInL1On' .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `lake env lean /tmp/bvc-split/Closure.lean (import-closure module list of GMT.Ch07.Submission filtered for Chapter02|Convolution|BumpFunction|HeineCantor|Floor)`
- `lake env lean /tmp/bvc-split/Ctx.lean and /tmp/bvc-split/Probe.lean (#check of about 35 cited lemmas in the contract scope)`
- `python3 scan of dag.json (lean_name, lean_statement, status) for reusable nodes: mollif|convolution|translation|integration by parts|divergence|trace|indicator|symmDiff|diagonal|subseq|StrictMono|BV|perimeter|cube; lookup of dorag_ha_lsc_ibp_c1_ball, dorag_ha_lsc_ibp_lipschitz, dgcr_stc_exists_normalized_mollifier, dorag_ha_rb_l2_subseq, cmc_fc_cs_diagonal_subseq, codim1_rdo_dg_bv_set_compactness`
- `uniqueness scan of the 11 names codim1_zsl_pc_* in dag.json, issue-workers.json, nodes/*/*.json|md, GMT/, .lake/packages/simongmt/Poincare and git grep over all 1661 refs; byte comparison of the frozen type of dorag_ha_lsc_ibp_c1_ball`
- `git show 46877ce9:GMT/Ch07/Submission.lean (accepted proofs of dorag_ha_lsc_ibp_lipschitz and dorag_ha_lsc_ibp_c1_ball); grep -n 'def check_source_delta' -A40 /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py; sed -n 4370,4390p and 6525,6570p /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `lake env lean /tmp/bvc-split/Types.lean, GlueT2.lean, agentT/T.lean, agentK/K.lean, agentK1/K1.lean, agentK23/K23.lean, agentT4a/T4a.lean, agentT4/T4.lean, agentT5/T5.lean, agentT2a/T2a.lean, agentT2b/T2b.lean and full/Full.lean (#print axioms of all 13 declarations)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/BorelCantelli.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Floor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Floor/Ring.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/WithLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/ProperSpace/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0548399d02/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-0b4bc9c57a/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/bvc-split/Types.lean`
- `/tmp/bvc-split/full/Full.lean`

Pins match.
- The snapshot manifest records project b4d606db and Mathlib 25730c7c; both equal workspace HEAD and .lake/packages/mathlib.
- The snapshot pins simongmt 2b366308.
- The snapshot Contract.lean and the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f9503…).

Import closure.
- GMT.Ch07.Submission has 5034 modules. They include Mathlib.Analysis.Convolution, Analysis.Calculus.ContDiff.Convolution, BumpFunction.Basic/InnerProduct/FiniteDimension and Topology.UniformSpace.HeineCantor.
- They do not include BumpFunction.Normed, BumpFunction.Convolution, MeasureTheory.Function.Floor (so Int.measurable_floor is unavailable), LineDeriv integration by parts, or SimonGMT Chapter02.BV.

Snapshot Mathlib provides every tool the children use. Locations:
- Topology/Sequences.lean:298 IsCompact.tendsto_subseq
- Topology/Compactness/Compact.lean:1172 isCompact_univ_pi
- MeasureTheory/OuterMeasure/BorelCantelli.lean:62/92 measure_limsup_atTop_eq_zero, ae_eventually_notMem
- MeasureTheory/Measure/Continuity.lean:220 tendsto_measure_iInter_atTop
- MeasureTheory/Measure/Prod.lean:1071 lintegral_lintegral_swap
- MeasureTheory/Measure/Lebesgue/Basic.lean:262 volume_pi_Ico
- MeasureTheory/Measure/Lebesgue/EqHaar.lean:500 addHaar_closedBall
- MeasureTheory/Integral/Lebesgue/Add.lean:233 lintegral_liminf_le
- MeasureTheory/Integral/Lebesgue/DominatedConvergence.lean:48 tendsto_lintegral_of_dominated_convergence
- MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:1148 integral_eq_sub_of_hasDerivAt
- MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean:70 integral_comp_comm
- MeasureTheory/Integral/Prod.lean:297 Integrable.mul_prod
- MeasureTheory/MeasurableSpace/Constructions.lean:42 measurable_to_countable'
- Algebra/Order/Floor/Ring.lean:154 preimage_floor_singleton
- Analysis/Calculus/ContDiff/Convolution.lean:61/427 hasFDerivAt_convolution_right, contDiff_convolution_left
- MeasureTheory/Measure/Regular.lean:385/843 exists_isOpen_sdiff_lt, exists_isCompact_sdiff_lt
- Topology/MetricSpace/Thickening.lean:439 exists_thickening_subset_open
- Analysis/InnerProductSpace/Trace.lean:25 trace_eq_sum_inner
- Analysis/InnerProductSpace/Dual.lean:178 toDual_symm_apply
- MeasureTheory/Measure/Haar/InnerProductSpace.lean:134 PiLp.volume_preserving_ofLp
- Topology/MetricSpace/ProperSpace/Lemmas.lean:45 exists_lt_subset_ball
- Analysis/Calculus/BumpFunction/Basic.lean:137/151/157 one_of_mem_closedBall, support_eq, tsupport_eq

No existing BV compactness to reuse.
- Mathlib has no Kolmogorov–Riesz or perimeter compactness; its BoundedVariation files are one-dimensional.
- The project's Ch02 BVCompactness is an unproved Prop definition outside the closure.
- SimonGMT BV.lean has only TendstoLocallyInL1On lemmas.

DAG.
- One theorem is reusable with an identical type: dorag_ha_lsc_ibp_c1_ball. It is accepted, candidate 46877ce9, its type is byte-identical, and its accepted dependency dorag_ha_lsc_ibp_lipschitz is in the same candidate history.
- dgcr_stc_exists_normalized_mollifier, dorag_ha_rb_l2_subseq and cmc_fc_cs_diagonal_subseq were not reused, because their types do not fit.
- The eleven new names codim1_zsl_pc_* have 0 hits in dag.json, issue-workers.json, the node files, GMT/, SimonGMT and all 1661 git refs.

Lean.
- Types.lean elaborates all 12 frozen types and proves the parent from them.
- Each child was proved separately, with siblings as stubs.
- Full.lean holds the accepted IBP proofs, the 11 new proofs and the parent assembly. It compiles in about 64 s, and #print axioms gives [propext, Classical.choice, Quot.sound] for every declaration, including the exact frozen parent type.
- check_source_delta forbids helper declarations and set_option in leaf proofs, which is why the argument is split into single-declaration children.
