# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_c2alpha-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_c2alpha-a1.dq_weak_equation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 4(a), (b) and (d) of the parent proof; the right-hand side computation 4(c) is the sibling dohr_eb_elc2_shift_ibp.
Notation. Delta(y) := Du(y + de) - Du(y), P_t(y) := Du(y) + t Delta(y), I(y) := integral_0^1 B(P_t(y))[d^{-1}Delta(y)][Dzeta(y)] dt, G(y) := integral_0^1 g(y + (td)e) dt and J(y) := <G(y), Dzeta(y)e>. The claim is integral_V I = integral_V J. Fix zeta as in the statement; K := tsupport zeta is compact, closed and contained in V. Lebesgue measure is translation invariant (integral_add_right_eq_self).
1. Vanishing. zeta(y) = 0 and Dzeta(y) = 0 for y not in K (fderiv_of_notMem_tsupport), so I(y) = 0 and J(y) = 0 for y not in K (both are linear in Dzeta(y)). As K is contained in V, integral_V I = integral I and integral_V J = integral J over R^n (setIntegral_eq_integral_of_forall_compl_eq_zero); it suffices to prove integral I = integral J.
2. Points of U. For y in K and t in [0,1], y + (td)e lies in U; in particular y and y + de lie in U. As U is open and u is C^1 on U, Du is continuous at every point of U (ContDiffOn.continuousOn_fderiv_of_isOpen); g is continuous at every point of U. Psi is C^2, so A is C^1 with derivative B, and A, B are continuous.
3. Continuity principle. If C is a compact subset of R^n and F : R^n -> R vanishes outside C and is continuous at every point of C, then F is continuous (a point outside the closed set C has a neighbourhood on which F = 0) and has compact support (HasCompactSupport.intro), hence is integrable (Continuous.integrable_of_hasCompactSupport).
4. Integrands. F1(y) := A(Du(y + de))[Dzeta(y)], F2(y) := A(Du(y))[Dzeta(y)] and R2(y) := <zeta(y), g(y)> vanish outside K and are continuous at every point of K (step 2). R3(x) := <zeta(x - de), g(x)> vanishes outside K + de (compact, contained in U by step 2) and is continuous at every point of K + de. By step 3 all four are integrable.
5. Test function zeta. zeta is C^1 with compact support and tsupport zeta = K is contained in U. The hypothesis gives integral_U A(Du(x))[Dzeta(x)] dx = - integral_U <zeta(x), g(x)> dx. Both integrands vanish outside K, a subset of U, so the integrals over U are integrals over R^n: (E2) integral F2 = - integral R2.
6. Translated test function. phi1(x) := zeta(x - de) is C^1 with Dphi1(x) = Dzeta(x - de) (fderiv_comp_sub); it has compact support (composition with the homeomorphism x -> x - de; HasCompactSupport.comp_isClosedEmbedding), and tsupport phi1 = K + de (tsupport_comp_eq_preimage) is contained in U. The hypothesis gives integral_U A(Du(x))[Dzeta(x - de)] dx = - integral_U <zeta(x - de), g(x)> dx. The integrands vanish outside K + de, so these are integrals over R^n; the right one is - integral R3, and translating x = y + de in the left one gives (E1) integral F1 = - integral R3. (Equivalently integral F1 = - integral <zeta(y), g(y + de)> dy, and integral <zeta(y), g(y + de)> dy = integral R3 by translation.)
7. Subtracting (E2) from (E1) and using step 4 (integral_sub): integral (F1 - F2) = integral R2 - integral R3 = integral (R2 - R3) = integral <zeta(x) - zeta(x - de), g(x)> dx (inner_sub_left).
8. Pointwise FTC. Fix y in K. h(t) := A(P_t(y)) in L* has derivative h'(t) = B(P_t(y))[Delta(y)] (chain rule: t -> P_t(y) is affine with derivative Delta(y)), continuous in t. By the fundamental theorem of calculus (intervalIntegral.integral_eq_sub_of_hasDerivAt), A(Du(y + de)) - A(Du(y)) = h(1) - h(0) = integral_0^1 B(P_t(y))[Delta(y)] dt, since P_1(y) = Du(y + de) and P_0(y) = Du(y). Evaluating at Dzeta(y) (ContinuousLinearMap.intervalIntegral_apply): F1(y) - F2(y) = integral_0^1 B(P_t(y))[Delta(y)][Dzeta(y)] dt. As Delta(y) = d (d^{-1}Delta(y)) and B(P_t(y)) is linear in its first argument, the integrand equals d B(P_t(y))[d^{-1}Delta(y)][Dzeta(y)], so F1(y) - F2(y) = d I(y). For y not in K both sides vanish (Dzeta(y) = 0). Hence integral (F1 - F2) = d integral I (integral_const_mul).
9. The sibling dohr_eb_elc2_shift_ibp, applied to (U, g, zeta, e, d) (its hypothesis is step 2: x + (td)e in U for x in tsupport zeta and t in [0,1]), gives integral <zeta(x) - zeta(x - de), g(x)> dx = d integral J.
10. Steps 7, 8 and 9 give d integral I = d integral J. Since d is nonzero, integral I = integral J, and step 1 gives integral_V I = integral_V J. QED
Instance note: the FTC in L* and the evaluation of B need set_option maxSynthPendingDepth 5 (checked; the realization below uses it).
Lean realization, checked at the pin (Lean 4.35.0-rc3, Mathlib 25730c7c): compiled inside namespace GMT.Ch05 of a scratch copy of GMT/Ch05/Submission.lean (contract opens in effect); #print axioms gives only propext, Classical.choice, Quot.sound; the NodeSolution file generated by verifier/gmt-compare.py (exact Submission.dohr_eb_elc2_dq_weak_equation) closes against it.
```lean
set_option maxSynthPendingDepth 5 in
theorem Submission.dohr_eb_elc2_dq_weak_equation : ∀ (n ℓ : ℕ) (Ψ : (Rn n →L[ℝ] Rn ℓ) → ℝ) (U V : Set (Rn n)) (u g : Rn n → Rn ℓ) (e : Rn n) (d : ℝ), ContDiff ℝ 2 Ψ → IsOpen U → IsOpen V → ContDiffOn ℝ 1 u U → ContinuousOn g U → d ≠ 0 → (∀ x ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, x + (t * d) • e ∈ U) → (∀ φ : Rn n → Rn ℓ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U → ∫ x in U, fderiv ℝ Ψ (fderiv ℝ u x) (fderiv ℝ φ x) = -∫ x in U, inner ℝ (φ x) (g x)) → ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ V → ∫ x in V, (∫ t in (0 : ℝ)..1, fderiv ℝ (fderiv ℝ Ψ) (fderiv ℝ u x + t • (fderiv ℝ u (x + d • e) - fderiv ℝ u x)) (d⁻¹ • (fderiv ℝ u (x + d • e) - fderiv ℝ u x)) (fderiv ℝ ζ x)) = ∫ x in V, inner ℝ (∫ t in (0 : ℝ)..1, g (x + (t * d) • e)) (fderiv ℝ ζ x e) := by
  intro n ℓ Ψ U V u g e d hΨ hU hV hu hg hd hseg hweak ζ hζ hζc hζV
  set K := tsupport ζ with hK_def
  have hKc : IsCompact K := hζc
  have hKcl : IsClosed K := isClosed_tsupport ζ
  have hKV : K ⊆ V := hζV
  have hsegK : ∀ y ∈ K, ∀ t ∈ Icc (0:ℝ) 1, y + (t * d) • e ∈ U := fun y hy => hseg y (hKV hy)
  have hKU : K ⊆ U := fun y hy => by simpa using hsegK y hy 0 (by simp)
  have hKdU : ∀ y ∈ K, y + d • e ∈ U := fun y hy => by simpa using hsegK y hy 1 (by simp)
  have hDuAt : ∀ y ∈ U, ContinuousAt (fderiv ℝ u) y := fun y hy =>
    (hu.continuousOn_fderiv_of_isOpen hU le_rfl).continuousAt (hU.mem_nhds hy)
  have hgAt : ∀ y ∈ U, ContinuousAt g y := fun y hy => hg.continuousAt (hU.mem_nhds hy)
  have hDζ : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv one_ne_zero
  have hζcont : Continuous ζ := hζ.continuous
  have hDζ0 : ∀ y ∉ K, fderiv ℝ ζ y = 0 := fun y hy => fderiv_of_notMem_tsupport ℝ hy
  have hζ0 : ∀ y ∉ K, ζ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hA1 : ContDiff ℝ 1 (fderiv ℝ Ψ) := hΨ.fderiv_right (by norm_num)
  have hAc : Continuous (fderiv ℝ Ψ) := hA1.continuous
  have hBc : Continuous (fderiv ℝ (fderiv ℝ Ψ)) := hA1.continuous_fderiv one_ne_zero
  have hAd : Differentiable ℝ (fderiv ℝ Ψ) := hA1.differentiable one_ne_zero
  have cont_of : ∀ (F : Rn n → ℝ) (C : Set (Rn n)), IsClosed C → (∀ y ∉ C, F y = 0) →
      (∀ y ∈ C, ContinuousAt F y) → Continuous F := by
    intro F C hC h0 hcont
    rw [continuous_iff_continuousAt]
    intro y
    by_cases hy : y ∈ C
    · exact hcont y hy
    · have hev : F =ᶠ[𝓝 y] fun _ => (0:ℝ) := by
        filter_upwards [hC.isOpen_compl.mem_nhds hy] with z hz using h0 z hz
      exact continuousAt_const.congr hev.symm
  have integ_of : ∀ (F : Rn n → ℝ) (C : Set (Rn n)), IsCompact C → (∀ y ∉ C, F y = 0) →
      (∀ y ∈ C, ContinuousAt F y) → Integrable F := by
    intro F C hC h0 hcont
    exact (cont_of F C hC.isClosed h0 hcont).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hC h0)
  -- the four (five) integrands
  set F1 : Rn n → ℝ := fun y => fderiv ℝ Ψ (fderiv ℝ u (y + d • e)) (fderiv ℝ ζ y) with hF1
  set F2 : Rn n → ℝ := fun y => fderiv ℝ Ψ (fderiv ℝ u y) (fderiv ℝ ζ y) with hF2
  set R2 : Rn n → ℝ := fun y => inner ℝ (ζ y) (g y) with hR2
  set R3 : Rn n → ℝ := fun x => inner ℝ (ζ (x - d • e)) (g x) with hR3
  set Kd : Set (Rn n) := (fun y => y + d • e) '' K with hKd
  have hKdc : IsCompact Kd := hKc.image (continuous_id.add continuous_const)
  have hmemKd : ∀ x, x - d • e ∈ K → x ∈ Kd := fun x hx => ⟨x - d • e, hx, by simp⟩
  have hKdU' : Kd ⊆ U := by rintro _ ⟨y, hy, rfl⟩; exact hKdU y hy
  have hF1i : Integrable F1 := by
    refine integ_of F1 K hKc (fun y hy => by simp [hF1, hDζ0 y hy]) (fun y hy => ?_)
    have h1 : ContinuousAt (fun y => fderiv ℝ u (y + d • e)) y :=
      (hDuAt _ (hKdU y hy)).comp_of_eq (continuous_id.add continuous_const).continuousAt rfl
    exact (hAc.continuousAt.comp h1).clm_apply hDζ.continuousAt
  have hF2i : Integrable F2 := by
    refine integ_of F2 K hKc (fun y hy => by simp [hF2, hDζ0 y hy]) (fun y hy => ?_)
    exact (hAc.continuousAt.comp (hDuAt y (hKU hy))).clm_apply hDζ.continuousAt
  have hR2i : Integrable R2 := by
    refine integ_of R2 K hKc (fun y hy => by simp [hR2, hζ0 y hy]) (fun y hy => ?_)
    exact hζcont.continuousAt.inner (hgAt y (hKU hy))
  have hR3i : Integrable R3 := by
    refine integ_of R3 Kd hKdc (fun x hx => ?_) (fun x hx => ?_)
    · have : x - d • e ∉ K := fun h => hx (hmemKd x h)
      simp [hR3, hζ0 _ this]
    · have h1 : ContinuousAt (fun x => ζ (x - d • e)) x :=
        (hζcont.comp (continuous_sub_right _)).continuousAt
      exact h1.inner (hgAt x (hKdU' hx))
  -- weak equation with ζ
  have hE2 : ∫ y, F2 y = -∫ y, R2 y := by
    have h := hweak ζ hζ hζc hKU
    have hl : ∫ x in U, fderiv ℝ Ψ (fderiv ℝ u x) (fderiv ℝ ζ x) = ∫ y, F2 y := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have : x ∉ K := fun h' => hx (hKU h')
      simp [hDζ0 x this]
    have hr : ∫ x in U, inner ℝ (ζ x) (g x) = ∫ y, R2 y := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have : x ∉ K := fun h' => hx (hKU h')
      simp [hζ0 x this]
    rw [hl, hr] at h
    exact h
  -- weak equation with the translate
  set φ1 : Rn n → Rn ℓ := fun x => ζ (x - d • e) with hφ1
  have hφ1C : ContDiff ℝ 1 φ1 := hζ.comp (contDiff_id.sub contDiff_const)
  have hφ1c : HasCompactSupport φ1 :=
    hζc.comp_isClosedEmbedding (Homeomorph.subRight (d • e)).isClosedEmbedding
  have hφ1ts : tsupport φ1 ⊆ U := by
    intro x hx
    have h := (tsupport_comp_eq_preimage ζ (Homeomorph.subRight (d • e))).subset hx
    have hxK : x - d • e ∈ K := h
    simpa using hKdU _ hxK
  have hφ1D : ∀ x, fderiv ℝ φ1 x = fderiv ℝ ζ (x - d • e) := fun x => fderiv_comp_sub (d • e)
  have hE1 : ∫ y, F1 y = -∫ y, inner ℝ (ζ y) (g (y + d • e)) := by
    have h := hweak φ1 hφ1C hφ1c hφ1ts
    have hl : ∫ x in U, fderiv ℝ Ψ (fderiv ℝ u x) (fderiv ℝ φ1 x) =
        ∫ x, fderiv ℝ Ψ (fderiv ℝ u x) (fderiv ℝ ζ (x - d • e)) := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
      · simp only [hφ1D]
      · intro x hx
        have : x - d • e ∉ K := fun h' => hx (hKdU' (hmemKd x h'))
        simp [hφ1D, hDζ0 _ this]
    have hr : ∫ x in U, inner ℝ (φ1 x) (g x) = ∫ x, R3 x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have : x - d • e ∉ K := fun h' => hx (hKdU' (hmemKd x h'))
      simp [hφ1, hζ0 _ this]
    have hl' : ∫ x, fderiv ℝ Ψ (fderiv ℝ u x) (fderiv ℝ ζ (x - d • e)) = ∫ y, F1 y := by
      rw [← integral_add_right_eq_self _ (d • e)]
      simp [hF1]
    have hr' : ∫ x, R3 x = ∫ y, inner ℝ (ζ y) (g (y + d • e)) := by
      rw [← integral_add_right_eq_self _ (d • e)]
      simp [hR3]
    rw [hl, hr, hl', hr'] at h
    exact h
  have hR1R3 : ∫ y, inner ℝ (ζ y) (g (y + d • e)) = ∫ x, R3 x := by
    rw [← integral_add_right_eq_self R3 (d • e)]
    simp [hR3]
  -- (E3)
  have hE3 : ∫ y, (F1 y - F2 y) = ∫ x, inner ℝ (ζ x - ζ (x - d • e)) (g x) := by
    rw [integral_sub hF1i hF2i, hE1, hE2, hR1R3]
    have : ∫ x, inner ℝ (ζ x - ζ (x - d • e)) (g x) = ∫ x, (R2 x - R3 x) := by
      congr 1; funext x; simp [hR2, hR3, inner_sub_left]
    rw [this, integral_sub hR2i hR3i]
    ring
  -- FTC
  set I : Rn n → ℝ := fun x => ∫ t in (0 : ℝ)..1, fderiv ℝ (fderiv ℝ Ψ)
    (fderiv ℝ u x + t • (fderiv ℝ u (x + d • e) - fderiv ℝ u x))
    (d⁻¹ • (fderiv ℝ u (x + d • e) - fderiv ℝ u x)) (fderiv ℝ ζ x) with hI
  set J : Rn n → ℝ := fun x => inner ℝ (∫ t in (0 : ℝ)..1, g (x + (t * d) • e)) (fderiv ℝ ζ x e)
    with hJ
  have hFTC : ∀ y, F1 y - F2 y = d * I y := by
    intro y
    by_cases hy : y ∈ K
    · set Δ := fderiv ℝ u (y + d • e) - fderiv ℝ u y with hΔ
      have hderiv : ∀ t ∈ uIcc (0:ℝ) 1, HasDerivAt (fun t : ℝ => fderiv ℝ Ψ (fderiv ℝ u y + t • Δ))
          (fderiv ℝ (fderiv ℝ Ψ) (fderiv ℝ u y + t • Δ) Δ) t := by
        intro t _
        have hl : HasDerivAt (fun t : ℝ => fderiv ℝ u y + t • Δ) Δ t := by
          simpa using ((hasDerivAt_id t).smul_const Δ).const_add (fderiv ℝ u y)
        exact (hAd (fderiv ℝ u y + t • Δ)).hasFDerivAt.comp_hasDerivAt t hl
      have hint : IntervalIntegrable
          (fun t : ℝ => fderiv ℝ (fderiv ℝ Ψ) (fderiv ℝ u y + t • Δ) Δ) volume 0 1 := by
        apply Continuous.intervalIntegrable
        exact (hBc.comp (by fun_prop)).clm_apply continuous_const
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
      simp only [one_smul, zero_smul, add_zero] at hftc
      have hP1 : fderiv ℝ u y + Δ = fderiv ℝ u (y + d • e) := by simp [hΔ]
      rw [hP1] at hftc
      have happ := congrArg (fun L => L (fderiv ℝ ζ y)) hftc
      try simp only at happ
      rw [ContinuousLinearMap.intervalIntegral_apply hint] at happ
      simp only [hF1, hF2, hI]
      rw [← ContinuousLinearMap.sub_apply, ← happ, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]
    · simp [hF1, hF2, hI, hDζ0 y hy]
  have hIBP := Submission.dohr_eb_elc2_shift_ibp n ℓ U g ζ e d hU hg hζ hζc hsegK
  have hmain : ∫ x, I x = ∫ x, J x := by
    have h1 : ∫ y, (F1 y - F2 y) = d * ∫ x, I x := by
      rw [← integral_const_mul]; congr 1; funext y; exact hFTC y
    have h2 : d * ∫ x, I x = d * ∫ x, J x := by rw [← h1, hE3, hIBP]
    exact mul_left_cancel₀ hd h2
  have hIV : ∫ x in V, I x = ∫ x, I x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have : x ∉ K := fun h' => hx (hKV h')
    simp [hI, hDζ0 x this]
  have hJV : ∫ x in V, J x = ∫ x, J x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have : x ∉ K := fun h' => hx (hKV h')
    simp [hJ, hDζ0 x this]
  calc _ = ∫ x in V, I x := rfl
    _ = ∫ x in V, J x := by rw [hIV, hJV, hmain]
    _ = _ := rfl
```

## Key steps

1. integrands vanish outside K = tsupport zeta; reduce integrals over V to R^n
2. test the weak equation with zeta and with zeta(. - de); translate; subtract (all integrands continuous with compact support)
3. FTC for t -> DPsi(Du(y) + t Delta(y)) gives F1 - F2 = d I pointwise
4. sibling shift_ibp turns integral <zeta(x) - zeta(x - de), g(x)> into d integral J
5. cancel d != 0

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp GMT/Ch05/Contract.lean against <snapshot>/project/GMT/Ch05/Contract.lean (read the IsLocallyHolderCkα and IsHolderCkα definitions)`
- `rg -l 'lebesgue_number_lemma|integral_add_right_eq_self|toContinuousLinearMap|tsupport_comp_eq_preimage|IsLocallyHolderCkα|difference quotient|intervalIntegral_integral_swap|integral_integral_swap|maxSynthPendingDepth' <snapshot>/project`
- `rg -l -i 'lebesgue_number|integral_add_right_eq_self|difference quotient|Holder' .lake/packages/simongmt/Poincare; rg -n -i holder .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/{FirstVariation,LpMeanCurvature}.lean`
- `grep -rn in <snapshot>/mathlib/Mathlib for: iteratedFDeriv_one_apply, norm_iteratedFDeriv_one, iteratedFDeriv_zero_eq_comp, iteratedFDeriv_succ_eq_comp_right, continuousMultilinearCurryFin1, contDiffOn_of_locally_contDiffOn, contDiffOn_zero, ContDiffOn.continuousOn_fderiv_of_isOpen, ContDiffOn.differentiableOn, ContDiff.fderiv_right, ContDiff.continuous_fderiv, lebesgue_number_lemma_of_metric, IsCompact.elim_finite_subcover, IsCompact.exists_bound_of_continuousOn, norm_image_sub_le_of_norm_fderiv_le (namespace Convex), norm_image_sub_le_of_norm_deriv_le_segment_01', integral_mul_right_eq_self (to_additive integral_add_right_eq_self), intervalIntegral.integral_eq_sub_of_hasDerivAt, integral_integral_swap, intervalIntegral_integral_swap, Measure.prod_restrict, IntegrableOn.of_forall_sdiff_eq_zero, ContinuousOn.integrableOn_compact, ContinuousOn.intervalIntegrable, ContinuousLinearMap.intervalIntegral_apply, ContinuousLinearMap.intervalIntegral_comp_comm, LinearMap.toContinuousLinearMap, setIntegral_congr_fun, setIntegral_eq_integral_of_forall_compl_eq_zero, fderiv_of_notMem_tsupport, fderiv_comp_sub, fderiv_comp_add_right, fderiv_const_smul, mulTSupport_comp_eq_preimage, HasCompactMulSupport.comp_isClosedEmbedding, HasCompactMulSupport.intro, Continuous.integrable_of_hasCompactSupport, integral_inner, intervalIntegral.norm_integral_le_of_norm_le_const, intervalIntegral.integral_mono_on, innerSL, EuclideanSpace.norm_single`
- `python3 scan of <run>/dag.json: lean_statements of the elliptic_bootstrap siblings; 'dohr_eb_elc2' name collisions; statements matching Lebesgue number / difference quotient / translat / bilinear form`
- `lake build GMT.Ch05.Submission in scratch /tmp/elc2-scratch-VvYZXQ/proj (Lean 4.35.0-rc3, shared lake-packages-25730c7c)`
- `lake env lean Checks/Children7.lean (seven child types in the replayed contract scope, generated with gmt-compare.py contract_scope)`
- `lake env lean Checks/Assembly.lean (frozen parent type from 6 child + 3 prerequisite axioms; #print axioms)`
- `lake env lean Checks/{C1feas,C2full,C3full,C4feas,C5feas,C6feas}.lean and Checks/EndToEnd.lean (complete child proofs; #print axioms)`
- `lake build of Submission.lean with the children under Submission.X; lake env lean Checks/NodeSolution_{0..7}.lean (gmt-compare.py child_modules output plus #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Module/Multilinear/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/L2Space.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpMeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`

The snapshot pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace Contract.lean and Submission.lean match the snapshot contract. The project snapshot contains nothing on difference quotients, Lebesgue numbers, translated weak equations or bilinear-form averaging; its only relevant match is the definition of IsLocallyHolderCkα. The simongmt Holder matches are Hoelder's integral inequality and are irrelevant. Every Mathlib declaration cited in the child proofs exists at the pin, for example: integral_add_right_eq_self (to_additive of integral_mul_right_eq_self, Group/Integral.lean:101), intervalIntegral_integral_swap (Integral/Prod.lean:483), Measure.prod_restrict (Measure/Prod.lean:778), IntegrableOn.of_forall_sdiff_eq_zero (IntegrableOn.lean), ContinuousLinearMap.intervalIntegral_apply/_comp_comm (IntervalIntegral/Basic.lean:863/870), LinearMap.toContinuousLinearMap (Module/FiniteDimension.lean:307), lebesgue_number_lemma_of_metric (Pseudo/Lemmas.lean:120), contDiffOn_of_locally_contDiffOn (ContDiff/Defs.lean:586), fderiv_of_notMem_tsupport (FDeriv/Const.lean:375), fderiv_comp_sub (FDeriv/Add.lean:892), mulTSupport_comp_eq_preimage (Topology/Algebra/Support.lean:106), continuousMultilinearCurryFin1 (Multilinear/Curry.lean:510). Some names are deprecated (ContinuousLinearMap.sub_apply/smul_apply, push_neg) but still compile. No 'dohr_eb_elc2' name exists in dag.json and no existing DAG node duplicates a child. Lean checks: (1) all seven child types elaborate in the replayed contract scope; (2) the frozen parent type follows from 6 child + 3 prerequisite axioms without sorry; (3) all seven children have complete proofs using only propext, Classical.choice and Quot.sound, and with them under their Submission.X names each generated NodeSolution closes. Instance note: the bilinear-form type over L = Rn n →L[ℝ] Rn ℓ needs set_option maxSynthPendingDepth 3 (5 for D^3 Psi and for the FTC in L*).
