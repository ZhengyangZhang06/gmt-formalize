# Parent-supplied natural-language proof

- Parent DAG node: `root.existence_of_minimizing_filling-a1.cone_filling-a1.cone_current-a1`
- Child DAG node: `root.existence_of_minimizing_filling-a1.cone_filling-a1.cone_current-a1.homotopy_formula-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 1(a) and 2 of the selected parent's supplied proof (Part B1–B2). That is Simon Ch. 6, 2.25, the homotopy formula for the affine homotopy h(t, x) = tx from f = 0 to g = id (book/chapter-06.txt lines 441–451). It is written at the level of forms through the Poincaré homotopy operator K_p with p = m + 1 ≥ 1. Three ingredients:
- the cancellation of the two alternating sums in the supplied Step 2 is taken from the comparator-accepted sibling euler_cartan (Cartan's formula for the Euler field X(z) = z), applied to the rescaled form z ↦ β(tz);
- smoothness and differentiation under the integral sign (supplied Step 1(a)) come from the sibling param_integral;
- the final integration is the fundamental theorem of calculus of the supplied Step 2.

Notation.
- E := ℝ^P = Euclid P. Λ^k := Covector E k, the continuous alternating k-linear maps E^k → ℝ; it is a complete real normed space with the operator norm.
- For α ∈ Λ^{k+1} and z ∈ E, ι_zα := α.curryLeft z ∈ Λ^k, so ι_zα(v_1, …, v_k) = α(z, v_1, …, v_k), the argument being Fin.cons z v.
- α ↦ α.curryLeft is the linear isometry curryLeftLI : Λ^{k+1} → L(E, Λ^k). Hence (α, z) ↦ ι_zα is continuous and bilinear, ι_z(cα) = c•ι_zα and ι_z(α + α') = ι_zα + ι_zα'.
- alt := ContinuousAlternatingMap.alternatizeUncurryFin : L(E, Λ^k) → Λ^{k+1} is continuous and linear (it is alternatizeUncurryFinCLM).
- For every k-form ω, dω(x) = exteriorDerivative ω x = extDeriv ω x = alt(Dω(x)), with Dω(x) = fderiv ℝ ω x.
- All integrals are interval integrals over [0, 1] = uIcc 0 1. As in the statement, Kβ(x) := ∫_0^1 t^m • ι_xβ(tx) dt and K(dβ)(x) := ∫_0^1 t^{m+1} • ι_x dβ(tx) dt.

1. Joint smoothness of the integrand. Define h : ℝ × E → Λ^m by h(t, z) := t^m • ι_zβ(tz), so that Kβ(x) = ∫_0^1 h(t, x) dt.
 - (t, z) ↦ tz is C^∞ and β is C^∞, so (t, z) ↦ β(tz) is C^∞.
 - Composing with the continuous linear map curryLeftLI gives the C^∞ map (t, z) ↦ β(tz).curryLeft ∈ L(E, Λ^m).
 - Applying it to the C^∞ map (t, z) ↦ z gives (t, z) ↦ ι_zβ(tz) C^∞ (ContDiff.clm_apply).
 - Multiplying by the C^∞ scalar t^m (ContDiff.smul) shows that h is C^∞.

2. Smoothness of Kβ and its derivative (sibling param_integral). Apply param_integral with N := P, the complete space V := Λ^m and h. Its first conjunct is (i): x ↦ ∫_0^1 h(t, x) dt = Kβ is C^∞. Its second conjunct gives, for every y ∈ E, HasFDerivAt Kβ (∫_0^1 D_z h(t, y) dt) y, where D_z h(t, y) := fderiv ℝ (z ↦ h(t, z)) y. Hence D(Kβ)(y) = ∫_0^1 D_z h(t, y) dt.

3. d commutes with the integral. Fix y ∈ E.
 - The map z ↦ (t, z) has derivative inr : E → ℝ × E, so by the chain rule D_z h(t, y) = Dh(t, y) ∘ inr.
 - t ↦ Dh(t, y) is continuous because h is C^1 (step 1), so t ↦ D_z h(t, y) is continuous and interval integrable on [0, 1].
 - Since alt is continuous linear it commutes with the interval integral (ContinuousLinearMap.intervalIntegral_comp_comm):
 d(Kβ)(y) = alt(D(Kβ)(y)) = alt(∫_0^1 D_z h(t, y) dt) = ∫_0^1 alt(D_z h(t, y)) dt = ∫_0^1 d(h(t, ·))(y) dt.
 - t ↦ d(h(t, ·))(y) = alt(D_z h(t, y)) is continuous, hence interval integrable.

4. Pointwise identity. Fix t ∈ ℝ. We show
 (★) d(h(t, ·))(y) + t^{m+1} • ι_y dβ(ty) = (m+1) • (t^m • β(ty)) + t^{m+1} • Dβ(ty)[y].
 (a) Let β_t(z) := β(tz). The map z ↦ tz has derivative t•id. By the chain rule β_t is differentiable at every z with Dβ_t(z) = Dβ(tz) ∘ (t•id) = t•Dβ(tz). Hence dβ_t(y) = alt(t•Dβ(ty)) = t•alt(Dβ(ty)) = t•dβ(ty) (alternatizeUncurryFin_smul), and Dβ_t(y)[y] = t•Dβ(ty)[y].
 (b) The sibling euler_cartan, applied to the (m+1)-form β_t (differentiable at y), gives
 d(z ↦ ι_zβ_t(z))(y) + ι_y(dβ_t(y)) = (m+1)•β_t(y) + Dβ_t(y)[y].
 Insert (a), use ι_y(t•α) = t•ι_yα, and note ι_zβ_t(z) = ι_zβ(tz) and β_t(y) = β(ty). This gives
 (★★) d(z ↦ ι_zβ(tz))(y) + t•ι_y dβ(ty) = (m+1)•β(ty) + t•Dβ(ty)[y].
 (c) As functions, h(t, ·) = t^m • (z ↦ ι_zβ(tz)). d commutes with multiplication by the constant t^m (extDeriv_smul), so d(h(t, ·))(y) = t^m • d(z ↦ ι_zβ(tz))(y). Multiply (★★) by t^m and use t^m•(t•α) = t^{m+1}•α and t^m•((m+1)•α) = (m+1)•(t^m•α). This gives (★).
 Remark. (★) is exactly the cancellation in the supplied Step 2. Expand both exterior derivatives with extDeriv_apply:
 - the alternating sums of terms t^{m+1}·Dβ(ty)[v_i](y, v without v_i) cancel;
 - the terms t^m·β(ty)(v_i, v without v_i) = (−1)^i·t^m·β(ty)(v) add up to (m+1)·t^m·β(ty)(v);
 - the term t^{m+1}·Dβ(ty)[y](v) remains.
 euler_cartan is the accepted packaging of this computation.

5. Fundamental theorem of calculus. Let φ(t) := t^{m+1} • β(ty) ∈ Λ^{m+1}.
 - t ↦ t^{m+1} has derivative (m+1)t^m.
 - t ↦ ty has derivative y, so by the chain rule t ↦ β(ty) has derivative Dβ(ty)[y].
 - By the product rule (HasDerivAt.smul), φ has derivative φ'(t) = (m+1)•(t^m•β(ty)) + t^{m+1}•Dβ(ty)[y] at every t.
 - φ' is continuous (β and Dβ are continuous), hence interval integrable.
 By intervalIntegral.integral_eq_sub_of_hasDerivAt, ∫_0^1 φ'(t) dt = φ(1) − φ(0) = 1^{m+1}•β(1·y) − 0^{m+1}•β(0·y) = β(y), because m + 1 ≥ 1.

6. Conclusion.
 - t ↦ t^{m+1} • ι_y dβ(ty) is continuous, hence interval integrable: dβ = alt ∘ Dβ is continuous since β is C^1, and (α, z) ↦ ι_zα is continuous.
 - t ↦ d(h(t, ·))(y) is interval integrable by step 3.
 By step 3, additivity of the interval integral, (★) and step 5:
 d(Kβ)(y) + K(dβ)(y) = ∫_0^1 d(h(t, ·))(y) dt + ∫_0^1 t^{m+1}•ι_y dβ(ty) dt = ∫_0^1 [d(h(t, ·))(y) + t^{m+1}•ι_y dβ(ty)] dt = ∫_0^1 φ'(t) dt = β(y).
 Since y ∈ E was arbitrary, this is (ii); (i) is step 2. ∎

Lean implementation note. The proof below was compiled during decomposition after `import GMT.Ch07.Submission` in namespace GMT.Ch07 with the contract's opens. It uses the two sibling types only. With the accepted proofs of param_integral and euler_cartan spliced in, #print axioms gives propext, Classical.choice, Quot.sound.
Two pitfalls:
(a) Under `open scoped ENNReal` the token `∞` is ENNReal's ⊤, so write `(⊤ : ℕ∞)` for smoothness orders.
(b) Instance synthesis fails for `ENormedAddMonoid (Euclid P →L[ℝ] Covector (Euclid P) m)`. Also, a hand-written type `Covector … →L[ℝ] (Euclid P →L[ℝ] Covector …)` picks ContinuousAlternatingMap's own topology instance, which does not unify with the norm topology required by ContinuousLinearMap.contDiff and Continuous.intervalIntegrable. The proof therefore states two helper facts over arbitrary normed spaces inside the proof and instantiates them with W := Covector: `gen2` (p ↦ p.1^m • L (g p) p.2 is C^∞) and `key` (L (∫ F) = ∫ L ∘ F for continuous F).

```lean
theorem Submission.ecf_cc_radial_homotopy_formula : ∀ (P m : ℕ) (β : DifferentialForm (Euclid P) (m + 1)), ContDiff ℝ (⊤ : ℕ∞) β → ContDiff ℝ (⊤ : ℕ∞) (fun x : Euclid P => ∫ t in (0 : ℝ)..1, t ^ m • (β (t • x)).curryLeft x) ∧ ∀ x : Euclid P, exteriorDerivative (fun y : Euclid P => ∫ t in (0 : ℝ)..1, t ^ m • (β (t • y)).curryLeft y) x + ∫ t in (0 : ℝ)..1, t ^ (m + 1) • (exteriorDerivative β (t • x)).curryLeft x = β x := by
  intro P m β hβ
  -- Step 1: joint smoothness of `h (t, z) = t ^ m • ι_z β (t • z)`
  let h : ℝ × Euclid P → Covector (Euclid P) m := fun p => p.1 ^ m • (β (p.1 • p.2)).curryLeft p.2
  -- generic helpers (stated over arbitrary normed spaces, to avoid instance diamonds of `Covector`)
  have gen2 : ∀ (W₁ W₃ : Type) [NormedAddCommGroup W₁] [NormedSpace ℝ W₁] [NormedAddCommGroup W₃]
      [NormedSpace ℝ W₃] (L : W₁ →L[ℝ] (Euclid P →L[ℝ] W₃)) (g : ℝ × Euclid P → W₁),
      ContDiff ℝ (⊤ : ℕ∞) g → ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Euclid P => p.1 ^ m • L (g p) p.2) := by
    intro W₁ W₃ _ _ _ _ L g hg
    exact (contDiff_fst.pow m).smul ((L.contDiff.comp hg).clm_apply contDiff_snd)
  have hhs : ContDiff ℝ (⊤ : ℕ∞) h :=
    gen2 (Covector (Euclid P) (m + 1)) (Covector (Euclid P) m)
      (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Euclid P) (F := ℝ) (n := m)).toContinuousLinearMap
      (fun p => β (p.1 • p.2)) (hβ.comp (contDiff_fst.smul contDiff_snd))
  -- Step 2: `param_integral`
  obtain ⟨hKs, hKd⟩ := Submission.cmcdt_lpo_slice_param_integral P (Covector (Euclid P) m) h hhs
  refine ⟨hKs, fun y => ?_⟩
  -- Step 3: `d` commutes with the integral
  have hpart : ∀ t : ℝ, HasFDerivAt (fun z : Euclid P => h (t, z))
      ((fderiv ℝ h (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ (Euclid P))) y := fun t =>
    (hhs.differentiable (by simp) (t, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right t y)
  have hpart_cont : Continuous (fun t : ℝ => fderiv ℝ (fun z : Euclid P => h (t, z)) y) := by
    have heq : (fun t : ℝ => fderiv ℝ (fun z : Euclid P => h (t, z)) y) =
        fun t => (fderiv ℝ h (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ (Euclid P)) := by
      funext t
      exact (hpart t).fderiv
    rw [heq]
    exact ((hhs.continuous_fderiv (by simp)).comp (continuous_id.prodMk continuous_const)).clm_comp
      continuous_const
  have hdK : exteriorDerivative (fun y : Euclid P => ∫ t in (0 : ℝ)..1, t ^ m • (β (t • y)).curryLeft y) y =
      ∫ t in (0 : ℝ)..1, exteriorDerivative (fun z : Euclid P => h (t, z)) y := by
    have hfd : fderiv ℝ (fun y : Euclid P => ∫ t in (0 : ℝ)..1, h (t, y)) y =
        ∫ t in (0 : ℝ)..1, fderiv ℝ (fun z : Euclid P => h (t, z)) y := (hKd y).fderiv
    change ContinuousAlternatingMap.alternatizeUncurryFin
        (fderiv ℝ (fun y : Euclid P => ∫ t in (0 : ℝ)..1, h (t, y)) y) =
      ∫ t in (0 : ℝ)..1, ContinuousAlternatingMap.alternatizeUncurryFin
        (fderiv ℝ (fun z : Euclid P => h (t, z)) y)
    rw [hfd]
    have key : ∀ (W W' : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
        [NormedAddCommGroup W'] [NormedSpace ℝ W'] [CompleteSpace W']
        (F : ℝ → (Euclid P →L[ℝ] W)) (L : (Euclid P →L[ℝ] W) →L[ℝ] W'),
        Continuous F → L (∫ t in (0 : ℝ)..1, F t) = ∫ t in (0 : ℝ)..1, L (F t) := by
      intro W W' _ _ _ _ _ _ F L hF
      exact (L.intervalIntegral_comp_comm (hF.intervalIntegrable 0 1)).symm
    exact key (Covector (Euclid P) m) (Covector (Euclid P) (m + 1))
      (fun t : ℝ => fderiv ℝ (fun z : Euclid P => h (t, z)) y)
      (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Euclid P) ℝ) hpart_cont
  -- Step 4: the pointwise identity, from `euler_cartan` applied to `z ↦ β (t • z)`
  have hpt : ∀ t : ℝ, exteriorDerivative (fun z : Euclid P => h (t, z)) y +
      t ^ (m + 1) • (exteriorDerivative β (t • y)).curryLeft y =
      ((m : ℝ) + 1) • (t ^ m • β (t • y)) + t ^ (m + 1) • fderiv ℝ β (t • y) y := by
    intro t
    set βt : DifferentialForm (Euclid P) (m + 1) := fun z => β (t • z) with hβtdef
    have hβt : ∀ z, HasFDerivAt βt (t • fderiv ℝ β (t • z)) z := by
      intro z
      have h1 : HasFDerivAt (fun z : Euclid P => t • z) (t • ContinuousLinearMap.id ℝ (Euclid P)) z :=
        (hasFDerivAt_id z).const_smul t
      have h2 : HasFDerivAt βt ((fderiv ℝ β (t • z)).comp (t • ContinuousLinearMap.id ℝ (Euclid P))) z :=
        (hβ.differentiable (by simp) (t • z)).hasFDerivAt.comp z h1
      convert h2 using 1
      refine ContinuousLinearMap.ext fun u => ?_
      simp
    have hEC := Submission.dtc_cone_euler_cartan P m βt y (hβt y).differentiableAt
    have hdβt : exteriorDerivative βt y = t • exteriorDerivative β (t • y) := by
      change ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ βt y) =
        t • ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ β (t • y))
      rw [(hβt y).fderiv, ContinuousAlternatingMap.alternatizeUncurryFin_smul]
    have hDβt : fderiv ℝ βt y y = t • fderiv ℝ β (t • y) y := by
      rw [(hβt y).fderiv]
      rfl
    rw [hdβt, hDβt, ContinuousAlternatingMap.curryLeft_smul, ContinuousLinearMap.smul_apply] at hEC
    simp only [hβtdef] at hEC
    have hsm : exteriorDerivative (fun z : Euclid P => h (t, z)) y =
        t ^ m • exteriorDerivative (fun z : Euclid P => (β (t • z)).curryLeft z) y := by
      have heq : (fun z : Euclid P => h (t, z)) = t ^ m • (fun z : Euclid P => (β (t • z)).curryLeft z) := rfl
      rw [heq]
      exact extDeriv_smul (t ^ m) _
    rw [hsm]
    linear_combination (norm := module) (t ^ m) • hEC
  -- Step 5: the fundamental theorem of calculus for `φ (t) = t ^ (m + 1) • β (t • y)`
  have hφ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => s ^ (m + 1) • β (s • y))
      (((m : ℝ) + 1) • (t ^ m • β (t • y)) + t ^ (m + 1) • fderiv ℝ β (t • y) y) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => s ^ (m + 1)) (((m : ℝ) + 1) * t ^ m) t := by
      simpa using hasDerivAt_pow (m + 1) t
    have h3 : HasDerivAt (fun s : ℝ => s • y) y t := by
      simpa using (hasDerivAt_id t).smul_const y
    have h2 : HasDerivAt (fun s : ℝ => β (s • y)) (fderiv ℝ β (t • y) y) t :=
      (hβ.differentiable (by simp) (t • y)).hasFDerivAt.comp_hasDerivAt t h3
    convert h1.smul h2 using 1
    module
  have hc1 : Continuous (fun t : ℝ => β (t • y)) := hβ.continuous.comp (continuous_id.smul continuous_const)
  have hφint : IntervalIntegrable (fun t : ℝ => ((m : ℝ) + 1) • (t ^ m • β (t • y)) +
      t ^ (m + 1) • fderiv ℝ β (t • y) y) MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    have hc2 : Continuous (fun t : ℝ => fderiv ℝ β (t • y) y) :=
      ((hβ.continuous_fderiv (by simp)).comp (continuous_id.smul continuous_const)).clm_apply
        continuous_const
    have hc3 : Continuous (fun t : ℝ => ((m : ℝ) + 1) • (t ^ m • β (t • y))) :=
      ((continuous_pow m).smul hc1).const_smul ((m : ℝ) + 1)
    have hc4 : Continuous (fun t : ℝ => t ^ (m + 1) • fderiv ℝ β (t • y) y) :=
      (continuous_pow (m + 1)).smul hc2
    exact hc3.add hc4
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hφ t) hφint
  have hφ1 : (1 : ℝ) ^ (m + 1) • β ((1 : ℝ) • y) = β y := by simp
  have hφ0 : (0 : ℝ) ^ (m + 1) • β ((0 : ℝ) • y) = 0 := by simp
  rw [hφ1, hφ0, sub_zero] at hFTC
  -- Step 6: conclusion
  have hdβc : Continuous (exteriorDerivative β) :=
    (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Euclid P) ℝ).continuous.comp
      (hβ.continuous_fderiv (by simp))
  have hint2 : IntervalIntegrable (fun t : ℝ => t ^ (m + 1) • (exteriorDerivative β (t • y)).curryLeft y)
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact (continuous_pow (m + 1)).smul
      (((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Euclid P) (F := ℝ) (n := m + 1)).continuous.comp
        (hdβc.comp (continuous_id.smul continuous_const))).clm_apply continuous_const)
  have hint1 : IntervalIntegrable (fun t : ℝ => exteriorDerivative (fun z : Euclid P => h (t, z)) y)
      MeasureTheory.volume 0 1 :=
    ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Euclid P) ℝ).continuous.comp
      hpart_cont).intervalIntegrable 0 1
  rw [hdK, ← intervalIntegral.integral_add hint1 hint2, ← hFTC]
  exact intervalIntegral.integral_congr (fun t _ => hpt t)
```

## Key steps

1. h(t, z) := t^m • ι_zβ(tz) is C^∞ on ℝ × ℝ^P (β ∘ (t, z) ↦ tz, the continuous linear curryLeftLI, ContDiff.clm_apply, smul by t^m).
2. Sibling param_integral: Kβ = ∫_0^1 h(t, ·) dt is C^∞ (conclusion (i)) and D(Kβ)(y) = ∫_0^1 D_z h(t, y) dt.
3. d(Kβ)(y) = alt(D(Kβ)(y)) = ∫_0^1 d(h(t, ·))(y) dt, because alt = alternatizeUncurryFinCLM is continuous linear and t ↦ D_z h(t, y) = Dh(t, y) ∘ inr is continuous.
4. Sibling euler_cartan for β_t(z) = β(tz), with Dβ_t = t·Dβ(t·) and dβ_t = t·dβ(t·), times t^m: d(h(t,·))(y) + t^{m+1} ι_y dβ(ty) = (m+1)t^m β(ty) + t^{m+1} Dβ(ty)[y] = φ'(t), where φ(t) = t^{m+1} β(ty).
5. FTC: ∫_0^1 φ' = φ(1) − φ(0) = β(y) since m + 1 ≥ 1; adding the two (continuous, hence integrable) integrands gives d(Kβ)(y) + K(dβ)(y) = β(y) (conclusion (ii)).

## Reference use

### local-project

Queries:
- `sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (all three e4148e7f9503aa28930a…; manifest: project b4d606db, Mathlib 25730c7c)`
- `grep -n in local-references/123e8435b4a2469b/mathlib/Mathlib: curryLeft_apply_apply|curryLeft_add|curryLeft_smul|curryLeft_zero|curryLeftLI (Analysis/Normed/Module/Alternating/Curry.lean); def alternatizeUncurryFin|alternatizeUncurryFinCLM_apply|alternatizeUncurryFin_smul (Analysis/Normed/Module/Alternating/Uncurry/Fin.lean); def extDeriv|extDeriv_smul|EventuallyEq.extDeriv_eq|extDeriv_apply (Analysis/Calculus/DifferentialForm/Basic.lean); isClosedMap_snd_of_compactSpace (Topology/Maps/Proper/Basic.lean:337); instance compactSpace_Icc (Topology/Order/Compact.lean:113); HasCompactSupport.smul_right (Topology/Algebra/Support.lean:466); ContDiff.fderiv_right (Analysis/Calculus/ContDiff/Comp.lean:750); IsBounded.subset_closedBall (Topology/MetricSpace/Bounded.lean:101); def apply (Topology/Algebra/Module/Alternating/Topology.lean:294); exists_contDiff_support_eq_eq_one_iff`
- `python3 -I over dag.json (2416 nodes): regex scans homotop|curryLeft|Poincar|cutoff|covectorEuclideanNorm|EqOn|Disjoint … → X.support ⊆|∃ ζ … ContDiff … = 1; status, candidate_commit and child/dependency closure of the 10 reuse targets; byte equality of their lean_statement; absence of ecf_cc_radial_homotopy_formula and ecf_cc_radial_homotopy_toolkit`
- `git show <candidate>:GMT/Ch07/Submission.lean for the 10 reused candidates: exact `theorem Submission.X : <frozen type> := by` header, contract prefix identical to the workspace contract, only sorry is main_theorem, 13 distinct theorem names`
- `sed of /runtime/flows/gmt-claude-a72bcd2dc14b/_recursive_lean/runtime.py (_existing_lean_name_problem, _accepted_checkpoint) and prompts.py (DECOMPOSE, DECOMPOSITION_AUDIT, SPECULATIVE_PARENT_TASK)`
- `cat .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Forms,Mass,CurrentLocalEquality,FormSupNorm}.lean`
- `sed -n 441,456p and 528,551p book/chapter-06.txt (Simon 6.2.25, 2.30–2.32)`
- `lean (LEAN_PATH = local copy of the lake libraries) on /tmp/cone-current-split/lean/{Probe,Types,Assembly,AssemblyAx,ProofA,ProofB,TC,Full}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Maps/Proper/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-existence-of-minimizing-filling-a1-cone-filling-a1-cone-current-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-existence-of-minimizing-filling-a1-cone-filling-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-euler-cartan-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-9310c84433/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-f92df94753/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-14afd577b6/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1-test-form-approx-a1-norm-props-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-82644d9359/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-eva-463e096c91/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-9b01f284ba/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-vanish-off-support-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1-support-a67ad69f81/parent-supplied-natural-proof.md`
- `/runtime/flows/gmt-claude-a72bcd2dc14b/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-a72bcd2dc14b/_recursive_lean/prompts.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/cone-current-split/lean/Types.lean`
- `/tmp/cone-current-split/lean/Assembly.lean`
- `/tmp/cone-current-split/lean/ProofA.lean`
- `/tmp/cone-current-split/lean/ProofB.lean`
- `/tmp/cone-current-split/lean/Full.lean`

The snapshot is project b4d606db with Mathlib 25730c7c. Its Ch07 Contract.lean is byte-identical (sha256 e4148e7f9503aa28930a…) to the workspace Contract.lean and Submission.lean, so the child types are checked against the frozen contract.

Snapshot contents:
- The pinned Mathlib supplies every tool the new children and the assembly cite: curryLeft, curryLeftLI, curryLeft_apply_apply/add/smul/zero, alternatizeUncurryFin(CLM) with alternatizeUncurryFin_smul, extDeriv = alternatizeUncurryFin ∘ fderiv, extDeriv_smul, Filter.EventuallyEq.extDeriv_eq, ContinuousAlternatingMap.apply, ContinuousLinearMap.intervalIntegral_comp_comm, intervalIntegral.integral_eq_sub_of_hasDerivAt, isClosedMap_snd_of_compactSpace, compactSpace_Icc, HasCompactSupport.smul_right, ContDiff.fderiv_right and Bornology.IsBounded.subset_closedBall.
- Neither Mathlib nor SimonGMT has a Poincaré homotopy operator, cone current or homotopy formula for forms, so homotopy_formula and homotopy_toolkit are genuine new obligations.
- SimonGMT Chapter06 supplies the frozen objects GeometricCurrentOn, TestFormOn, boundary (boundary_apply) and exteriorDerivativeTestOn, plus covectorEuclideanNorm, massOn/mass, support/zeroRegion and GeometricCurrentOn.ext.

DAG scan (2416 nodes): ten accepted checkpoints match steps of the supplied proof with exactly usable types. They are cmcdt_lpo_slice_param_integral, dtc_cone_euler_cartan, cmcdt_lpo_slice_covector_bound, cmcdt_lp_covector_curryLeft_norm_le, rsd_mw_tfa_norm_props, cbrcs_ce_smooth_cutoff, cmr_abs_apply_le_massOn, cmcdt_lpo_tk_bounded_current, dtc_vanish_off_support and rsd_cmr_support_subset_of_vanish.
- Their frozen types are byte-identical to the reused children.
- Their candidate commits contain those exact headers, and the only sorry is main_theorem.
- Their closures are accepted.

Lean checks:
- All child types elaborate.
- A sorry-free chain built from the accepted candidate proofs, the two new proofs and the parent assembly compiles with propext, Classical.choice and Quot.sound only.
- One pitfall: Lean cannot synthesize ENormedAddMonoid on Euclid P →L[ℝ] Covector … The new children's compiled proofs avoid this with helper statements over generic normed spaces.
