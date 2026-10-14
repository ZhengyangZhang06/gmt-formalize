# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.projection-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 5–7 (and the cutoff used in step 8) of the parent proof, with Y_k = p_#(Γ_k⌞{g<t}) written as an integral; here U = B_{2R}, S = {g ≤ t}, F = {g < t} in the parent. Uses the sibling covector_bounds (b): |γ∘pL| ≤ |γ| for every l-covector γ on ℝⁿ.
0. Tools. (N1) |c·α| = |c|·|α| and |α| ≥ 0 for covectors (each coefficient α(e∘I) scales by c; covectorEuclideanNorm is the square root of the sum of their squares). (N2) |α| ≤ C_l‖α‖ with C_l := (number of strictly increasing I)^{1/2}, because |α(e∘I)| ≤ ‖α‖∏_k‖e_{I(k)}‖ = ‖α‖ (ContinuousMultilinearMap.le_opNorm); also α ↦ |α| is continuous (square root of a finite sum of squares of the continuous linear functionals α ↦ α(e∘I)). (N3) |(p^#γ)(x)| ≤ |γ(pL x)| for every form γ on ℝⁿ (covector_bounds (b)). (N4) Cutoffs: if K ⊆ ℝ^P is compact, O ⊆ ℝ^P open and K ⊆ O, there are r > 0 with cthickening(2r, K) ⊆ O compact (IsCompact.exists_cthickening_subset_open, IsCompact.cthickening) and, by exists_contDiff_support_eq_eq_one_iff (smooth Urysohn in a finite-dimensional space) applied to the open set thickening(2r, K) and the closed set cthickening(r, K) ⊆ thickening(2r, K), a smooth χ : ℝ^P → [0, 1] with support χ = thickening(2r, K) and χ = 1 on cthickening(r, K); then tsupport χ ⊆ cthickening(2r, K) ⊆ O is compact and χ = 1 on the open set O' := thickening(r, K) ⊇ K. (N5) If γ : ℝⁿ → Λ^l(ℝⁿ) is smooth then x ↦ (p^#γ)(x) = (ContinuousAlternatingMap.compContinuousLinearMapCLM pL)(γ(pL x)) is smooth (composition with the continuous linear maps pL and compContinuousLinearMapCLM pL), and (p^#γ)(x) = 0 whenever pL x ∉ tsupport γ. (N6) Locality and naturality of d: if two forms agree on a neighbourhood of x their exterior derivatives agree at x (extDeriv ω x = alternatizeUncurryFin (fderiv ℝ ω x) and Filter.EventuallyEq.fderiv_eq); for smooth γ on ℝⁿ, d(p^#γ)(x) = (p^#(dγ))(x) for every x (extDeriv_pullback with f := pL, which is smooth with fderiv ℝ pL x = pL).
1. (Integrability.) Let ω ∈ 𝒟ⁿ(U) and K := tsupport ω, compact and ⊆ U. The integrand Φ_ω(x) := ξ(x)((p^#ω)(x)) is μ-a.e. strongly measurable (ξ is a.e. strongly measurable into MultiVector P n, x ↦ (p^#ω)(x) is continuous, and the evaluation (ζ, β) ↦ ζ(β) is continuous; AEStronglyMeasurable.prodMk and Continuous.comp_aestronglyMeasurable). For μ-a.e. x: |Φ_ω(x)| ≤ |(p^#ω)(x)| ≤ |ω(pL x)| ≤ ‖ω‖_* := sup_y|ω(y)| < ∞ (N2, N3; y ↦ |ω(y)| is continuous with compact support), and Φ_ω(x) = 0 unless pL x ∈ K (N5). Hence |1_FΦ_ω| ≤ ‖ω‖_*·1_{S ∩ pL⁻¹(K)} μ-a.e. (F ⊆ S) and μ(S ∩ pL⁻¹(K)) < ∞ (compact by hypothesis), so 1_FΦ_ω is μ-integrable.
2. (Linearity.) ω ↦ p^#ω is linear (compContinuousLinearMap is linear in the alternating map) and ξ(x) is linear, so Φ_{aω+bη} = aΦ_ω + bΦ_η and, by step 1, Y₀(ω) := ∫_FΦ_ωdμ is an ℝ-linear functional on 𝒟ⁿ(U) (integral_add, integral_smul).
3. (Continuity.) Let ω_j → 0 in 𝒟ⁿ(U) (TestFormOnConverges): there is a compact K ⊆ U containing every tsupport ω_j, and ω_j → 0 uniformly on K (the k = 0 case: ‖iteratedFDeriv ℝ 0 ω_j x‖ = ‖ω_j x‖, norm_iteratedFDeriv_zero), while ω_j = 0 off K. By step 1 and (N2): |Y₀(ω_j)| ≤ μ(S ∩ pL⁻¹(K))·C_n·sup_{y∈K}‖ω_j(y)‖ → 0. Hence Y := ⟨Y₀, continuity⟩ ∈ 𝒟_n(U), and (i) holds by definition.
4. (Mass, (ii).) Let ω ∈ 𝒟ⁿ(U) with |ω(y)| ≤ 1 for all y. For μ-a.e. x ∈ F: |Φ_ω(x)| ≤ |ω(pL x)| ≤ 1, and Φ_ω(x) = 0 if pL x ∉ U (then pL x ∉ tsupport ω ⊆ U). So Y(ω) ≤ |Y(ω)| ≤ ∫_F1_{pL⁻¹(U)}dμ = μ(F ∩ pL⁻¹(U)) (norm_integral_le_of_norm_le / integral_mono_ae; trivial if the right side is ∞). Thus ofReal(Y ω) ≤ μ(F ∩ pL⁻¹U) for every ω ∈ massAdmissibleOn U n U, and M_U(Y) ≤ μ(F ∩ pL⁻¹(U)) (sSup_le).
5. (Extension, (iv).) Let ω ∈ 𝒟ⁿ(U), K := S ∩ pL⁻¹(tsupport ω) (compact by hypothesis). Take χ, O' from (N4) with O := ℝ^P and set ω' := χ·p^#ω. By (N5) ω' is smooth with tsupport ω' ⊆ tsupport χ compact, so ω' is a test n-form on ℝ^P. For x ∈ S: if x ∈ O', χ(x) = 1 and ω'(x) = (p^#ω)(x); if x ∉ O' then x ∉ K, so pL x ∉ tsupport ω and (p^#ω)(x) = 0 = ω'(x).
6. (Boundary mass, (iii).) Let W ⊆ U be open and γ ∈ massAdmissibleOn U d W: γ ∈ 𝒟^d(U), tsupport γ ⊆ W, |γ(y)| ≤ 1 for all y. K := S ∩ pL⁻¹(tsupport γ) is compact (hypothesis; tsupport γ is a compact subset of U) and contained in the open set pL⁻¹(W). Take χ, O' from (N4) with O := pL⁻¹(W) and set γ' := χ·p^#γ: a test d-form on ℝ^P (N5) with tsupport γ' ⊆ tsupport χ ⊆ pL⁻¹(W) and |γ'(x)| = χ(x)|(p^#γ)(x)| ≤ |γ(pL x)| ≤ 1 (N1, N3). So γ' ∈ massAdmissibleOn ℝ^P d (pL⁻¹W) and ofReal(∂Z(γ')) ≤ M_{pL⁻¹(W)}(∂Z) (GeometricCurrentOn.le_massOn). Claim: dγ'(x) = (p^#(dγ))(x) for every x ∈ S. If x ∈ O', γ' = p^#γ on the neighbourhood O' of x, so dγ'(x) = d(p^#γ)(x) = (p^#(dγ))(x) (N6). If x ∈ S ∖ O', then x ∉ K, so pL x ∉ tsupport γ; tsupport γ is closed, so γ = 0 on an open V ∋ pL x; then p^#γ and γ' vanish on the open neighbourhood pL⁻¹(V) of x, so dγ'(x) = 0, and dγ = 0 on V, so (p^#(dγ))(x) = 0 (N6). Now dγ ∈ 𝒟ⁿ(U), dγ' ∈ 𝒟ⁿ(ℝ^P) (exteriorDerivativeTestOn), F ⊆ S, and by (i), the representation of Z and the claim (setIntegral_congr on F): ∂Y(γ) = Y(dγ) = ∫_Fξ(x)((p^#(dγ))(x))dμ = ∫_Fξ(x)(dγ'(x))dμ = Z(dγ') = ∂Z(γ'). Hence ofReal(∂Y(γ)) ≤ M_{pL⁻¹(W)}(∂Z) for every admissible γ, and M_W(∂Y) ≤ M_{pL⁻¹(W)}(∂Z) (sSup_le). ∎

Verified Lean realization (supplementary). The single theorem below was compiled with `lake env lean` (Lean v4.35.0-rc3; project b4d606db, Mathlib 25730c7c, SimonGMT 2b366308) in a file that imports GMT.Ch07.Submission and reopens the frozen contract's namespace GMT.Ch07 with its `open`s, with the sibling dependency Submission.cbr_ci_pw_orthonormal_covector_bounds (covector_bounds) declared by its exact frozen Lean type: no errors and no warnings; `#count_heartbeats` reports 102743 heartbeats, below the default maxHeartbeats 200000 (no set_option); `#print axioms` lists propext, Classical.choice, Quot.sound and that sibling; inserted before main_theorem in GMT/Ch07/Submission.lean it passes the runtime's leaf source-delta check (one appended theorem under its exact name; no helper declaration, import, set_option or placeholder). Its local lemmas aux_* are proved inline and correspond to the numbered steps above: aux_smooth_cutoff is the cutoff construction (N4); aux_pullback_extension is (N5), (N6) together with the cutoff of steps 5–6 (for compact S ∩ pL⁻¹(tsupport γ) inside an open O it yields a test form γ' on ℝ^P with tsupport γ' ⊆ O, |γ'| ≤ |p^#γ|, γ' = p^#γ on S and dγ' = p^#(dγ) on S); aux_integral_estimate is step 1 with the uniform estimate used in step 3; aux_integral_current is steps 2–3 (the current Y with formula (i)); aux_mass_le is step 4 (ii); aux_boundary_mass_le is step 6 (iii); the final lines take (N3) from covector_bounds (b) and obtain (iv) from aux_pullback_extension with O := ℝ^P (step 5). It may be appended verbatim as the single leaf theorem:
```lean
theorem Submission.dmcbr_ci_pw_projected_current : ∀ (P d : ℕ) (v : Fin (d + 1) → Euclid P) (pL : Euclid P →L[ℝ] Euclid (d + 1)) (U : Set (Euclid (d + 1))) (S F : Set (Euclid P)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (Z : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)), Orthonormal ℝ v → (∀ (x : Euclid P) (i : Fin (d + 1)), pL x i = inner ℝ (v i) x) → IsOpen U → MeasurableSet F → F ⊆ S → (∀ K : Set (Euclid (d + 1)), IsCompact K → K ⊆ U → IsCompact (S ∩ pL ⁻¹' K)) → (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ β : Covector (Euclid P) (d + 1), |ξ x β| ≤ covectorEuclideanNorm β) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Z ω = ∫ x in F, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → ∃ Y : GeometricCurrentOn U (d + 1), (∀ ω : TestFormOn U (d + 1), Y ω = ∫ x in F, ξ x (((ω : DifferentialForm (Euclid (d + 1)) (d + 1)) (pL x)).compContinuousLinearMap pL) ∂μ) ∧ Y.massOn U ≤ μ (F ∩ pL ⁻¹' U) ∧ (∀ W : Set (Euclid (d + 1)), IsOpen W → W ⊆ U → Y.boundary.massOn W ≤ Z.boundary.massOn (pL ⁻¹' W)) ∧ ∀ ω : TestFormOn U (d + 1), ∃ ω' : TestFormOn (univ : Set (Euclid P)) (d + 1), ∀ x ∈ S, (ω' : DifferentialForm (Euclid P) (d + 1)) x = ((ω : DifferentialForm (Euclid (d + 1)) (d + 1)) (pL x)).compContinuousLinearMap pL := by
  have aux_smooth_cutoff : ∀ (P : ℕ) (K O : Set (Euclid P)), IsCompact K → IsOpen O → K ⊆ O → ∃ (χ : Euclid P → ℝ) (O' : Set (Euclid P)), ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ O ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ IsOpen O' ∧ K ⊆ O' ∧ ∀ x ∈ O', χ x = 1 := by
    intro P K O hK hO hKO
    -- Step 1: `cthickening δ K ⊆ O` for some `δ > 0`; put `r = δ/2`
    obtain ⟨δ, hδ, hδO⟩ := hK.exists_cthickening_subset_open hO hKO
    have hr : 0 < δ / 2 := half_pos hδ
    -- Steps 2-3: smooth Urysohn for the closed `cthickening r K` inside the open `thickening δ K`
    obtain ⟨χ, hχ, hrange, hsupp, hone⟩ :=
      exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) (isOpen_thickening (δ := δ) (E := K))
        (isClosed_cthickening (δ := δ / 2) (E := K))
        (cthickening_subset_thickening' hδ (half_lt_self hδ) K)
    -- Step 4: `tsupport χ = closure (thickening δ K) ⊆ cthickening δ K`
    have hts : tsupport χ ⊆ cthickening δ K := by
      rw [tsupport, hsupp]
      exact closure_thickening_subset_cthickening δ K
    -- Steps 5-7: compact support inside the compact `cthickening δ K`, the bounds `0 ≤ χ ≤ 1`, and
    -- `χ = 1` on `O' = thickening r K ⊆ cthickening r K`
    refine ⟨χ, thickening (δ / 2) K, hχ, ?_, hts.trans hδO, fun x => ?_, isOpen_thickening,
      self_subset_thickening hr K, fun x hx => (hone x).1 (thickening_subset_cthickening _ _ hx)⟩
    · exact (hK.cthickening (r := δ)).of_isClosed_subset (isClosed_tsupport χ) hts
    · exact hrange (mem_range_self x)
  have aux_pullback_extension : ∀ (P m l : ℕ) (pL : Euclid P →L[ℝ] Euclid m) (S O : Set (Euclid P)) (γ : DifferentialForm (Euclid m) l), ContDiff ℝ (⊤ : ℕ∞) γ → IsOpen O → IsCompact (S ∩ pL ⁻¹' tsupport γ) → S ∩ pL ⁻¹' tsupport γ ⊆ O → ∃ γ' : TestFormOn (univ : Set (Euclid P)) l, tsupport (γ' : DifferentialForm (Euclid P) l) ⊆ O ∧ (∀ x, covectorEuclideanNorm ((γ' : DifferentialForm (Euclid P) l) x) ≤ covectorEuclideanNorm ((γ (pL x)).compContinuousLinearMap pL)) ∧ (∀ x ∈ S, (γ' : DifferentialForm (Euclid P) l) x = (γ (pL x)).compContinuousLinearMap pL) ∧ ∀ x ∈ S, exteriorDerivative (γ' : DifferentialForm (Euclid P) l) x = (exteriorDerivative γ (pL x)).compContinuousLinearMap pL := by
    intro P m l pL S O γ hγ hO hK hKO
    -- Step 1: a smooth cut-off `χ`, `spt χ ⊆ O`, `0 ≤ χ ≤ 1`, `χ = 1` on an open `O' ⊇ K`
    obtain ⟨χ, O', hχ, hχc, hχO, hχ01, hO', hKO', hχ1⟩ :=
      aux_smooth_cutoff P _ O hK hO hKO
    -- Step 2: `β = p^#γ = Λ ∘ γ ∘ pL` is smooth, `Λ α = α ∘ pL` being continuous linear
    set β : DifferentialForm (Euclid P) l := fun x => (γ (pL x)).compContinuousLinearMap pL
      with hβdef
    have hβ : ContDiff ℝ (⊤ : ℕ∞) β := by
      have := (ContinuousAlternatingMap.compContinuousLinearMapCLM (ι := Fin l) (F := ℝ) pL).contDiff
        (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) |>.comp (hγ.comp pL.contDiff)
      simpa [Function.comp_def] using this
    -- Step 3: `β x = 0` whenever `pL x ∉ spt γ`
    have hβ0 : ∀ x, pL x ∉ tsupport γ → β x = 0 := by
      intro x hx
      ext v
      simp [hβdef, image_eq_zero_of_notMem_tsupport hx]
    -- Step 4: `γ' = χ • β` is a test form on `ℝᴾ` with `spt γ' ⊆ spt χ ⊆ O`
    set g : DifferentialForm (Euclid P) l := fun x => χ x • β x with hgdef
    have hg : ContDiff ℝ (⊤ : ℕ∞) g := hχ.smul hβ
    have hgc : HasCompactSupport g := hχc.smul_right
    have hgs : tsupport g ⊆ tsupport χ := tsupport_smul_subset_left _ _
    let γ' : TestFormOn (univ : Set (Euclid P)) l := ⟨g, ⟨⟨hg, hgc⟩, subset_univ _⟩⟩
    -- Step 5: the coefficient norm is absolutely homogeneous, `|c • α| = |c| |α|`
    have hscale : ∀ (c : ℝ) (α : Covector (Euclid P) l),
        covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
      intro c α
      unfold covectorEuclideanNorm
      have : (∑ I : Fin l → Fin P, if StrictMono I then
            ((c • α) (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0) =
          c ^ 2 * ∑ I : Fin l → Fin P, if StrictMono I then
            (α (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun I _ => ?_
        split_ifs <;> simp [mul_pow]
      rw [this, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
    refine ⟨γ', hgs.trans hχO, fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
    -- Step 6 (b): `|χ x • β x| = χ x |β x| ≤ |β x|`
    · change covectorEuclideanNorm (χ x • β x) ≤ covectorEuclideanNorm (β x)
      rw [hscale, abs_of_nonneg (hχ01 x).1]
      exact mul_le_of_le_one_left (covectorEuclideanNorm_nonneg _) (hχ01 x).2
    -- Step 7 (c): `χ = 1` on `O'`, and `β x = 0` at `x ∈ S \ O'`, since `K ⊆ O'`
    · change χ x • β x = β x
      by_cases hxO' : x ∈ O'
      · rw [hχ1 x hxO', one_smul]
      · have : pL x ∉ tsupport γ := fun h => hxO' (hKO' ⟨hx, h⟩)
        rw [hβ0 x this, smul_zero]
    -- Step 8 (d) on `O'`: `g = β` near `x`, so `dg(x) = dβ(x) = p^#(dγ)(x)` by naturality of `d`
    · change extDeriv g x = (extDeriv γ (pL x)).compContinuousLinearMap pL
      by_cases hxO' : x ∈ O'
      · have hev : g =ᶠ[𝓝 x] β := by
          filter_upwards [hO'.mem_nhds hxO'] with y hy
          simp [hgdef, hχ1 y hy]
        rw [hev.extDeriv_eq]
        have hpb := extDeriv_pullback (x := x) (ω := γ) (f := ⇑pL) (r := ((⊤ : ℕ∞) : WithTop ℕ∞))
          ((hγ.differentiable (by simp)).differentiableAt) pL.contDiff.contDiffAt (by simp)
        simpa [ContinuousLinearMap.fderiv] using hpb
      -- Step 9 (d) off `O'`: `g` vanishes near `x` and `γ` near `pL x`, so both sides are `0`
      · have hxK : pL x ∉ tsupport γ := fun h => hxO' (hKO' ⟨hx, h⟩)
        have hopen : IsOpen ((tsupport γ)ᶜ) := (isClosed_tsupport γ).isOpen_compl
        have hev : g =ᶠ[𝓝 x] 0 := by
          filter_upwards [(hopen.preimage pL.continuous).mem_nhds hxK] with y hy
          simp [hgdef, hβ0 y hy]
        have hev' : γ =ᶠ[𝓝 (pL x)] 0 := by
          filter_upwards [hopen.mem_nhds hxK] with y hy
          exact image_eq_zero_of_notMem_tsupport hy
        rw [hev.extDeriv_eq, hev'.extDeriv_eq]
        ext v
        simp [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  have aux_integral_estimate : ∀ (P m l : ℕ) (pL : Euclid P →L[ℝ] Euclid m) (S F : Set (Euclid P)) (K : Set (Euclid m)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P l), MeasurableSet F → F ⊆ S → IsCompact (S ∩ pL ⁻¹' K) → (∀ K' : Set (Euclid P), IsCompact K' → μ K' < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ β : Covector (Euclid P) l, |ξ x β| ≤ covectorEuclideanNorm β) → (∀ γ : Covector (Euclid m) l, covectorEuclideanNorm (γ.compContinuousLinearMap pL) ≤ covectorEuclideanNorm γ) → ∃ c : ℝ, 0 ≤ c ∧ ∀ (ω : DifferentialForm (Euclid m) l) (M : ℝ), Continuous ω → (∀ y, y ∉ K → ω y = 0) → (∀ y, ‖ω y‖ ≤ M) → Integrable (fun x => ξ x ((ω (pL x)).compContinuousLinearMap pL)) (μ.restrict F) ∧ |∫ x in F, ξ x ((ω (pL x)).compContinuousLinearMap pL) ∂μ| ≤ c * M := by
    intro P m l pL S F K μ ξ hF hFS hSK hμ hξm hξb hN3
    -- Step 1 (N2): `|α|_E ≤ C ‖α‖` with `C = √#(Fin l → Fin m)`, since `|α(e_I)| ≤ ‖α‖`
    set C : ℝ := Real.sqrt (Fintype.card (Fin l → Fin m)) with hCdef
    have hC0 : 0 ≤ C := Real.sqrt_nonneg _
    have hN2 : ∀ α : Covector (Euclid m) l, covectorEuclideanNorm α ≤ C * ‖α‖ := by
      intro α
      unfold covectorEuclideanNorm
      rw [hCdef, ← Real.sqrt_sq (norm_nonneg α), ← Real.sqrt_mul (Nat.cast_nonneg _)]
      apply Real.sqrt_le_sqrt
      calc (∑ I : Fin l → Fin m, if StrictMono I then
              (α (fun i ↦ EuclideanSpace.basisFun (Fin m) ℝ (I i))) ^ 2 else 0)
          ≤ ∑ _I : Fin l → Fin m, ‖α‖ ^ 2 := by
            apply Finset.sum_le_sum
            intro I _
            split_ifs
            · have h1 := α.le_opNorm (fun i ↦ EuclideanSpace.basisFun (Fin m) ℝ (I i))
              have hprod : ∏ i, ‖EuclideanSpace.basisFun (Fin m) ℝ (I i)‖ = 1 := by
                simp
              rw [hprod, mul_one] at h1
              have h2 : |α (fun i ↦ EuclideanSpace.basisFun (Fin m) ℝ (I i))| ≤ ‖α‖ := by
                simpa [Real.norm_eq_abs] using h1
              rw [← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) h2 2
            · positivity
        _ = (Fintype.card (Fin l → Fin m) : ℝ) * ‖α‖ ^ 2 := by simp
    -- Step 2: `A = S ∩ pL⁻¹(K)` is compact, so measurable with `μ(A) < ∞`; `c = C μ(A)`
    set μK : ℝ := (μ (S ∩ pL ⁻¹' K)).toReal with hμKdef
    have hSKm : MeasurableSet (S ∩ pL ⁻¹' K) := hSK.isClosed.measurableSet
    have hμKfin : μ (S ∩ pL ⁻¹' K) < ∞ := hμ _ hSK
    refine ⟨C * μK, mul_nonneg hC0 ENNReal.toReal_nonneg, fun ω M hω hωK hωM => ?_⟩
    -- Step 3: `M ≥ ‖ω(0)‖ ≥ 0`, and `β(x) = ω(pL x) ∘ pL` is continuous
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hωM 0)
    set β : Euclid P → Covector (Euclid P) l := fun x => (ω (pL x)).compContinuousLinearMap pL
      with hβdef
    have hβc : Continuous β := by
      have := (ContinuousAlternatingMap.compContinuousLinearMapCLM (ι := Fin l) (F := ℝ)
        pL).continuous.comp (hω.comp pL.continuous)
      simpa [Function.comp_def] using this
    -- Step 4: `x ↦ ξ(x)(β(x))` is the continuous evaluation of `(ξ, β)`, so a.e. strongly measurable
    have hΦm : AEStronglyMeasurable (fun x => ξ x (β x)) μ :=
      (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Covector (Euclid P) l)
        (F := ℝ)).continuous.comp_aestronglyMeasurable (hξm.prodMk hβc.aestronglyMeasurable)
    -- Step 5: `|ξ(x)(β(x))| ≤ g(x) = C M 1_A(x)` for `μ⌞F`-a.e. `x`
    set g : Euclid P → ℝ := (S ∩ pL ⁻¹' K).indicator (fun _ => C * M) with hgdef
    have hb : ∀ᵐ x ∂(μ.restrict F), ‖ξ x (β x)‖ ≤ g x := by
      filter_upwards [ae_restrict_mem hF, ae_restrict_of_ae hξb] with x hxF hx
      by_cases hxK : pL x ∈ K
      · rw [hgdef, indicator_of_mem (show x ∈ S ∩ pL ⁻¹' K from ⟨hFS hxF, hxK⟩), Real.norm_eq_abs]
        calc |ξ x (β x)| ≤ covectorEuclideanNorm (β x) := hx _
          _ ≤ covectorEuclideanNorm (ω (pL x)) := hN3 _
          _ ≤ C * ‖ω (pL x)‖ := hN2 _
          _ ≤ C * M := mul_le_mul_of_nonneg_left (hωM _) hC0
      · have h0 : ω (pL x) = 0 := hωK _ hxK
        have hβ0 : β x = 0 := by
          ext v
          simp [hβdef, h0]
        rw [hgdef, indicator_of_notMem (fun h => hxK h.2), hβ0, map_zero, norm_zero]
    -- Step 6: `g` is `μ⌞F`-integrable since `μ(A ∩ F) ≤ μ(A) < ∞`; domination gives integrability
    have hgint : Integrable g (μ.restrict F) := by
      rw [hgdef, integrable_indicator_iff hSKm]
      refine integrableOn_const ?_
      rw [Measure.restrict_apply hSKm]
      exact (lt_of_le_of_lt (measure_mono inter_subset_left) hμKfin).ne
    refine ⟨Integrable.mono' hgint hΦm.restrict hb, ?_⟩
    -- Step 7: `|∫_F ξ(β)| ≤ ∫ g d(μ⌞F) = C M μ(A ∩ F) ≤ C M μ(A) = c M`
    have hle := norm_integral_le_of_norm_le hgint hb
    rw [Real.norm_eq_abs] at hle
    refine hle.trans ?_
    rw [hgdef, integral_indicator hSKm, setIntegral_const, smul_eq_mul]
    have hle2 : (μ.restrict F).real (S ∩ pL ⁻¹' K) ≤ μK := by
      rw [Measure.real, Measure.restrict_apply hSKm, hμKdef]
      exact ENNReal.toReal_mono hμKfin.ne (measure_mono inter_subset_left)
    have hCM : 0 ≤ C * M := mul_nonneg hC0 hM0
    calc (μ.restrict F).real (S ∩ pL ⁻¹' K) * (C * M) ≤ μK * (C * M) :=
          mul_le_mul_of_nonneg_right hle2 hCM
      _ = C * μK * M := by ring
  have aux_integral_current : ∀ (P m l : ℕ) (pL : Euclid P →L[ℝ] Euclid m) (U : Set (Euclid m)) (S F : Set (Euclid P)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P l), MeasurableSet F → F ⊆ S → (∀ K : Set (Euclid m), IsCompact K → K ⊆ U → IsCompact (S ∩ pL ⁻¹' K)) → (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ β : Covector (Euclid P) l, |ξ x β| ≤ covectorEuclideanNorm β) → (∀ γ : Covector (Euclid m) l, covectorEuclideanNorm (γ.compContinuousLinearMap pL) ≤ covectorEuclideanNorm γ) → ∃ Y : GeometricCurrentOn U l, ∀ ω : TestFormOn U l, Y ω = ∫ x in F, ξ x (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL) ∂μ := by
    intro P m l pL U S F μ ξ hF hFS hcpt hμ hξm hξb hN3
    -- every integrand is `μ⌞F`-integrable: `integral_estimate` with `K = spt ω`, `M = sup ‖ω‖`
    have hint : ∀ ω : TestFormOn U l, Integrable (fun x => ξ x
        (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL)) (μ.restrict F) := by
      intro ω
      have hωc : Continuous (ω : DifferentialForm (Euclid m) l) := ω.property.1.1.continuous
      have hK : IsCompact (tsupport (ω : DifferentialForm (Euclid m) l)) := ω.property.1.2
      obtain ⟨c, -, hc⟩ := aux_integral_estimate P m l pL S F
        (tsupport (ω : DifferentialForm (Euclid m) l)) μ ξ hF hFS (hcpt _ hK ω.property.2) hμ hξm
        hξb hN3
      obtain ⟨M, hM⟩ := hωc.bounded_above_of_compact_support ω.property.1.2
      exact (hc _ M hωc (fun y hy => image_eq_zero_of_notMem_tsupport hy) hM).1
    -- `Y` is linear: `ω ↦ ⟨ω(pL x) ∘ pL, ξ(x)⟩` is linear for each `x`
    let T : CurrentOn U l :=
      { toFun := fun ω => ∫ x in F, ξ x
          (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL) ∂μ
        map_add' := fun ω η => by
          rw [← integral_add (hint ω) (hint η)]
          congr 1
          funext x
          rw [← map_add]
          congr 1
        map_smul' := fun c ω => by
          rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
          congr 1
          funext x
          rw [← smul_eq_mul, ← map_smul]
          congr 1 }
    refine ⟨⟨T, fun ωs hωs => ?_⟩, fun ω => rfl⟩
    -- continuity: the supports lie in one compact `K ⊆ U` and `ωⱼ → 0` uniformly on `K`
    obtain ⟨K, hK, hKU, hsupp, -, hconv⟩ := hωs
    obtain ⟨c, hc0, hc⟩ := aux_integral_estimate P m l pL S F K μ ξ hF hFS
      (hcpt K hK hKU) hμ hξm hξb hN3
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hδ : 0 < ε / (c + 1) := div_pos hε (by linarith)
    obtain ⟨N, hN⟩ := (Metric.tendstoUniformlyOn_iff.1 (hconv 0) _ hδ).exists_forall_of_atTop
    refine ⟨N, fun n hn => ?_⟩
    -- `‖ωₙ(y)‖ ≤ ε / (c + 1)` everywhere: on `K` by uniform convergence, off `K` `ωₙ(y) = 0`
    have hbd : ∀ y, ‖(ωs n : DifferentialForm (Euclid m) l) y‖ ≤ ε / (c + 1) := by
      intro y
      by_cases hy : y ∈ K
      · have := hN n hn y hy
        simp only [ZeroMemClass.coe_zero, iteratedFDeriv_zero, Pi.zero_apply, dist_zero_left,
          norm_iteratedFDeriv_zero] at this
        exact this.le
      · rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hsupp n h)), norm_zero]
        exact hδ.le
    have hωc : Continuous (ωs n : DifferentialForm (Euclid m) l) := (ωs n).property.1.1.continuous
    have := (hc _ _ hωc (fun y hy => image_eq_zero_of_notMem_tsupport (fun h => hy (hsupp n h)))
      hbd).2
    rw [Real.dist_eq, sub_zero]
    calc |T (ωs n)| ≤ c * (ε / (c + 1)) := this
      _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith
  have aux_mass_le : ∀ (P m l : ℕ) (pL : Euclid P →L[ℝ] Euclid m) (U : Set (Euclid m)) (F : Set (Euclid P)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P l) (Y : GeometricCurrentOn U l), IsOpen U → (∀ᵐ x ∂μ, ∀ β : Covector (Euclid P) l, |ξ x β| ≤ covectorEuclideanNorm β) → (∀ γ : Covector (Euclid m) l, covectorEuclideanNorm (γ.compContinuousLinearMap pL) ≤ covectorEuclideanNorm γ) → (∀ ω : TestFormOn U l, Y ω = ∫ x in F, ξ x (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL) ∂μ) → Y.massOn U ≤ μ (F ∩ pL ⁻¹' U) := by
    intro P m l pL U F μ ξ Y hU hξb hN3 hY
    -- `pL⁻¹(U)` is open, hence measurable
    have hUm : MeasurableSet (pL ⁻¹' U) := (hU.preimage pL.continuous).measurableSet
    -- Step 1: it suffices to bound `ofReal (Y ω)` for each admissible `ω`
    apply sSup_le
    rintro r ⟨ω, ⟨-, hω1⟩, rfl⟩
    show ENNReal.ofReal (Y ω) ≤ _
    rw [hY ω]
    -- Step 2: `‖Φ_ω‖ₑ ≤ 1_{pL⁻¹(U)}` a.e. on `F`; off `pL⁻¹(U)`, `ω (pL x) = 0` as `tsupport ω ⊆ U`
    have hpt : ∀ᵐ x ∂(μ.restrict F), ‖ξ x (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL)‖ₑ ≤ (pL ⁻¹' U).indicator 1 x := by
      filter_upwards [ae_restrict_of_ae hξb] with x hx
      by_cases hxU : pL x ∈ U
      · rw [indicator_of_mem (show x ∈ pL ⁻¹' U from hxU), Pi.one_apply, Real.enorm_eq_ofReal_abs,
          ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal ((hx _).trans ((hN3 _).trans (hω1 _)))
      · have h0 : (ω : DifferentialForm (Euclid m) l) (pL x) = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h => hxU (ω.property.2 h))
        have hβ0 : ((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL = 0 := by
          ext v
          simp [h0]
        rw [hβ0, map_zero, enorm_zero]
        exact zero_le
    -- Step 3: `ofReal (Y ω) ≤ ‖∫_F Φ_ω‖ₑ ≤ ∫⁻_F ‖Φ_ω‖ₑ ≤ ∫⁻_F 1_{pL⁻¹(U)} = μ(F ∩ pL⁻¹(U))`
    calc ENNReal.ofReal (∫ x in F, ξ x (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL) ∂μ)
        ≤ ‖∫ x in F, ξ x (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL) ∂μ‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ x in F, ‖ξ x (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL)‖ₑ ∂μ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x in F, (pL ⁻¹' U).indicator 1 x ∂μ := lintegral_mono_ae hpt
      _ = μ (F ∩ pL ⁻¹' U) := by
          rw [lintegral_indicator_one hUm, Measure.restrict_apply hUm, inter_comm]
  have aux_boundary_mass_le : ∀ (P m l : ℕ) (pL : Euclid P →L[ℝ] Euclid m) (U : Set (Euclid m)) (S F : Set (Euclid P)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (l + 1)) (Y : GeometricCurrentOn U (l + 1)) (Z : GeometricCurrentOn (univ : Set (Euclid P)) (l + 1)), MeasurableSet F → F ⊆ S → (∀ K : Set (Euclid m), IsCompact K → K ⊆ U → IsCompact (S ∩ pL ⁻¹' K)) → (∀ γ : Covector (Euclid m) l, covectorEuclideanNorm (γ.compContinuousLinearMap pL) ≤ covectorEuclideanNorm γ) → (∀ ω : TestFormOn U (l + 1), Y ω = ∫ x in F, ξ x (((ω : DifferentialForm (Euclid m) (l + 1)) (pL x)).compContinuousLinearMap pL) ∂μ) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (l + 1), Z ω = ∫ x in F, ξ x ((ω : DifferentialForm (Euclid P) (l + 1)) x) ∂μ) → ∀ W : Set (Euclid m), IsOpen W → Y.boundary.massOn W ≤ Z.boundary.massOn (pL ⁻¹' W) := by
    intro P m l pL U S F μ ξ Y Z hF hFS hcpt hN3 hY hZ W hW
    -- Step 1: it suffices to bound `∂Y(γ)` for every `γ` admissible for `M_W(∂Y)`
    apply sSup_le
    rintro r ⟨γ, ⟨hγW, hγ1⟩, rfl⟩
    show ENNReal.ofReal (Y.boundary γ) ≤ _
    -- Steps 2–3: `S ∩ p⁻¹(spt γ)` is a compact subset of the open set `p⁻¹(W)`, so `p^#γ` has a
    -- cut-off `γ' ∈ 𝒟ˡ(ℝᴾ)` supported in `p⁻¹(W)`
    have hK : IsCompact (S ∩ pL ⁻¹' tsupport (γ : DifferentialForm (Euclid m) l)) :=
      hcpt _ γ.property.1.2 γ.property.2
    obtain ⟨γ', hγ'O, hγ'n, -, hγ'd⟩ := aux_pullback_extension P m l pL S
      (pL ⁻¹' W) (γ : DifferentialForm (Euclid m) l) γ.property.1.1 (hW.preimage pL.continuous) hK
      (fun x hx => hγW hx.2)
    -- Step 4: `|γ'(x)| ≤ |γ(p x) ∘ p| ≤ |γ(p x)| ≤ 1`, so `γ'` is admissible for `M_{p⁻¹(W)}(∂Z)`
    have hadm : γ' ∈ massAdmissibleOn (univ : Set (Euclid P)) l (pL ⁻¹' W) :=
      ⟨hγ'O, fun x => (hγ'n x).trans ((hN3 _).trans (hγ1 _))⟩
    -- Step 5: `∂Y(γ) = ∫_F ξ(p^#(dγ)) dμ = ∫_F ξ(dγ') dμ = ∂Z(γ')`, since `F ⊆ S`
    have heq : Y.boundary γ = Z.boundary γ' := by
      rw [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.boundary_apply, hY, hZ]
      apply setIntegral_congr_fun hF
      intro x hx
      change ξ x ((exteriorDerivative (γ : DifferentialForm (Euclid m) l)
          (pL x)).compContinuousLinearMap pL) =
        ξ x (exteriorDerivative (γ' : DifferentialForm (Euclid P) l) x)
      rw [hγ'd x (hFS hx)]
    -- Step 6: `ofReal (∂Y(γ)) = ofReal (∂Z(γ')) ≤ M_{p⁻¹(W)}(∂Z)`
    rw [heq]
    exact Z.boundary.le_massOn hadm
  intro P d v pL U S F μ ξ Z hv hpL hU hF hFS hcpt hμ hξm hξb hZ
  -- (N3): `|γ ∘ pL| ≤ |γ|` for covectors of every degree on `ℝⁿ`, `n = d + 1`.
  have hN3 := (Submission.cbr_ci_pw_orthonormal_covector_bounds P (d + 1) v pL hv hpL).2
  -- Steps 1–3: `Y` is a current in `U`, given by the integral formula (i).
  obtain ⟨Y, hY⟩ := aux_integral_current P (d + 1) (d + 1) pL U S F μ ξ
    hF hFS hcpt hμ hξm hξb (hN3 (d + 1))
  -- Step 4 gives (ii) and step 6 gives (iii).
  refine ⟨Y, hY,
    aux_mass_le P (d + 1) (d + 1) pL U F μ ξ Y hU hξb (hN3 (d + 1)) hY,
    fun W hW _ => aux_boundary_mass_le P (d + 1) d pL U S F μ ξ Y Z hF hFS
      hcpt (hN3 d) hY hZ W hW, fun ω => ?_⟩
  -- Step 5, (iv): cut off `p^#ω` near the compact set `S ∩ pL⁻¹(spt ω)`.
  obtain ⟨ω', -, -, hω', -⟩ := aux_pullback_extension P (d + 1) (d + 1) pL
    S univ (ω : DifferentialForm (Euclid (d + 1)) (d + 1)) ω.property.1.1 isOpen_univ
    (hcpt _ ω.property.1.2 ω.property.2) (subset_univ _)
  exact ⟨ω', hω'⟩
```

## Key steps

1. The integrand ξ(x)((p^#ω)(x)) is a.e. bounded by sup|ω| and vanishes off the compact set S ∩ pL⁻¹(spt ω), so Y(ω) := ∫_F ξ(p^#ω)dμ is a continuous linear current on U.
2. |p^#ω| ≤ |ω∘pL| (covector_bounds) gives M_U(Y) ≤ μ(F ∩ pL⁻¹U).
3. A smooth cutoff χ ≡ 1 near S ∩ pL⁻¹(spt ω) turns p^#ω into a test form ω' on ℝ^P agreeing with p^#ω on S.
4. For admissible γ, γ' := χ·p^#γ is admissible for M_{pL⁻¹W}(∂Z) and d γ' = p^#(dγ) on S by locality and naturality of d, so ∂Y(γ) = ∂Z(γ').

## Reference use

### local-project

Queries:
- `cat SNAPSHOT/manifest.json -> mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d; git rev-parse HEAD in the workspace, .lake/packages/mathlib and .lake/packages/simongmt -> b4d606db1, 25730c7c, 2b366308; cmp SNAPSHOT/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean -> identical`
- `python3 -I scans of RUN/dag.json (2229 nodes): selected node (depth 5, decomposing, attempt 2 started 2026-10-14T02:29:54Z); subtree of root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1 (cbr_ci_plane_weight_ge_one: identical frozen type, speculative-ready) with statuses, candidate commits and updated_at; lean_name lookup of all 11 proposed names: the 8 reused names each occur once, accepted with candidate commits (latest 02:28:02Z) and identical lean_statement; the 3 dmcbr_ci_pw_* names have no node; byte comparisons dimred_mbl_slice_mass_bounds = cmc_slice_mass_bounds, dmcbr_measure_convergence_tools = cbr_measure_convergence_tools, first conjunct of dimred_mbl_current_foundations = cmc_exists_massRepresentation, and (REP), (SL), (CT) occur verbatim in the selected type`
- `grep -n / sed -n over /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_decompose, _existing_lean_name_problem, _accepted_checkpoint, _solve_children existing_by_name), store.py (refresh, update: accepted status is permanent), leaf_verification.py (check_source_delta), lean_contract.py (validate_lean_statement); swarm-project.json -> max_depth 6, max_children 12`
- `read RUN/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-fc3eb928c0/{parent-child-handoff.json, parent-supplied-plan.md, decomposition-v1.json}: attempt 1 (12 children) was rejected only by the name check on cbr_ci_pw_bv_smooth_test_bound; its child statements, types and proofs were reused here, except smooth_test_bound (dropped) and bv_estimate (now the accepted cbr_ci_pw_bv_mollifier_estimate, with Claim A proved inline)`
- `git show <candidate>:GMT/Ch07/Submission.lean for e55e2ff3e6, f6358e3d52, e42d9153e5, b0c7e18f51, 7bb3791613, 4020906019, 04807323c8, 144655f39d -> each contains 'theorem Submission.<name> : <frozen type> :=' with the reused name occurring exactly once`
- `grep -rn over SNAPSHOT/mathlib/Mathlib for the library names cited in the bv_estimate proof: ae_tendsto_average_norm_sub (Covering/DensityTheorem.lean:150, Covering/Differentiation.lean:837), tendsto_integral_smul_of_tendsto_average_norm_sub, integral_comp_inv_smul_of_nonneg, addHaar_real_closedBall', contDiff_convolution_right, integrableOn_iff_integrable_of_support_subset, integrableOn_of_bounded, continuous_of_dominated, intervalIntegral_integral_swap, norm_integral_le_of_norm_le_const, fderiv_comp_add_right, tsupport_comp_eq_preimage, integral_sub_right_eq_self, Integrable.mul_prod, integral_integral_swap, Integrable.mul_bdd, setIntegral_indicator, integral_pos_iff_support_of_nonneg, measure_ball_pos, Integrable.integral_prod_left, Integrable.integral_prod_right, Continuous.integrable_of_hasCompactSupport, Continuous.bounded_above_of_compact_support, HasCompactSupport.fderiv, integral_eq_sub_of_hasDerivAt -> all present`
- `rg -l dmcbr_ci_pw_projected_current|dmcbr_ci_pw_density_null_off_image|dmcbr_ci_pw_density_l1_tendsto_const over SNAPSHOT/project, GMT and .lake/packages/simongmt -> no match (exit 1)`
- `lake env lean /tmp/dmcbr_ci_a2/lean/Types.lean (the 11 child types as Submission.* theorems) -> only sorry warnings, exit 0`
- `lake env lean /tmp/dmcbr_ci_a2/lean/Assembly.lean (exact frozen parent type from the 11 child types as axioms, no sorry) -> #print axioms: propext, Classical.choice, Quot.sound, cbr_ci_pw_good_level_slices, cbr_ci_pw_isolate_plane, cbr_ci_pw_orthonormal_covector_bounds, cbr_ci_pw_plane_map_volume, cbr_ci_pw_top_current_density, dmcbr_ci_pw_density_l1_tendsto_const, dmcbr_ci_pw_density_null_off_image, dmcbr_ci_pw_projected_current`
- `lake env lean /tmp/dmcbr_ci_a2/lean/check_{projection,null_off_image,l1_constant}.lean (#count_heartbeats in + realization + #print axioms, siblings declared by exact frozen types) -> 102743 / 19932 / 59551 heartbeats, axioms = standard three + declared siblings only`
- `lake env lean /tmp/dmcbr_ci_a2/lean/EndToEnd.lean (3 fresh realizations as theorems + assembly) -> #print axioms: propext, Classical.choice, Quot.sound + the 8 reused accepted declarations, exit 0`
- `python3 -I: AST-extracted leaf_verification.check_source_delta on GMT/Ch07/Submission.lean with each fresh realization inserted before main_theorem's docstring -> OK (3/3); lean_contract.validate_lean_statement on all 11 child types -> valid and unchanged`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-fc3eb928c0/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-fc3eb928c0/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-fc3eb928c0/decomposition-v1.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `/tmp/dmcbr_ci_a2/lean/Types.lean`
- `/tmp/dmcbr_ci_a2/lean/Assembly.lean`
- `/tmp/dmcbr_ci_a2/lean/check_projection.lean`
- `/tmp/dmcbr_ci_a2/lean/check_null_off_image.lean`
- `/tmp/dmcbr_ci_a2/lean/check_l1_constant.lean`
- `/tmp/dmcbr_ci_a2/lean/EndToEnd.lean`

The snapshot is compatible: pins match, and the snapshot contract is byte-identical to Submission.lean. No dmcbr_ci_pw_* declaration exists in the snapshot, the workspace or SimonGMT. The 8 reused children (covector_bounds, plane_map, isolate_plane, good_level, top_density, interior_form, mollified_uniform, bv_estimate = cbr_ci_pw_bv_mollifier_estimate) are accepted checkpoints. They were accepted before this attempt's DAG refresh, and each candidate commit declares exactly the frozen type. The 3 fresh children take globally unused dmcbr_ci_pw_* names because their other-branch counterparts are unaccepted. All 11 child types elaborate. The sorry-free conditional assembly and the end-to-end file prove the exact parent type using only propext, Classical.choice, Quot.sound and child or reused accepted declarations. The fresh single-theorem realizations compile within the default heartbeats and pass the leaf delta check.
