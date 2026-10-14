# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.im_series-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.im_series-a1.ae_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 5–7 of the supplied proof of dor_lmb_fc_im_series (Simon Ch. 6, Lemma 3.13, chapter-06.txt lines 901–935: the limit multiplicity is integer-valued, T_x M_q = T_x M₊ off small sets so the limit orientation orients M₊, and T = τ(M₊, θ, ξ)), stated for an arbitrary Hⁿ-a.e. convergent sequence of IM densities. Departures (details only): (i) the dual norm |·|* of the supplied step 5 is replaced by N(ζ) := √|ζ(L ζ)|, where L is the continuous linear map of the reused accepted sibling unit_orientation_dual (UOD); N is continuous and N(cζ) = c for every unit orientation ζ and c ≥ 0, which are the only properties of |·|* that step 5 uses; (ii) the local integrability of the limit multiplicity (supplied step 7, ∫_{M₊∩K} θ ≤ ∫|η|* ≤ Λ) is obtained by Fatou's lemma from the hypothesis μ_{R_q}(K) ≤ C_K; (iii) the fact that two unit orientations of the same plane differ by a sign (supplied step 6) is the reused accepted sibling orientation_sign; the tangent-plane locality is (IMC)(a) of the reused accepted sibling im_calculus, as in the supplied proof. Conventions: ℝ^P = Euclid P and Hⁿ = μHE[n]. Λ_n(ℝ^P) = MultiVector P n is the space of continuous linear functionals on n-covectors (Covector (Euclid P) n), with its operator norm ‖·‖ and the induced topology. An IMRep R = (M, θ, ξ) in U is the contract structure IMRep U n (M = R.carrier Borel, M ⊆ U, countably n-rectifiable; θ = R.mult : ℝ^P → ℕ measurable, θ ≥ 1 on M, locally Hⁿ-integrable on M in U; ξ = R.orient : ℝ^P → Λ_n(ℝ^P), Hⁿ⌞M-a.e. strongly measurable and Hⁿ⌞M-a.e. a unit orientation (IsUnitOrientationOf) of an approximate tangent space of M). Its density is D_R(x) := 1_M(x)θ(x)ξ(x) ∈ Λ_n(ℝ^P) (Lean: R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x), its weight is μ_R := θ·Hⁿ⌞M (R.measure), and its action on an n-form ω is R.action(ω) = ∫_M θ(x)·ξ(x)(ω(x)) dHⁿ(x). 𝒟ⁿ(U) = TestFormOn U n (smooth n-forms on ℝ^P with compact support contained in U).
Notation: μ := Hⁿ; R_q = (N_q, ϑ_q, ζ_q); D_q := D_{R_q}; b_q(x) := 1_{N_q}(x)ϑ_q(x) ∈ ℕ (a Borel function); T(A, x, Q) abbreviates HasApproximateTangentSpaceAt n A x Q.
0. The multiplicity functional. Let L : Λ_n(ℝ^P) → Λⁿ(ℝ^P) be the continuous linear map of (UOD): ξ(Lξ) = 1 whenever ξ is a unit orientation of some subspace. Put N(ζ) := √|ζ(Lζ)|. N is continuous (ζ ↦ (ζ, Lζ) is continuous, the evaluation (ζ, α) ↦ ζ(α) is a bounded bilinear map, and |·| and √ are continuous). If ζ is a unit orientation and c ≥ 0 then (cζ)(L(cζ)) = c²·ζ(Lζ) = c², so N(cζ) = √(c²) = c. Also N(0) = 0.
1. Multiplicities from densities. Fix q. By the field orients of R_q, for μ-a.e. x: if x ∈ N_q then there is a subspace Q with T(N_q, x, Q) and ζ_q(x) a unit orientation of Q. For such x, N(D_q(x)) = b_q(x): if x ∈ N_q, N(ϑ_q(x)ζ_q(x)) = ϑ_q(x) by step 0; if x ∉ N_q, N(0) = 0 = b_q(x).
2. A Borel version of η. Each D_q is a.e. strongly measurable for μ (x ↦ ϑ_q(x)ζ_q(x) is a.e. strongly measurable for μ⌞N_q, and D_q is its indicator on the Borel set N_q). Λ_n(ℝ^P) is a normed, hence metrizable, space, so the μ-a.e. limit η is a.e. strongly measurable for μ (aestronglyMeasurable_of_tendsto_ae). Fix a strongly measurable (Borel) η̃ with η̃ = η μ-a.e.
3. Good points. Let G be the set of x such that η(x) = η̃(x), D_q(x) → η(x), and for every q both the implication of step 1 and N(D_q(x)) = b_q(x) hold. By the hypothesis, step 1, step 2 and countable intersection, μ-a.e. x lies in G. Let Z₀ be a Borel μ-null set containing ℝ^P ∖ G (toMeasurable); thus every x ∉ Z₀ lies in G.
4. Integer limits. Lemma: if c_q ∈ ℕ and c_q → a in ℝ, there is q₀ with c_q = c_{q₀} for all q ≥ q₀, and a = c_{q₀}. Indeed choose q₀ with |c_q − a| < 1/2 for q ≥ q₀; then |c_q − c_{q₀}| < 1, so the integers c_q and c_{q₀} coincide; the eventually constant sequence converges to c_{q₀}, and limits in ℝ are unique. For x ∈ G, N(D_q(x)) → N(η(x)) by continuity of N, and N(D_q(x)) = b_q(x) ∈ ℕ; so there is q₀(x) with b_q(x) = b_{q₀(x)}(x) for all q ≥ q₀(x), and N(η(x)) = b_{q₀(x)}(x). Define θ(x) := ⌊N(η̃(x))⌋ (floor in ℕ) for x ∉ Z₀ and θ(x) := 0 for x ∈ Z₀. θ is Borel (the floor function is monotone, hence Borel; N is continuous; η̃ is Borel; Z₀ is Borel). For x ∉ Z₀: θ(x) = ⌊N(η(x))⌋ = b_{q₀(x)}(x), hence
 (★) b_q(x) = θ(x) for all q ≥ q₀(x).
5. Carrier and orientation. Let M₊ := (⋃_q N_q) ∩ (ℝ^P ∖ Z₀) ∩ {θ ≥ 1}; it is Borel and M₊ ⊆ ⋃_q N_q ⊆ U. Let ξ(x) := θ(x)⁻¹·η̃(x) for x ∈ M₊ and ξ(x) := 0 otherwise; ξ is strongly measurable. For x ∈ M₊ and q ≥ q₀(x), (★) gives b_q(x) = θ(x) ≥ 1, hence
 (★★) x ∈ N_q, ϑ_q(x) = θ(x) and D_q(x) = θ(x)ζ_q(x).
6. Local finiteness (Fatou). Fix a compact K ⊆ U (K is Borel). For every q, μ_{R_q}(K) = ∫_K ϑ_q d(μ⌞N_q) = ∫_{K∩N_q} ϑ_q dμ = ∫ 1_K b_q dμ. For every x, 1_{M₊∩K}(x)θ(x) ≤ liminf_q 1_K(x)b_q(x): if x ∈ M₊ ∩ K the sequence on the right is eventually equal to θ(x) by (★); otherwise the left side is 0. By Fatou's lemma (each 1_K b_q is measurable) and the hypothesis, ∫_{M₊∩K} θ dμ ≤ liminf_q ∫ 1_K b_q dμ = liminf_q μ_{R_q}(K) ≤ C_K < ∞. As θ ≥ 1 on M₊, μ(M₊ ∩ K) ≤ ∫_{M₊∩K} θ dμ < ∞. Likewise μ(N_q ∩ K) ≤ ∫_{N_q∩K} ϑ_q dμ < ∞ for every q (ϑ_q ≥ 1 on N_q, and the field locallyIntegrable_mult of R_q).
7. Orientation of M₊. For each q apply (IMC)(a) twice with the Borel set M := M₊ ∩ N_q, once with M' := N_q and once with M' := M₊ (both Borel, contained in U, with μ(M' ∩ K) < ∞ for all compact K ⊆ U by step 6): for μ-a.e. x ∈ M₊ ∩ N_q and every subspace Q, T(M₊ ∩ N_q, x, Q) ⇔ T(N_q, x, Q) and T(M₊ ∩ N_q, x, Q) ⇔ T(M₊, x, Q). Let Z₁ be the union over q of the corresponding exceptional μ-null sets. Let x ∈ M₊ ∖ Z₁. Then x ∉ Z₀, so x ∈ G, and by (★★) x ∈ N_q for all q ≥ q₀(x). For each q ≥ q₀(x), step 1 (x ∈ G) gives a subspace Q_q with T(N_q, x, Q_q) and ζ_q(x) a unit orientation of Q_q; then T(M₊ ∩ N_q, x, Q_q) and T(M₊, x, Q_q). By uniqueness of approximate tangent spaces (SimonGMT HasApproximateTangentSpaceAt.unique), Q_q = Q_{q₀(x)} =: Q for all q ≥ q₀(x). Let e := ζ_{q₀(x)}(x). By orientation_sign, ζ_q(x) ∈ {e, −e} for all q ≥ q₀(x). By (★★) and x ∈ G, for q ≥ q₀(x): ζ_q(x) = θ(x)⁻¹·D_q(x) → θ(x)⁻¹·η(x) = θ(x)⁻¹·η̃(x) = ξ(x). The finite set {e, −e} is closed, so ξ(x) ∈ {e, −e}. Both e and −e are unit orientations of Q (if e(α) = ±α(τ) for all α, then (−e)(α) = ∓α(τ) for all α, with the same orthonormal τ spanning Q). Hence T(M₊, x, Q) and ξ(x) is a unit orientation of Q. This holds for every x ∈ M₊ ∖ Z₁, i.e. μ⌞M₊-a.e.
8. The IMRep. R' := (M₊, θ, ξ) is an IMRep in U: M₊ is Borel and M₊ ⊆ U (step 5); ⋃_q N_q is countably n-rectifiable (SimonGMT countablyRectifiable_iUnion) and contains M₊ (CountablyRectifiable.mono); θ is measurable (step 4) and θ ≥ 1 > 0 on M₊; ∫_{M₊∩K} θ dμ < ∞ for compact K ⊆ U (step 6); ξ is strongly measurable, hence a.e. strongly measurable for μ⌞M₊; the orientation condition holds μ⌞M₊-a.e. (step 7).
9. Density and action. Let x ∉ Z₀ (this holds for μ-a.e. x). If x ∈ M₊: D_{R'}(x) = θ(x)·θ(x)⁻¹·η̃(x) = η̃(x) = η(x). If x ∉ M₊: D_{R'}(x) = 0, and η(x) = 0 because D_q(x) = 0 for all q ≥ q₀(x): if x ∈ N_q for some q ≥ q₀(x), then b_q(x) = ϑ_q(x) ≥ 1, so θ(x) ≥ 1 by (★) and x ∈ (⋃_q N_q) ∖ Z₀ with θ(x) ≥ 1, i.e. x ∈ M₊, a contradiction; hence η(x) = lim_q D_q(x) = 0. Thus D_{R'} = η μ-a.e. Finally, for every n-form ω on ℝ^P, R'.action(ω) = ∫_{M₊} θ(x)·ξ(x)(ω(x)) dμ = ∫ D_{R'}(x)(ω(x)) dμ = ∫ η(x)(ω(x)) dμ (integral_indicator, then integral_congr_ae). These are Bochner integrals: the integrands agree μ-a.e., so the identity holds whether or not they are integrable. ∎

Lean reference implementation (kernel-checked during this decomposition in namespace GMT.Ch07 after import GMT.Ch07.Submission, together with stand-ins carrying the exact frozen types of the reused accepted declarations; #print axioms of the conditional version gives [propext, Classical.choice, Quot.sound]; it compiles with the default maxHeartbeats):
theorem Submission.dor_lmb_fc_ims_ae_limit_imrep : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : ℕ → IMRep U n) (η : Euclid P → MultiVector P n), IsOpen U → (∀ᵐ x ∂μHE[n], Tendsto (fun q => (R q).carrier.indicator (fun y => ((R q).mult y : ℝ) • (R q).orient y) x) atTop (𝓝 (η x))) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ q, (R q).measure K ≤ C) → ∃ R' : IMRep U n, (∀ᵐ x ∂μHE[n], R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x = η x) ∧ ∀ ω : DifferentialForm (Euclid P) n, R'.action ω = ∫ x, η x (ω x) ∂μHE[n] := by
  have hIMC := Submission.cmc_imRep_locality_restrict_sub
  have hUOD := Submission.dor_ims_unitOrientation_dual
  have hsign := Submission.rsdic_unitOrientation_eq_or_eq_neg
  intro P n U R η hU hconv hbound
  obtain ⟨L, hL⟩ := hUOD P n
  -- Step 0: the multiplicity functional N(ζ) = √|ζ(Lζ)|
  set N : MultiVector P n → ℝ := fun ζ => Real.sqrt |ζ (L ζ)| with hN
  have hN_cont : Continuous N := by
    have h1 : Continuous fun ζ : MultiVector P n => ζ (L ζ) :=
      isBoundedBilinearMap_apply.continuous.comp (continuous_id.prodMk L.continuous)
    exact Real.continuous_sqrt.comp (continuous_abs.comp h1)
  have hN_smul : ∀ (ζ : MultiVector P n) (Q : Submodule ℝ (Euclid P)) (c : ℝ),
      IsUnitOrientationOf ζ Q → 0 ≤ c → N (c • ζ) = c := by
    intro ζ Q c hζ hc
    have h1 := (hL ζ Q hζ).2.2
    have h2 : (c • ζ) (L (c • ζ)) = c * c := by
      rw [map_smul, ContinuousLinearMap.smul_apply, map_smul, h1, smul_eq_mul, smul_eq_mul,
        mul_one]
    simp only [hN, h2]
    rw [abs_of_nonneg (mul_nonneg hc hc), Real.sqrt_mul_self hc]
  have hN_zero : N 0 = 0 := by simp [hN]
  -- densities and integer multiplicities
  set D : ℕ → Euclid P → MultiVector P n := fun q x =>
    (R q).carrier.indicator (fun y => ((R q).mult y : ℝ) • (R q).orient y) x with hD
  set b : ℕ → Euclid P → ℕ := fun q x => (R q).carrier.indicator (R q).mult x with hb
  have hb_meas : ∀ q, Measurable (b q) := fun q =>
    (R q).measurable_mult.indicator (R q).measurableSet_carrier
  have hor : ∀ q, ∀ᵐ x ∂μHE[n], x ∈ (R q).carrier → ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n (R q).carrier x Q ∧ IsUnitOrientationOf ((R q).orient x) Q :=
    fun q => (ae_restrict_iff' (R q).measurableSet_carrier).1 (R q).orients
  -- Step 1: N(D_q(x)) = b_q(x) a.e.
  have hND : ∀ q, ∀ᵐ x ∂μHE[n], N (D q x) = (b q x : ℝ) := by
    intro q
    filter_upwards [hor q] with x hx
    by_cases hxM : x ∈ (R q).carrier
    · obtain ⟨Q, -, hQ⟩ := hx hxM
      simp only [hD, hb, Set.indicator_of_mem hxM]
      exact hN_smul _ Q _ hQ (Nat.cast_nonneg _)
    · simp only [hD, hb, Set.indicator_of_notMem hxM, Nat.cast_zero]
      exact hN_zero
  -- Step 2: a Borel version of η
  have hmult_meas : ∀ q, Measurable (fun y => ((R q).mult y : ℝ)) := fun q =>
    measurable_from_nat.comp (R q).measurable_mult
  have hD_meas : ∀ q, AEStronglyMeasurable (D q) μHE[n] := fun q =>
    (aestronglyMeasurable_indicator_iff (R q).measurableSet_carrier).2
      ((hmult_meas q).aestronglyMeasurable.smul (R q).aestronglyMeasurable_orient)
  have hmetr : TopologicalSpace.PseudoMetrizableSpace (MultiVector P n) :=
    @PseudoEMetricSpace.pseudoMetrizableSpace _
      (inferInstance : PseudoEMetricSpace (MultiVector P n))
  have hη_meas : AEStronglyMeasurable η μHE[n] :=
    aestronglyMeasurable_of_tendsto_ae atTop hD_meas hconv
  set ηt := hη_meas.mk η with hηt
  have hηt_sm : StronglyMeasurable ηt := hη_meas.stronglyMeasurable_mk
  have hηt_ae : η =ᵐ[μHE[n]] ηt := hη_meas.ae_eq_mk
  -- Step 3: the good set and a Borel null set Z₀ containing its complement
  set G : Set (Euclid P) := {x | η x = ηt x ∧ Tendsto (fun q => D q x) atTop (𝓝 (η x)) ∧
    ∀ q, N (D q x) = (b q x : ℝ) ∧ (x ∈ (R q).carrier → ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n (R q).carrier x Q ∧
        IsUnitOrientationOf ((R q).orient x) Q)} with hG
  have hG_ae : ∀ᵐ x ∂μHE[n], x ∈ G := by
    have h3 := ae_all_iff.2 fun q => (hND q).and (hor q)
    filter_upwards [hηt_ae, hconv, h3] with x h1 h2 h3
    exact ⟨h1, h2, h3⟩
  set Z₀ := toMeasurable μHE[n] Gᶜ with hZ₀
  have hZ₀_meas : MeasurableSet Z₀ := measurableSet_toMeasurable _ _
  have hZ₀_null : μHE[n] Z₀ = 0 := by
    rw [hZ₀, measure_toMeasurable]
    exact hG_ae
  have hgood : ∀ x, x ∉ Z₀ → x ∈ G := fun x hx => by
    by_contra h
    exact hx (subset_toMeasurable _ _ h)
  -- Step 4: integer limits
  have nat_stab : ∀ (c : ℕ → ℕ) (a : ℝ), Tendsto (fun q => (c q : ℝ)) atTop (𝓝 a) →
      ∃ q₀, (∀ q ≥ q₀, c q = c q₀) ∧ a = c q₀ := by
    intro c a h
    obtain ⟨q₀, hq₀⟩ := (Metric.tendsto_atTop.1 h) (1 / 2) (by norm_num)
    have hconst : ∀ q ≥ q₀, c q = c q₀ := by
      intro q hq
      have h1 := hq₀ q hq
      have h2 := hq₀ q₀ le_rfl
      rw [Real.dist_eq] at h1 h2
      have h3 : |(c q : ℝ) - (c q₀ : ℝ)| < 1 := by
        calc |(c q : ℝ) - (c q₀ : ℝ)| = |((c q : ℝ) - a) - ((c q₀ : ℝ) - a)| := by ring_nf
          _ ≤ |(c q : ℝ) - a| + |(c q₀ : ℝ) - a| := abs_sub _ _
          _ < 1 / 2 + 1 / 2 := add_lt_add h1 h2
          _ = 1 := by norm_num
      have h4 : |((c q : ℤ) - (c q₀ : ℤ))| < 1 := by
        have : (((c q : ℤ) - (c q₀ : ℤ) : ℤ) : ℝ) = (c q : ℝ) - (c q₀ : ℝ) := by push_cast; ring
        rw [← Int.cast_lt (R := ℝ), Int.cast_abs, this]
        simpa using h3
      have h5 := Int.abs_lt_one_iff.1 h4
      omega
    refine ⟨q₀, hconst, ?_⟩
    have h5 : Tendsto (fun q => (c q : ℝ)) atTop (𝓝 (c q₀ : ℝ)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop q₀] with q hq
      rw [hconst q hq]
    exact tendsto_nhds_unique h h5
  have hstab : ∀ x ∈ G, ∃ q₀, (∀ q ≥ q₀, b q x = b q₀ x) ∧ N (η x) = (b q₀ x : ℝ) := by
    intro x hx
    have h1 : Tendsto (fun q => N (D q x)) atTop (𝓝 (N (η x))) :=
      (hN_cont.tendsto _).comp hx.2.1
    have h2 : Tendsto (fun q => (b q x : ℝ)) atTop (𝓝 (N (η x))) :=
      h1.congr fun q => (hx.2.2 q).1
    exact nat_stab (fun q => b q x) _ h2
  -- the multiplicity θ, the carrier M₊ and the orientation ξ
  set θ : Euclid P → ℕ := Z₀ᶜ.indicator (fun y => ⌊N (ηt y)⌋₊) with hθ
  have hθ_meas : Measurable θ :=
    (Measurable.comp (show Measurable (Nat.floor : ℝ → ℕ) from Nat.floor_mono.measurable)
      (hN_cont.measurable.comp hηt_sm.measurable)).indicator hZ₀_meas.compl
  have hθ_good : ∀ x, x ∉ Z₀ → ∃ q₀, (∀ q ≥ q₀, b q x = θ x) := by
    intro x hx
    obtain ⟨q₀, hq₀, hNη⟩ := hstab x (hgood x hx)
    refine ⟨q₀, fun q hq => ?_⟩
    have h1 : θ x = b q₀ x := by
      simp only [hθ, Set.indicator_of_mem (show x ∈ Z₀ᶜ from hx)]
      rw [← (hgood x hx).1, hNη, Nat.floor_natCast]
    rw [h1, hq₀ q hq]
  set M : Set (Euclid P) := (⋃ q, (R q).carrier) ∩ Z₀ᶜ ∩ {x | 1 ≤ θ x} with hM
  have hM_meas : MeasurableSet M :=
    ((MeasurableSet.iUnion fun q => (R q).measurableSet_carrier).inter hZ₀_meas.compl).inter
      (hθ_meas (MeasurableSet.of_discrete (s := {k : ℕ | 1 ≤ k})))
  have hMU : M ⊆ U := fun x hx => by
    obtain ⟨q, hq⟩ := mem_iUnion.1 hx.1.1
    exact (R q).carrier_subset hq
  set ξ : Euclid P → MultiVector P n := M.indicator (fun x => ((θ x : ℝ))⁻¹ • ηt x) with hξ
  have hθr_meas : Measurable (fun x => ((θ x : ℝ))⁻¹) :=
    (measurable_from_nat.comp hθ_meas : Measurable (fun x => (θ x : ℝ))).inv
  have hξ_sm : StronglyMeasurable ξ :=
    (hθr_meas.stronglyMeasurable.smul hηt_sm).indicator hM_meas
  -- Step 6: Fatou and local finiteness
  have hmeasK : ∀ q (K : Set (Euclid P)), MeasurableSet K →
      (R q).measure K = ∫⁻ x, K.indicator (fun y => (b q y : ℝ≥0∞)) x ∂μHE[n] := by
    intro q K hKm
    have hNm := (R q).measurableSet_carrier
    have h1 : K.indicator (fun y => (b q y : ℝ≥0∞)) =
        (K ∩ (R q).carrier).indicator (fun y => ((R q).mult y : ℝ≥0∞)) := by
      funext y
      by_cases hyK : y ∈ K <;> by_cases hyN : y ∈ (R q).carrier <;> simp [hb, hyK, hyN]
    rw [h1, lintegral_indicator (hKm.inter hNm), IMRep.measure, withDensity_apply _ hKm,
      Measure.restrict_restrict hKm]
  have hM_lint : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in M ∩ K, (θ x : ℝ≥0∞) ∂μHE[n] ≠ ∞ := by
    intro K hK hKU
    obtain ⟨C, hC, hCq⟩ := hbound K hK hKU
    have hKm := hK.measurableSet
    have hpt : ∀ x, (M ∩ K).indicator (fun y => (θ y : ℝ≥0∞)) x ≤
        liminf (fun q => K.indicator (fun y => (b q y : ℝ≥0∞)) x) atTop := by
      intro x
      by_cases hx : x ∈ M ∩ K
      · rw [Set.indicator_of_mem hx]
        obtain ⟨q₀, hq₀⟩ := hθ_good x hx.1.1.2
        have hev : (fun q => K.indicator (fun y => (b q y : ℝ≥0∞)) x) =ᶠ[atTop]
            fun _ => (θ x : ℝ≥0∞) := by
          filter_upwards [eventually_ge_atTop q₀] with q hq
          rw [Set.indicator_of_mem hx.2, hq₀ q hq]
        rw [(tendsto_const_nhds.congr' hev.symm).liminf_eq]
      · rw [Set.indicator_of_notMem hx]
        exact zero_le
    have hlt : ∫⁻ x in M ∩ K, (θ x : ℝ≥0∞) ∂μHE[n] ≤ C := by
      calc ∫⁻ x in M ∩ K, (θ x : ℝ≥0∞) ∂μHE[n]
          = ∫⁻ x, (M ∩ K).indicator (fun y => (θ y : ℝ≥0∞)) x ∂μHE[n] :=
            (lintegral_indicator (hM_meas.inter hKm) _).symm
        _ ≤ ∫⁻ x, liminf (fun q => K.indicator (fun y => (b q y : ℝ≥0∞)) x) atTop ∂μHE[n] :=
            lintegral_mono hpt
        _ ≤ liminf (fun q => ∫⁻ x, K.indicator (fun y => (b q y : ℝ≥0∞)) x ∂μHE[n]) atTop :=
            lintegral_liminf_le fun q =>
              ((measurable_from_nat.comp (hb_meas q) : Measurable (fun y => (b q y : ℝ≥0∞)))).indicator hKm
        _ = liminf (fun q => (R q).measure K) atTop := by
            congr 1
            funext q
            exact (hmeasK q K hKm).symm
        _ ≤ C := liminf_le_of_frequently_le' (Frequently.of_forall hCq)
    exact ne_top_of_le_ne_top hC hlt
  have hNq_fin : ∀ q (K : Set (Euclid P)), IsCompact K → K ⊆ U →
      μHE[n] ((R q).carrier ∩ K) ≠ ∞ := by
    intro q K hK hKU
    refine ne_top_of_le_ne_top ((R q).locallyIntegrable_mult K hK hKU) ?_
    calc μHE[n] ((R q).carrier ∩ K) = ∫⁻ _ in (R q).carrier ∩ K, 1 ∂μHE[n] :=
          (setLIntegral_one _).symm
      _ ≤ ∫⁻ x in (R q).carrier ∩ K, ((R q).mult x : ℝ≥0∞) ∂μHE[n] := by
          apply setLIntegral_mono' ((R q).measurableSet_carrier.inter hK.measurableSet)
          intro x hx
          exact_mod_cast (R q).mult_pos x hx.1
  have hM_fin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M ∩ K) ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (hM_lint K hK hKU) ?_
    calc μHE[n] (M ∩ K) = ∫⁻ _ in M ∩ K, 1 ∂μHE[n] := (setLIntegral_one _).symm
      _ ≤ ∫⁻ x in M ∩ K, (θ x : ℝ≥0∞) ∂μHE[n] := by
          apply setLIntegral_mono' (hM_meas.inter hK.measurableSet)
          intro x hx
          exact_mod_cast hx.1.2
  -- Step 7: orientation
  have htan : ∀ q, ∀ᵐ x ∂μHE[n], x ∈ M ∩ (R q).carrier → ∀ Q : Submodule ℝ (Euclid P),
      (HasApproximateTangentSpaceAt n (M ∩ (R q).carrier) x Q ↔
        HasApproximateTangentSpaceAt n (R q).carrier x Q) ∧
      (HasApproximateTangentSpaceAt n (M ∩ (R q).carrier) x Q ↔
        HasApproximateTangentSpaceAt n M x Q) := by
    intro q
    have hMq := hM_meas.inter (R q).measurableSet_carrier
    have h1 := hIMC.1 P n U (M ∩ (R q).carrier) (R q).carrier hU hMq
      (R q).measurableSet_carrier inter_subset_right (R q).carrier_subset (hNq_fin q)
    have h2 := hIMC.1 P n U (M ∩ (R q).carrier) M hU hMq hM_meas inter_subset_left hMU hM_fin
    rw [ae_restrict_iff' hMq] at h1 h2
    filter_upwards [h1, h2] with x hx1 hx2 hx Q
    exact ⟨hx1 hx Q, hx2 hx Q⟩
  have htan' := ae_all_iff.2 htan
  have horients : ∀ᵐ x ∂(μHE[n].restrict M), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n M x Q ∧ IsUnitOrientationOf (ξ x) Q := by
    rw [ae_restrict_iff' hM_meas]
    filter_upwards [htan'] with x hx hxM
    have hxZ : x ∉ Z₀ := hxM.1.2
    have hxG := hgood x hxZ
    obtain ⟨q₀, hq₀⟩ := hθ_good x hxZ
    have hθpos : 1 ≤ θ x := hxM.2
    have hmem : ∀ q ≥ q₀, x ∈ (R q).carrier ∧ (R q).mult x = θ x := by
      intro q hq
      have h1 := hq₀ q hq
      by_cases hxq : x ∈ (R q).carrier
      · refine ⟨hxq, ?_⟩
        simpa [hb, hxq] using h1
      · exfalso
        simp only [hb, Set.indicator_of_notMem hxq] at h1
        omega
    have hTq : ∀ q ≥ q₀, ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n M x Q ∧ IsUnitOrientationOf ((R q).orient x) Q := by
      intro q hq
      have hxq := (hmem q hq).1
      obtain ⟨Q, hQT, hQu⟩ := (hxG.2.2 q).2 hxq
      refine ⟨Q, ?_, hQu⟩
      have h := hx q ⟨hxM, hxq⟩ Q
      exact h.2.1 (h.1.2 hQT)
    obtain ⟨Q, hQT, hQu⟩ := hTq q₀ le_rfl
    set e := (R q₀).orient x with he
    have hpm : ∀ q ≥ q₀, (R q).orient x ∈ ({e, -e} : Set (MultiVector P n)) := by
      intro q hq
      obtain ⟨Q', hQ'T, hQ'u⟩ := hTq q hq
      have hQQ' : Q' = Q := hQ'T.unique hQT
      rw [hQQ'] at hQ'u
      rcases hsign P n e ((R q).orient x) Q hQu hQ'u with h | h
      · exact Or.inl h
      · exact Or.inr h
    have hθx0 : (θ x : ℝ) ≠ 0 := by
      have : θ x ≠ 0 := by omega
      exact_mod_cast this
    have hlim : Tendsto (fun q => (R q).orient x) atTop (𝓝 (ξ x)) := by
      have h1 : Tendsto (fun q => ((θ x : ℝ))⁻¹ • D q x) atTop (𝓝 (((θ x : ℝ))⁻¹ • η x)) :=
        hxG.2.1.const_smul _
      have h2 : ξ x = ((θ x : ℝ))⁻¹ • η x := by
        simp only [hξ, Set.indicator_of_mem hxM, hxG.1]
      rw [h2]
      refine h1.congr' ?_
      filter_upwards [eventually_ge_atTop q₀] with q hq
      obtain ⟨hxq, hmq⟩ := hmem q hq
      simp only [hD, Set.indicator_of_mem hxq, hmq, smul_smul, inv_mul_cancel₀ hθx0, one_smul]
    have hclosed : IsClosed ({e, -e} : Set (MultiVector P n)) :=
      (Set.toFinite _).isClosed
    have hξmem : ξ x ∈ ({e, -e} : Set (MultiVector P n)) :=
      hclosed.mem_of_tendsto hlim (eventually_atTop.2 ⟨q₀, hpm⟩)
    refine ⟨Q, hQT, ?_⟩
    rcases hξmem with h | h
    · rw [h]
      exact hQu
    · rw [Set.mem_singleton_iff.1 h]
      obtain ⟨τ, hτ, hspan, hs⟩ := hQu
      refine ⟨τ, hτ, hspan, ?_⟩
      rcases hs with hs | hs
      · right
        intro α
        rw [ContinuousLinearMap.neg_apply, hs α]
      · left
        intro α
        rw [ContinuousLinearMap.neg_apply, hs α, neg_neg]
  -- Step 8: the IMRep
  let R' : IMRep U n :=
    { carrier := M
      mult := θ
      orient := ξ
      measurableSet_carrier := hM_meas
      carrier_subset := hMU
      rectifiable := (Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion _
        fun q => (R q).rectifiable).mono fun x hx => hx.1.1
      measurable_mult := hθ_meas
      mult_pos := fun x hx => hx.2
      locallyIntegrable_mult := hM_lint
      aestronglyMeasurable_orient := hξ_sm.aestronglyMeasurable
      orients := horients }
  -- Step 9: the density of R' is η a.e., and the action formula
  have hdens : ∀ᵐ x ∂μHE[n], M.indicator (fun y => (θ y : ℝ) • ξ y) x = η x := by
    have hZ := measure_eq_zero_iff_ae_notMem.1 hZ₀_null
    filter_upwards [hZ] with x hxZ
    have hxG := hgood x hxZ
    by_cases hxM : x ∈ M
    · have hθ1 : 1 ≤ θ x := hxM.2
      have hθx0 : (θ x : ℝ) ≠ 0 := by
        have : θ x ≠ 0 := by omega
        exact_mod_cast this
      simp only [Set.indicator_of_mem hxM, hξ, smul_smul, mul_inv_cancel₀ hθx0, one_smul]
      exact hxG.1.symm
    · rw [Set.indicator_of_notMem hxM]
      obtain ⟨q₀, hq₀⟩ := hθ_good x hxZ
      have hzero : ∀ q ≥ q₀, D q x = 0 := by
        intro q hq
        by_cases hxq : x ∈ (R q).carrier
        · exfalso
          apply hxM
          refine ⟨⟨mem_iUnion.2 ⟨q, hxq⟩, hxZ⟩, ?_⟩
          show 1 ≤ θ x
          rw [← hq₀ q hq]
          simp only [hb, Set.indicator_of_mem hxq]
          exact (R q).mult_pos x hxq
        · simp only [hD, Set.indicator_of_notMem hxq]
      have h5 : Tendsto (fun q => D q x) atTop (𝓝 0) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop q₀] with q hq
        rw [hzero q hq]
      exact tendsto_nhds_unique h5 hxG.2.1
  refine ⟨R', hdens, fun ω => ?_⟩
  show ∫ x in M, (θ x : ℝ) * ξ x (ω x) ∂μHE[n] = ∫ x, η x (ω x) ∂μHE[n]
  rw [← integral_indicator hM_meas]
  apply integral_congr_ae
  filter_upwards [hdens] with x hx
  rw [← hx]
  by_cases hxM : x ∈ M
  · simp only [Set.indicator_of_mem hxM, ContinuousLinearMap.smul_apply, smul_eq_mul]
  · simp only [Set.indicator_of_notMem hxM, ContinuousLinearMap.zero_apply]

Implementation notes (Lean v4.35.0-rc3, Mathlib 25730c7c, after import GMT.Ch07.Submission): for MultiVector P n, generic normed-group lemmas may fail to find instances; use ContinuousLinearMap.opNorm_smul_le / ContinuousLinearMap.opNorm_zero instead of norm_smul / norm_zero, Summable.of_norm_bounded (E := MultiVector P n), and the explicit instance @PseudoEMetricSpace.pseudoMetrizableSpace _ (inferInstance : PseudoEMetricSpace (MultiVector P n)) before aestronglyMeasurable_of_tendsto_ae; Nat.measurable_floor is not imported, use Nat.floor_mono.measurable.

## Key steps

1. N(ζ) := √|ζ(Lζ)| with L from (UOD) is continuous and N(cζ) = c for unit orientations ζ and c ≥ 0, so N(D_{R_q}) = 1_{N_q}ϑ_q Hⁿ-a.e.
2. The natural numbers 1_{N_q}(x)ϑ_q(x) converge to N(η(x)), hence equal θ(x) := ⌊N(η̃(x))⌋ for all q ≥ q₀(x), off a Borel null set Z₀.
3. M₊ := (⋃_q N_q) ∖ Z₀ ∩ {θ ≥ 1} and ξ := η̃/θ on M₊ are Borel; on M₊ eventually x ∈ N_q, ϑ_q(x) = θ(x) and ζ_q(x) = D_{R_q}(x)/θ(x) → ξ(x).
4. Fatou with μ_{R_q}(K) ≤ C_K gives ∫_{M₊∩K} θ dHⁿ ≤ C_K, hence local finiteness of Hⁿ⌞M₊.
5. (IMC)(a) on M₊ ∩ N_q ⊆ N_q, M₊, tangent-plane uniqueness and orientation_sign put ζ_q(x) in the closed set {±e}, so ξ(x) is a unit orientation of the approximate tangent plane of M₊; (M₊, θ, ξ) is an IMRep.
6. D_{R'} = η Hⁿ-a.e., hence R'.action(ω) = ∫ η(ω) dHⁿ for every n-form ω.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `sed -n 880,945p book/chapter-06.txt (Simon Ch. 6, Lemma 3.13 and its printed proof)`
- `sed -n 1,116p .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean; sed -n 100,200p .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean (massAdmissibleOn, massOn, mass, le_massOn, GeometricCurrentOn, TestFormOn)`
- `rg -n 'theorem countablyRectifiable_of_measure_zero|theorem CountablyRectifiable.mono|theorem countablyRectifiable_iUnion|theorem HasApproximateTangentSpaceAt.unique' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `python3 -I scans of dag.json (re-read at 2026-10-13T13:51Z): accepted declarations mentioning IMRep / IsIntegerMultiplicity / IsUnitOrientationOf; status and byte-identical frozen type of the 7 reused declarations (all still accepted); cmc_fc_series_current, cmcdt_im_series and cmcdt_ims_imrep_tsum are speculative-ready, not accepted, hence not reusable; no collision for dor_lmb_fc_ims_*`
- `grep -rl dor_lmb_fc_ims_ nodes decomposition-reopenings (no match)`
- `git show 0af9ed59:GMT/Ch07/Submission.lean (theorem Submission.rsdic_exists_imrep_int_combination); git show d76960cc:GMT/Ch07/Submission.lean (PseudoMetrizableSpace (MultiVector P n) instance workaround)`
- `rg -n in local-references/123e8435b4a2469b/mathlib: hasSum_integral_of_dominated_convergence, integral_tsum, lintegral_tsum, lintegral_liminf_le, ae_lt_top, aestronglyMeasurable_of_tendsto_ae, measure_eq_zero_iff_ae_notMem, Set.Finite.isClosed, liminf_le_of_frequently_le', UniformSpace.pseudoMetrizableSpace, Summable.of_norm_bounded, HasSum.mapL`
- `cat nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-im-series-a1/decomposition-audit-v1.json (parallel im_series split via a common orientation, accepted)`
- `python3 -I gmt-compare.py contract_scope replay and lean_contract.validate_lean_statement on all 10 lean_statement strings`
- `lake env lean /tmp/ims-decomp/lean/{Types,Assembly,ChildA,ChildB,ChildC,ChildC_noHB,Final}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-ac22a8c7fb/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-convergence-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-im-series-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Separation/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Metrizable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/InfiniteSum.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/InfiniteSum/Module.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ims-decomp/lean/Assembly.lean`
- `/tmp/ims-decomp/lean/ChildA.lean`
- `/tmp/ims-decomp/lean/ChildB.lean`
- `/tmp/ims-decomp/lean/ChildC.lean`
- `/tmp/ims-decomp/lean/Final.lean`

Snapshot: project b4d606db and mathlib 25730c7c. The snapshot Ch07 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.
Neither SimonGMT nor the snapshot contains Simon's Lemma 3.13 or any completeness result for IM currents. Seven comparator-accepted DAG declarations supply the needed IMRep calculus and are reused with byte-identical frozen types: dor_imrep_massOn_eq_measure_and_support (C1), cmc_imRep_locality_restrict_sub (IMC), dor_ims_unitOrientation_dual (UOD), unit_orientation_norm_le_one, rsdic_exists_imrep_int_combination, dor_lmb_ic_measure_le_of_weighted_orient_eq and rsdic_unitOrientation_eq_or_eq_neg. cmc_fc_series_current has the type of supplied step 1 but is only speculative-ready, so it is not reused; the assembly gets Y from (IMC)(b) instead. The speculative-ready cmcdt_ims_imrep_tsum overlaps the three new children taken together and is likewise not reusable. SimonGMT supplies countablyRectifiable_of_measure_zero / iUnion / mono and HasApproximateTangentSpaceAt.unique. The snapshot Mathlib supplies dominated convergence for series, Fatou, a.e. limits of a.e. strongly measurable maps, and Summable.of_norm_bounded.
Lean: all ten child types elaborate in the replayed comparator scope. The three new children and the exact parent type are kernel-checked conditionally on the reused frozen types with axioms [propext, Classical.choice, Quot.sound], and they compile as drop-in Submission declarations.
