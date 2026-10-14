# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.source_charts-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions: ℝ^P = EuclideanSpace ℝ (Fin P) (Lean `Eucl P`) with inner product ⟨·,·⟩ and norm |·|; Hⁿ = μHE[n], Mathlib's Euclidean-normalised n-dimensional Hausdorff measure, which equals Lebesgue measure Lⁿ = volume on ℝⁿ. An n-covector on E is a continuous alternating n-linear map α : Eⁿ → ℝ with the operator norm. An n-vector is a continuous linear functional on n-covectors (`NVector E n`), also with the operator norm. simpleNVector v is the n-vector α ↦ α(v₁,…,vₙ). For a continuous linear map A, A_#u := nVectorPushforward n A u = u ∘ A^#, where A^#α = α(A·,…,A·). Thus A_# is linear in u, and A_#(simpleNVector v) = simpleNVector(A∘v) (`nVectorPushforward_simple`). `HasWeightedApproximateTangentSpaceAt n M θ x T` is Simon's weighted approximate tangent space (Ch. 3, 1.7). By SimonGMT `HasWeightedApproximateTangentSpaceAt.unique` it is unique when θ(x) ≠ 0, and its first component says dim T = n. The derivative clause for (M, θ, f, L) means: for Hⁿ⌞M-a.e. x, for every subspace T with HasWeightedApproximateTangentSpaceAt n M θ x T and every v ∈ T, the map t ↦ f(x + t v) has derivative L(x)v at t = 0. Φ is c-antilipschitz on Ω if c|w − w′| ≤ |Φ(w) − Φ(w′)| for all w, w′ ∈ Ω.

This is Step 6 of the parent proof, together with the regular-point analysis of Step 1 and the induced orientation of Step 3. The parent's disjoint pieces A_{j,k} are replaced by an a.e. statement at the source point x: disjointness, and injectivity of f on the pieces, are not needed for this conclusion. Write Ξ(x) := L(x)_#ξ(x).

1. (Source charts.) The field `countablyRectifiable` says M is countably n-rectifiable, so (CRC) gives C¹ maps Φ_j : ℝⁿ → ℝ^P and open Ω_j ⊆ ℝⁿ with Φ_j K_j-Lipschitz on Ω_j, Φ_j c_j-antilipschitz on Ω_j (c_j > 0), and Hⁿ(M ∖ ⋃_j Φ_j(Ω_j)) = 0. Put Ω′_j := Ω_j ∩ Φ_j⁻¹(U), open since Φ_j is continuous and U is open. Φ_j is still K_j-Lipschitz and c_j-antilipschitz on Ω′_j. Since M ⊆ U, M ∩ Φ_j(Ω_j) ⊆ Φ_j(Ω′_j), so Hⁿ(M ∖ ⋃_j Φ_j(Ω′_j)) = 0.
2. (u_j := f∘Φ_j is locally Lipschitz on Ω′_j.) Let w ∈ Ω′_j and x := Φ_j(w) ∈ U. Since U is open, f is Λ-Lipschitz on a neighbourhood N ⊆ U of x. Then Ω′_j ∩ Φ_j⁻¹(N) is a neighbourhood of w within Ω′_j on which u_j is ΛK_j-Lipschitz. (In Lean: unfold `LocallyLipschitzOn`; Ω′_j ∩ Φ_j⁻¹(N) ∈ 𝓝[Ω′_j] w by continuity of Φ_j at w; then use `LipschitzOnWith.comp` and `LipschitzOnWith.mono`. Note that `LocallyLipschitzOn.comp` does not exist at this Mathlib pin.)
3. (Target charts.) For each j apply (LCIP) to u_j on the open set Ω′_j. This gives C¹ maps G_{j,k}, open O_{j,k} with G_{j,k} antilipschitz on O_{j,k}, and Borel E_{j,k} ⊆ O_{j,k} ∩ Ω′_j, such that u_j(w) = G_{j,k}(w) and u_j has Fréchet derivative DG_{j,k}(w) at w for w ∈ E_{j,k}. It also gives an Lⁿ-null set Z^c_j such that every w ∈ Ω′_j ∖ Z^c_j at which u_j has an injective Fréchet derivative lies in ⋃_k E_{j,k}. Re-index by m ∈ ℕ: G_m := G_{a,b} and O_m := O_{a,b} with (a, b) := Nat.unpair m. These G_m, O_m are C¹, open and antilipschitz, as required.
4. (Exceptional sets.) Let R be the set of x ∈ M at which the conclusion of `orients` fails, i.e. there is no orthonormal τ with HasWeightedApproximateTangentSpaceAt n M θ x (span(range τ)) and ξ(x) = ±simpleNVector τ. Since M is null-measurable and `orients` holds Hⁿ⌞M-a.e., Hⁿ(R) = Hⁿ⌞M(R) = 0 (`Measure.restrict_apply₀'`). Let B be the set of x ∈ M with Ξ(x) ≠ 0 at which the required conclusion (existence of m, w, σ) fails. Again by null-measurability of M, the asserted a.e. statement is equivalent to Hⁿ(B) = 0, which we now prove.
5. (Chart preimages of Hⁿ-null sets are Lⁿ-null.) Let Z ⊆ ℝ^P with Hⁿ(Z) = 0. Φ_j is injective on Ω′_j, so it has an inverse Ψ_j on Φ_j(Ω′_j) (`Function.invFunOn`). By antilipschitz-ness Ψ_j is c_j⁻¹-Lipschitz on Φ_j(Ω′_j), and Ω′_j ∩ Φ_j⁻¹(Z) = Ψ_j(Z ∩ Φ_j(Ω′_j)). A K-Lipschitz map multiplies Hⁿ by at most Kⁿ (SimonGMT `Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n : LipschitzOnWith K f A → μHE[n] (f '' A) ≤ K ^ n * μHE[n] A`, available through the imports of GMT.Ch06.Submission; equivalently Mathlib's `LipschitzOnWith.hausdorffMeasure_image_le` transferred to μHE), and Hⁿ = Lⁿ on ℝⁿ (`EuclideanSpace.euclideanHausdorffMeasure_eq_volume`). Hence Lⁿ(Ω′_j ∩ Φ_j⁻¹(Z)) = 0.
6. Fix j. Let Z^a_j be the set of w ∈ Ω′_j ∩ Φ_j⁻¹(M) at which the conclusion of (CCR) fails. Apply (CCR) to (U, M, θ, ξ, f, L, Φ_j, Ω′_j); its hypotheses are U open, the triple, f locally Lipschitz on U, the derivative clause, Ω′_j open, Φ_j C¹ and antilipschitz on Ω′_j. Since μ(t ∩ s) ≤ μ⌞s(t) (`Measure.le_restrict_apply`), Z^a_j is Lⁿ-null. Let Z^b_j := Ω′_j ∩ Φ_j⁻¹(R), which is Lⁿ-null by Step 5. Claim: Ω′_j ∩ Φ_j⁻¹(B) ⊆ Z^a_j ∪ Z^b_j ∪ Z^c_j. Let w ∈ Ω′_j with x := Φ_j(w) ∈ B, and suppose w ∉ Z^a_j ∪ Z^b_j ∪ Z^c_j.
 (i) x ∈ M ∖ R, so there is an orthonormal τ with HasWeightedApproximateTangentSpaceAt n M θ x (span(range τ)) and ξ(x) = ±simpleNVector τ.
 (ii) w ∉ Z^a_j, so HasWeightedApproximateTangentSpaceAt n M θ x (range DΦ_j(w)) and u_j = f∘Φ_j has Fréchet derivative D := L(x)∘DΦ_j(w) at w. θ(x) > 0 (field `pos`), so uniqueness of weighted approximate tangent spaces (`HasWeightedApproximateTangentSpaceAt.unique`) gives range DΦ_j(w) = span(range τ).
 (iii) Ξ(x) ≠ 0, so the sibling lemma lpf_pi_induced_orientation (applied with (SNA), A := L(x), w := ξ(x)) shows that L(x)∘τ is linearly independent. It also gives an orthonormal σ with span(range σ) = span(range(L(x)∘τ)) and Ξ(x) = ‖Ξ(x)‖ • simpleNVector σ or Ξ(x) = −(‖Ξ(x)‖ • simpleNVector σ).
 (iv) D is injective. DΦ_j(w) : ℝⁿ → ℝ^P has range span(range τ), of dimension n (τ orthonormal), so it is injective by rank–nullity. L(x) is injective on span(range τ), since it maps the basis τ to the linearly independent family L(x)∘τ.
 (v) w ∈ Ω′_j ∖ Z^c_j and u_j has the injective Fréchet derivative D at w, so w ∈ E_{j,k} for some k. Then w ∈ O_{j,k}, G_{j,k}(w) = u_j(w) = f(Φ_j(w)) = f(x), and u_j has Fréchet derivative DG_{j,k}(w) at w. By uniqueness of Fréchet derivatives (`HasFDerivAt.unique`), DG_{j,k}(w) = D. Hence range DG_{j,k}(w) = L(x)(range DΦ_j(w)) = L(x)(span(range τ)) = span(range(L(x)∘τ)) = span(range σ) (`Submodule.map_span`).
 (vi) With m := Nat.pair j k (so G_m = G_{j,k}, O_m = O_{j,k}), (v) and (iii) give the required conclusion at x, contradicting x ∈ B. This proves the claim.
7. By Step 6, Lⁿ(Ω′_j ∩ Φ_j⁻¹(B)) = 0. Since Φ_j is K_j-Lipschitz on Ω′_j, Hⁿ(B ∩ Φ_j(Ω′_j)) ≤ Hⁿ(Φ_j(Ω′_j ∩ Φ_j⁻¹(B))) ≤ K_jⁿ·Lⁿ(Ω′_j ∩ Φ_j⁻¹(B)) = 0 (Step 5's Lipschitz bound). Finally B ⊆ (M ∖ ⋃_j Φ_j(Ω′_j)) ∪ ⋃_j (B ∩ Φ_j(Ω′_j)), so countable subadditivity and Step 1 give Hⁿ(B) = 0. ∎

Verified Lean script (engineering aid; the mathematics is the numbered proof above). On 2026-10-12 the script below was compiled as the complete proof of `theorem Submission.lpf_pi_source_charts : <the frozen Lean statement> := by` in the child context: `import GMT.Ch06.Submission`, inside `namespace GMT.Ch06` with the contract's `open` commands. It was compiled in one file together with the other ten children's proofs, which were real proofs, not stubs. `#print axioms` gives exactly propext, Classical.choice, Quot.sound. The script adds no helper declarations; all auxiliary facts are local `have`s. It uses the declared sibling `Submission.lpf_pi_induced_orientation`. The remaining compiler output consists only of style-linter and deprecation warnings.
```
  intro hsna CRC CCR LCIP P Q n U M θ ξ f L hU htri hf hderiv
  -- antilipschitz chart preimage of an Hⁿ-null set is Lⁿ-null
  have hnull : ∀ (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)) (c : ℝ), 0 < c →
      (∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → ∀ (Z : Set (Eucl P)),
      (μHE[n] : Measure (Eucl P)) Z = 0 → (volume : Measure (Eucl n)) (Ω ∩ Φ ⁻¹' Z) = 0 := by
    intro Φ Ω c hc hanti Z hZ
    classical
    have hinj : InjOn Φ Ω := by
      intro w hw w' hw' h
      have h1 := hanti w hw w' hw'
      rw [h, sub_self, norm_zero] at h1
      have h2 : ‖w - w'‖ ≤ 0 := by
        by_contra hcon
        push_neg at hcon
        have := mul_pos hc hcon
        linarith
      exact sub_eq_zero.mp (norm_le_zero_iff.mp h2)
    have hΨlip : LipschitzOnWith (Real.toNNReal c⁻¹) (Function.invFunOn Φ Ω) (Φ '' Ω) := by
      apply LipschitzOnWith.of_dist_le_mul
      rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩
      rw [hinj.leftInvOn_invFunOn hw, hinj.leftInvOn_invFunOn hw', dist_eq_norm, dist_eq_norm,
        Real.coe_toNNReal _ (inv_nonneg.mpr hc.le), inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
      exact hanti w hw w' hw'
    have hsub : Ω ∩ Φ ⁻¹' Z ⊆ Function.invFunOn Φ Ω '' (Z ∩ Φ '' Ω) := by
      rintro w ⟨hw, hwZ⟩
      exact ⟨Φ w, ⟨hwZ, w, hw, rfl⟩, hinj.leftInvOn_invFunOn hw⟩
    rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    apply measure_mono_null hsub
    apply le_antisymm _ zero_le
    calc (μHE[n] : Measure (Eucl n)) (Function.invFunOn Φ Ω '' (Z ∩ Φ '' Ω))
        ≤ (Real.toNNReal c⁻¹ : ℝ≥0∞) ^ n * μHE[n] (Z ∩ Φ '' Ω) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            (hΨlip.mono inter_subset_right)
      _ = 0 := by rw [measure_mono_null inter_subset_left hZ, mul_zero]
  -- linear algebra of step 6(iv)-(v)
  have hlinalg : ∀ (D : Eucl n →L[ℝ] Eucl P) (A : Eucl P →L[ℝ] Eucl Q) (τ : Fin n → Eucl P),
      LinearMap.range D.toLinearMap = Submodule.span ℝ (range τ) →
      LinearIndependent ℝ (fun i => A (τ i)) →
      Function.Injective (A.comp D) ∧
        LinearMap.range (A.comp D).toLinearMap = Submodule.span ℝ (range (fun i => A (τ i))) := by
    intro D A τ hD hAτ
    have hrange : LinearMap.range (A.comp D).toLinearMap = Submodule.span ℝ (range (fun i => A (τ i))) := by
      rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp, hD, Submodule.map_span, ← range_comp]
      rfl
    refine ⟨?_, hrange⟩
    have hfr : Module.finrank ℝ (LinearMap.range (A.comp D).toLinearMap) = n := by
      rw [hrange, finrank_span_eq_card hAτ, Fintype.card_fin]
    have hker := LinearMap.finrank_range_add_finrank_ker (A.comp D).toLinearMap
    rw [hfr, finrank_euclideanSpace_fin] at hker
    have hker0 : Module.finrank ℝ (LinearMap.ker (A.comp D).toLinearMap) = 0 := by omega
    have : LinearMap.ker (A.comp D).toLinearMap = ⊥ := Submodule.finrank_eq_zero.mp hker0
    exact LinearMap.ker_eq_bot.mp this
  -- covering argument of steps 1, 4, 7
  have hcover_null : ∀ (Φ : ℕ → Eucl n → Eucl P) (Ω Ω' : ℕ → Set (Eucl n)), (∀ j, Ω' j ⊆ Ω j) →
      (∀ j, ∀ w ∈ Ω j, Φ j w ∈ M → w ∈ Ω' j) →
      (∀ j, ∃ K : ℝ≥0, LipschitzOnWith K (Φ j) (Ω j)) →
      (μHE[n] : Measure (Eucl P)) (M \ ⋃ j, Φ j '' Ω j) = 0 →
      ∀ (good : Eucl P → Prop),
      (∀ j, (volume : Measure (Eucl n)) {w | w ∈ Ω' j ∧ Φ j w ∈ M ∧ ¬ good (Φ j w)} = 0) →
      ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), good x := by
    intro Φ Ω Ω' hΩ'sub hΩ'cov hΦlip hcover good hbad
    rw [ae_iff, Measure.restrict_apply₀' htri.nullMeasurableSet]
    have hsub : {x | ¬ good x} ∩ M ⊆
        (M \ ⋃ j, Φ j '' Ω j) ∪ ⋃ j, Φ j '' {w | w ∈ Ω' j ∧ Φ j w ∈ M ∧ ¬ good (Φ j w)} := by
      rintro x ⟨hx, hxM⟩
      by_cases hc : x ∈ ⋃ j, Φ j '' Ω j
      · right
        obtain ⟨j, hj⟩ := mem_iUnion.mp hc
        obtain ⟨w, hw, rfl⟩ := hj
        exact mem_iUnion.mpr ⟨j, w, ⟨hΩ'cov j w hw hxM, hxM, hx⟩, rfl⟩
      · left; exact ⟨hxM, hc⟩
    refine measure_mono_null hsub (measure_union_null hcover (measure_iUnion_null fun j => ?_))
    obtain ⟨K, hK⟩ := hΦlip j
    apply le_antisymm _ zero_le
    calc (μHE[n] : Measure (Eucl P)) (Φ j '' {w | w ∈ Ω' j ∧ Φ j w ∈ M ∧ ¬ good (Φ j w)})
        ≤ (K : ℝ≥0∞) ^ n * μHE[n] {w | w ∈ Ω' j ∧ Φ j w ∈ M ∧ ¬ good (Φ j w)} :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            (hK.mono fun w hw => hΩ'sub j hw.1)
      _ = 0 := by rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hbad j, mul_zero]
  have hio := Submission.lpf_pi_induced_orientation hsna
  obtain ⟨Φ, Ω, hΩo, hΦc, hΦlip, hΦanti, hcover⟩ := CRC P n M htri.countablyRectifiable
  have hΩ'o : ∀ j, IsOpen (Ω j ∩ Φ j ⁻¹' U) := fun j =>
    (hΩo j).inter ((hΦc j).continuous.isOpen_preimage U hU)
  have hΦanti' : ∀ j, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω j ∩ Φ j ⁻¹' U, ∀ w' ∈ Ω j ∩ Φ j ⁻¹' U,
      c * ‖w - w'‖ ≤ ‖Φ j w - Φ j w'‖ := by
    intro j
    obtain ⟨c, hc, h⟩ := hΦanti j
    exact ⟨c, hc, fun w hw w' hw' => h w hw.1 w' hw'.1⟩
  have hloc : ∀ j, LocallyLipschitzOn (Ω j ∩ Φ j ⁻¹' U) (f ∘ Φ j) := by
    intro j w hw
    obtain ⟨K, hK⟩ := hΦlip j
    obtain ⟨Λ, t, ht, hft⟩ := hf hw.2
    rw [hU.nhdsWithin_eq hw.2] at ht
    refine ⟨Λ * K, (Ω j ∩ Φ j ⁻¹' U) ∩ Φ j ⁻¹' t,
      inter_mem_nhdsWithin _ ((hΦc j).continuous.continuousAt.preimage_mem_nhds ht), ?_⟩
    exact hft.comp (hK.mono fun w hw => hw.1.1) fun w hw => hw.2
  choose G O E hOo hGc hGanti hEm hEsub hEdisj hEeq hEcov using
    fun j => LCIP n Q (Ω j ∩ Φ j ⁻¹' U) (f ∘ Φ j) (hΩ'o j) (hloc j)
  refine ⟨fun m => G m.unpair.1 m.unpair.2, fun m => O m.unpair.1 m.unpair.2,
    fun m => hOo _ _, fun m => hGc _ _, fun m => hGanti _ _, ?_⟩
  have hR : (μHE[n] : Measure (Eucl P)) ({x | ¬ ∃ τ : Fin n → Eucl P, Orthonormal ℝ τ ∧
      HasWeightedApproximateTangentSpaceAt n M θ x (Submodule.span ℝ (range τ)) ∧
      (ξ x = simpleNVector τ ∨ ξ x = -simpleNVector τ)} ∩ M) = 0 :=
    le_antisymm ((Measure.le_restrict_apply _ _).trans (ae_iff.mp htri.orients).le) zero_le
  apply hcover_null Φ Ω (fun j => Ω j ∩ Φ j ⁻¹' U)
    (fun j => inter_subset_left) (fun j w hw hwM => ⟨hw, htri.subset hwM⟩) hΦlip hcover
  intro j
  have hCCR := CCR P Q n U M θ ξ f L (Φ j) (Ω j ∩ Φ j ⁻¹' U) hU htri hf hderiv (hΩ'o j) (hΦc j)
    (hΦanti' j)
  have hZa := le_antisymm ((Measure.le_restrict_apply _ _).trans (ae_iff.mp hCCR).le) zero_le
  obtain ⟨c, hc, hanti⟩ := hΦanti' j
  have hZb := hnull (Φ j) (Ω j ∩ Φ j ⁻¹' U) c hc hanti _ hR
  have hZc := ae_iff.mp (hEcov j)
  refine measure_mono_null ?_ (measure_union_null (measure_union_null hZa hZb) hZc)
  rintro w ⟨hw, hxM, hng⟩
  obtain ⟨hΞ, hngood⟩ := not_imp.mp hng
  by_cases ha : HasWeightedApproximateTangentSpaceAt n M θ (Φ j w)
      (LinearMap.range (fderiv ℝ (Φ j) w).toLinearMap) ∧
      HasFDerivAt (f ∘ Φ j) ((L (Φ j w)).comp (fderiv ℝ (Φ j) w)) w
  swap
  · exact Or.inl (Or.inl ⟨ha, hw, hxM⟩)
  by_cases hb : ∃ τ : Fin n → Eucl P, Orthonormal ℝ τ ∧
      HasWeightedApproximateTangentSpaceAt n M θ (Φ j w) (Submodule.span ℝ (range τ)) ∧
      (ξ (Φ j w) = simpleNVector τ ∨ ξ (Φ j w) = -simpleNVector τ)
  swap
  · exact Or.inl (Or.inr ⟨hw, hb, hxM⟩)
  refine Or.inr ?_
  show ¬ _
  intro hc'
  apply hngood
  obtain ⟨τ, hτ, htan, hξ⟩ := hb
  obtain ⟨htanΦ, hfd⟩ := ha
  have huniq : LinearMap.range (fderiv ℝ (Φ j) w).toLinearMap = Submodule.span ℝ (range τ) :=
    htanΦ.unique (htri.pos _ hxM).ne' htan
  obtain ⟨hli, σ, hσ, hσspan, hσeq⟩ := hio P Q n τ (L (Φ j w)) (ξ (Φ j w)) hτ hξ hΞ
  obtain ⟨hinj, hrange⟩ := hlinalg (fderiv ℝ (Φ j) w) (L (Φ j w)) τ huniq hli
  obtain ⟨k, hk⟩ := mem_iUnion.mp (hc' hw ⟨_, hfd, hinj⟩)
  obtain ⟨hueq, hufd⟩ := hEeq j k w hk
  have hDeq : fderiv ℝ (G j k) w = (L (Φ j w)).comp (fderiv ℝ (Φ j) w) := hufd.unique hfd
  refine ⟨Nat.pair j k, w, ?_, ?_, σ, hσ, ?_, hσeq⟩
  · simp only [Nat.unpair_pair]; exact (hEsub j k hk).1
  · simp only [Nat.unpair_pair]; exact hueq.symm
  · simp only [Nat.unpair_pair]; rw [hDeq, hrange, hσspan]
```

## Key steps

1. Source charts Φ_j on Ω′_j = Ω_j ∩ Φ_j⁻¹U from (CRC); u_j = f∘Φ_j locally Lipschitz
2. Target charts G_{j,k}, O_{j,k}, E_{j,k} from (LCIP), re-indexed by Nat.pair
3. Antilipschitz charts pull Hⁿ-null sets back to Lⁿ-null sets
4. At a.e. parameter w: orients + (CCR) + tangent uniqueness give range DΦ_j(w) = span τ and D(f∘Φ_j)(w) = L(x)∘DΦ_j(w)
5. Ξ(x) ≠ 0 ⇒ induced orientation σ and injective derivative ⇒ w ∈ E_{j,k}, DG_{j,k}(w) = L(x)∘DΦ_j(w), range = span σ
6. Bad parameters are Lⁿ-null ⇒ bad points Hⁿ-null via Lipschitz images and countable subadditivity

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp snapshot project/GMT/Ch06/{Contract,Submission}.lean against workspace GMT/Ch06/{Contract,Submission}.lean (identical)`
- `python3 over dag.json: frozen lean_statement/status of the 8 uncle nodes; all lean_name fields (226 unique); grep -c 'lpf_pi_' dag.json (0 matches)`
- `contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') from verifier/gmt-compare.py (replay: open MeasureTheory Filter Set Metric; open scoped ENNReal NNReal Topology; namespace GMT.Ch06; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasWeightedApproximateTangentSpaceAt); open Poincare.SimonGMT.Chapter01 (dimensionalUpperDensity); noncomputable section; end)`
- `lean_contract.validate_lean_statement on all 11 child statements`
- `grep -n 'def CountablyRectifiable|theorem CountablyRectifiable.mono|theorem countablyRectifiable_range|theorem countablyRectifiable_iUnion|def HasWeightedApproximateTangentSpaceAt|theorem HasWeightedApproximateTangentSpaceAt.unique' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n 'abbrev NVector|def covectorPullback|def nVectorPushforward|def simpleNVector|theorem nVectorPushforward_simple' simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean; 'abbrev Covector|abbrev DifferentialForm|def IsTestForm' Chapter06/Forms.lean; 'abbrev TestFormOn|structure GeometricCurrentOn' Chapter06/Currents.lean; 'def GeometricCurrentOn.support|theorem GeometricCurrentOn.support_subset_domain' Chapter06/CurrentLocalEquality.lean`
- `grep -n 'theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn' simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean (line 216)`
- `grep -n 'LocallyLipschitzOn.comp|protected lemma comp' mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean (only LocallyLipschitz.comp exists)`
- `lake build GMT.Ch06.Submission in /tmp/lpi3_scratch (scratch copy, .lake/packages linked to the pinned package tree)`
- `lake env lean Scratch/Stmts.lean (11 statements in comparator scope, only sorry warnings)`
- `lake env lean Scratch/Names.lean (#check of ~90 cited Mathlib/SimonGMT names; #synth Norm (NVector (Eucl 3) 2) = ContinuousLinearMap.hasOpNorm, ENorm via SeminormedAddGroup.toContinuousENorm, MeasureSpace (Eucl 3) = measureSpaceOfInnerProductSpace, Norm (Covector ..) = ContinuousAlternatingMap.instNormedAddCommGroup.toNorm)`
- `lake env lean Scratch/Inst.lean (#synth ContinuousAdd / PseudoMetrizableSpace / ContinuousENorm (NVector (Eucl 3) 2) fail; documented workarounds compile)`
- `lake env lean Scratch/Assembly.lean (parent from 19 stubs; #print axioms propext, sorryAx, Classical.choice, Quot.sound)`
- `lake env lean Scratch/AllChildren.lean and Scratch/E2E.lean (all 11 children proved in dependency order + parent assembly; per-child #print axioms = propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-locally-lipschitz-image-a1-inner-com-6be04fd41f/rlcr-plan-v1.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/lpi3_scratch/Scratch/Stmts.lean`
- `/tmp/lpi3_scratch/Scratch/Names.lean`
- `/tmp/lpi3_scratch/Scratch/Inst.lean`
- `/tmp/lpi3_scratch/Scratch/Assembly.lean`
- `/tmp/lpi3_scratch/Scratch/AllChildren.lean`
- `/tmp/lpi3_scratch/Scratch/E2E.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) is byte-identical to the workspace Contract and Submission. The child scope is import GMT.Ch06.Submission plus the replayed namespace and opens. It provides the contract notions (IsRectifiableTriple, tauAction, IsIntegerMultiplicity) and SimonGMT Ch03 Rectifiable (CountablyRectifiable with mono/range/iUnion, HasWeightedApproximateTangentSpaceAt, .unique for θ x ≠ 0). It also provides Ch06 n-vectors (NVector = Covector →L[ℝ] ℝ with the operator norm, simpleNVector, nVectorPushforward_simple), test forms, currents and support_subset_domain, plus Ch02 euclideanHausdorffMeasure_image_le_of_lipschitzOn.

It does not provide:
- SimonGMT SubmanifoldCover (countablyRectifiable_image_contDiffOn_open) or Mathlib's Multilinear.FiniteDimensional; both facts are therefore separate import-free leaves.
- LocallyLipschitzOn.comp.
- Instance search on NVector for ContinuousAdd, PseudoMetrizableSpace, ContinuousENorm and NormSMulClass; the verified workarounds are recorded in the child texts.

No lpf_pi_* name is reserved in dag.json, and leaf plans forbid helper declarations, so every child script is a single theorem. All 11 frozen statements validate and elaborate in the comparator scope. All 11 children are fully proved in Lean with only propext, Classical.choice and Quot.sound, using only their declared siblings. The frozen parent type follows from them and the eight uncles by the stated assembly; its only sorryAx comes from the uncle stubs.
