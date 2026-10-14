# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.im_of_chart_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions: ℝ^P = EuclideanSpace ℝ (Fin P) (Lean `Eucl P`) with inner product ⟨·,·⟩ and norm |·|; Hⁿ = μHE[n], Mathlib's Euclidean-normalised n-dimensional Hausdorff measure, which equals Lebesgue measure Lⁿ = volume on ℝⁿ. An n-covector on E is a continuous alternating n-linear map α : Eⁿ → ℝ with the operator norm. An n-vector is a continuous linear functional on n-covectors (`NVector E n`), also with the operator norm. simpleNVector v is the n-vector α ↦ α(v₁,…,vₙ). For a continuous linear map A, A_#u := nVectorPushforward n A u = u ∘ A^#, where A^#α = α(A·,…,A·). Thus A_# is linear in u, and A_#(simpleNVector v) = simpleNVector(A∘v) (`nVectorPushforward_simple`). `HasWeightedApproximateTangentSpaceAt n M θ x T` is Simon's weighted approximate tangent space (Ch. 3, 1.7). By SimonGMT `HasWeightedApproximateTangentSpaceAt.unique` it is unique when θ(x) ≠ 0, and its first component says dim T = n. The derivative clause for (M, θ, f, L) means: for Hⁿ⌞M-a.e. x, for every subspace T with HasWeightedApproximateTangentSpaceAt n M θ x T and every v ∈ T, the map t ↦ f(x + t v) has derivative L(x)v at t = 0. Φ is c-antilipschitz on Ω if c|w − w′| ≤ |Φ(w) − Φ(w′)| for all w, w′ ∈ Ω.

This is Steps 7, 8 (the integer coefficient), 10 and 11 of the parent proof, stated for an abstract chart-oriented density. As in the parent, the tangent plane at a.e. image point is first identified through the auxiliary pair (Y, 1), and then the orientation field is checked through (M′, θ′).

1. (Tangent planes of (Y, 1).) For each k apply (WTC) to (V, Y, θ ≡ 1, G_k, O_k). The hypotheses hold: V open; Y ⊆ V null-measurable; 1 > 0; 1 is integrable on Y ∩ K because Hⁿ(Y ∩ K) < ∞ (`integrableOn_const_iff`); O_k open; G_k C¹ and antilipschitz. Let E_k be the set of y ∈ Y ∩ G_k(O_k) for which some w ∈ O_k with G_k(w) = y fails HasWeightedApproximateTangentSpaceAt n Y 1 y (range DG_k(w)). E_k is Hⁿ-null because μ(t ∩ s) ≤ μ⌞s(t) (`Measure.le_restrict_apply`). Let E₀ be the set of y ∈ Y for which the assumed family does not exist; Hⁿ(E₀) = 0, again because μ(t ∩ s) ≤ μ⌞s(t) (`Measure.le_restrict_apply`), here with s = Y. Put E := E₀ ∪ ⋃_k E_k, an Hⁿ-null set.
2. (Common plane, integer coefficient.) Let y ∈ Y ∖ E with family (m, a, k, w, σ) and m ≥ 1. For each i, y = G_{k_i}(w_i) ∈ Y ∩ G_{k_i}(O_{k_i}) and y ∉ E_{k_i}, so HasWeightedApproximateTangentSpaceAt n Y 1 y (span(range σ_i)). The weight 1 is nonzero, so uniqueness (`HasWeightedApproximateTangentSpaceAt.unique`) gives span(range σ_i) = span(range σ_1) for every i. By part (b) of the sibling lemma lpf_pi_simple_unit_facts (applied to (SNA)), simpleNVector σ_i = ε_i • simpleNVector σ_1 with ε_i ∈ {1, −1}. Hence Ψ(y) = c(y) • simpleNVector σ_1 with c(y) := Σ_i ε_i a_i ∈ ℤ. By part (a) of lpf_pi_simple_unit_facts, ‖Ψ(y)‖ = |c(y)|. If m = 0, then Ψ(y) = 0 (empty sum).
3. (The new triple.) Put M′ := {y ∈ Y ∖ E : Ψ(y) ≠ 0}, θ′(y) := ‖Ψ(y)‖ and ξ′(y) := ‖Ψ(y)‖⁻¹ • Ψ(y). For y ∈ M′, Step 2 applies with m ≥ 1 and c(y) ≠ 0. So θ′(y) = |c(y)| = (c(y).natAbs : ℝ) is a positive integer, and ξ′(y) = (c(y)/|c(y)|) • simpleNVector σ_1, i.e. ξ′(y) = simpleNVector σ_1 or ξ′(y) = −simpleNVector σ_1.
4. (Representation.) Let ω ∈ Dⁿ(V). The integrand y ↦ Ψ(y)(ω(y)) vanishes on (Y ∖ E) ∖ M′, and E is null. With Y null-measurable, `setIntegral_eq_of_subset_of_ae_sdiff_eq_zero` gives S(ω) = ∫_Y Ψ(ω) dHⁿ = ∫_{M′} Ψ(ω) dHⁿ. On M′, θ′(y)·ξ′(y)(ω(y)) = ‖Ψ(y)‖·‖Ψ(y)‖⁻¹·Ψ(y)(ω(y)) = Ψ(y)(ω(y)), since ‖Ψ(y)‖ ≠ 0. Hence S(ω) = ∫_{M′} θ′ ξ′(ω) dHⁿ = tauAction n M′ θ′ ξ′ ω.
5. (IsRectifiableTriple V n M′ θ′ ξ′.)
 • subset: M′ ⊆ Y ⊆ V.
 • nullMeasurableSet: Y is null-measurable, E is null, and {y ∈ Y : Ψ(y) ≠ 0} = Y ∩ {‖Ψ‖ ≠ 0} is null-measurable, because ‖Ψ‖ is Hⁿ⌞Y-a.e. measurable and Y is null-measurable.
 • countablyRectifiable: by Step 3 every y ∈ M′ has a family with m ≥ 1, so y = G_{k_1}(w_1) ∈ G_{k_1}(O_{k_1}). Thus M′ ⊆ ⋃_k G_k(O_k). Each G_k(O_k) is countably n-rectifiable by the sibling lemma lpf_pi_chart_image_rectifiable (hypotheses: O_k is open and G_k is C¹ on O_k, the latter from `ContDiff.contDiffOn`). A countable union and a subset of countably n-rectifiable sets are countably n-rectifiable (`Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion`, `CountablyRectifiable.mono`; both live in Poincare.SimonGMT.Chapter03.Rectifiable, which GMT.Ch06.Submission imports). Do not use SimonGMT's `countablyRectifiable_image_contDiffOn_open`: its module Poincare.SimonGMT.Chapter03.SubmanifoldCover is not imported by GMT.Ch06.Submission, and a child may not add imports.
 • pos: θ′(y) = ‖Ψ(y)‖ > 0 for y ∈ M′.
 • integrableOn: for compact K ⊆ V, M′ ∩ K ⊆ Y ∩ K and ‖Ψ‖ is integrable on Y ∩ K (`IntegrableOn.mono_set`).
 • aestronglyMeasurable: ξ′ = ‖Ψ‖⁻¹ • Ψ is Hⁿ⌞Y-a.e. strongly measurable, hence Hⁿ⌞M′-a.e. strongly measurable (M′ ⊆ Y).
 • orients: for each k apply (WTC) to (V, M′, θ′, G_k, O_k); its hypotheses are the five items just verified, together with O_k open and G_k C¹ and antilipschitz. Let E′_k be the set of y ∈ M′ ∩ G_k(O_k) for which some w ∈ O_k with G_k(w) = y fails HasWeightedApproximateTangentSpaceAt n M′ θ′ y (range DG_k(w)); E′_k is Hⁿ-null as in Step 1. For y ∈ M′ ∖ ⋃_k E′_k take the family of Step 3. Since y = G_{k_1}(w_1) with w_1 ∈ O_{k_1}, HasWeightedApproximateTangentSpaceAt n M′ θ′ y (range DG_{k_1}(w_1)), and range DG_{k_1}(w_1) = span(range σ_1). Moreover σ_1 is orthonormal and ξ′(y) = ±simpleNVector σ_1 (Step 3), so τ := σ_1 witnesses `orients` at y. This holds for Hⁿ⌞M′-a.e. y.
6. (Integrality.) For y ∈ M′, θ′(y) = (c(y).natAbs : ℝ) with c(y).natAbs ∈ ℕ.
7. Steps 4–6 give IsRectifiableTriple V n M′ θ′ ξ′, θ′(y) ∈ ℕ for y ∈ M′, and S(ω) = tauAction n M′ θ′ ξ′ ω for every ω ∈ Dⁿ(V). That is, S is integer multiplicity. ∎

Lean note (verified in this environment; engineering advice, not part of the mathematics). For maps into `NVector (Eucl Q) n`, instance search fails for `ContinuousAdd`, `TopologicalSpace.PseudoMetrizableSpace`, `ContinuousENorm` and `ContinuousEval`. So `AEStronglyMeasurable.add/.norm/.enorm`, `Finset.aestronglyMeasurable_fun_sum` and `continuous_eval` do not apply out of the box. Working replacements: (1) `have : ContinuousAdd (NVector (Eucl Q) n) := ⟨(inferInstance : IsTopologicalAddGroup (NVector (Eucl Q) n)).toContinuousAdd.continuous_add⟩`, after which finite sums and `.add` of a.e.-strongly-measurable n-vector fields work; (2) `(@continuous_norm (NVector (Eucl Q) n) _).comp_aestronglyMeasurable h` for y ↦ ‖Ψ y‖, then `ofReal_norm` to pass to ‖·‖ₑ; (3) `continuous_fst.clm_apply continuous_snd` for continuity of (ζ, α) ↦ ζ α; (4) express sets such as {Ψ ≠ 0} as {‖Ψ‖ ≠ 0}, so null-measurability comes from the real-valued a.e.-measurable function ‖Ψ‖.

Verified Lean script (engineering aid; the mathematics is the numbered proof above). On 2026-10-12 the script below was compiled as the complete proof of `theorem Submission.lpf_pi_im_of_chart_density : <the frozen Lean statement> := by` in the child context: `import GMT.Ch06.Submission`, inside `namespace GMT.Ch06` with the contract's `open` commands. It was compiled in one file together with the other ten children's proofs, which were real proofs, not stubs. `#print axioms` gives exactly propext, Classical.choice, Quot.sound. The script adds no helper declarations; all auxiliary facts are local `have`s. It uses the declared siblings `Submission.lpf_pi_simple_unit_facts`, `Submission.lpf_pi_chart_image_rectifiable`. The remaining compiler output consists only of style-linter and deprecation warnings.
```
  intro hWTC hSNA Q n V Y Ψ G O S hV hO hG hanti hYV hY hYfin hΨm hΨint hfam hS
  obtain ⟨hunit, hsign⟩ := Submission.lpf_pi_simple_unit_facts hSNA
  set μ : Measure (Eucl Q) := (μHE[n] : Measure (Eucl Q)) with hμdef
  -- Step 1: tangent planes of (Y, 1) on each chart
  let TY : ℕ → Eucl Q → Prop := fun k y => ∀ w ∈ O k, G k w = y →
      HasWeightedApproximateTangentSpaceAt n Y (fun _ => (1:ℝ)) y
        (LinearMap.range (fderiv ℝ (G k) w).toLinearMap)
  have hWY : ∀ k, ∀ᵐ y ∂(μ.restrict (Y ∩ G k '' O k)), TY k y := by
    intro k
    exact hWTC Q n V Y (fun _ => (1:ℝ)) (G k) (O k) hV hYV hY (fun _ _ => one_pos)
      (fun K hK hKV => integrableOn_const (hYfin K hK hKV).ne) (hO k) (hG k) (hanti k)
  let Ek : ℕ → Set (Eucl Q) := fun k => {y | ¬ TY k y} ∩ (Y ∩ G k '' O k)
  have hEk : ∀ k, μ (Ek k) = 0 := by
    intro k
    have h1 : μ.restrict (Y ∩ G k '' O k) {y | ¬ TY k y} = 0 := ae_iff.mp (hWY k)
    exact le_antisymm ((Measure.le_restrict_apply _ _).trans h1.le) bot_le
  let Fam : Eucl Q → Prop := fun y => ∃ (m : ℕ) (a : Fin m → ℤ) (k : Fin m → ℕ)
      (w : Fin m → Eucl n) (σ : Fin m → Fin n → Eucl Q),
      (∀ i, w i ∈ O (k i) ∧ G (k i) (w i) = y ∧ Orthonormal ℝ (σ i) ∧
        Submodule.span ℝ (range (σ i)) = LinearMap.range (fderiv ℝ (G (k i)) (w i)).toLinearMap) ∧
      Ψ y = ∑ i, (a i : ℝ) • simpleNVector (σ i)
  let E0 : Set (Eucl Q) := {y | ¬ Fam y} ∩ Y
  have hE0 : μ E0 = 0 := by
    have h1 : μ.restrict Y {y | ¬ Fam y} = 0 := ae_iff.mp hfam
    exact le_antisymm ((Measure.le_restrict_apply _ _).trans h1.le) bot_le
  let E : Set (Eucl Q) := E0 ∪ ⋃ k, Ek k
  have hE : μ E = 0 := measure_union_null hE0 (measure_iUnion_null hEk)
  -- Step 2: common plane and integer coefficient
  have key : ∀ y ∈ Y, y ∉ E → Ψ y ≠ 0 → ∃ (c : ℤ) (k₀ : ℕ) (w₀ : Eucl n) (σ₀ : Fin n → Eucl Q),
      w₀ ∈ O k₀ ∧ G k₀ w₀ = y ∧ Orthonormal ℝ σ₀ ∧
      Submodule.span ℝ (range σ₀) = LinearMap.range (fderiv ℝ (G k₀) w₀).toLinearMap ∧
      Ψ y = (c : ℝ) • simpleNVector σ₀ := by
    intro y hyY hyE hΨ0
    have hFam : Fam y := by
      by_contra hc
      exact hyE (Or.inl ⟨hc, hyY⟩)
    obtain ⟨m, a, k, w, σ, hi, hΨy⟩ := hFam
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      exact (hΨ0 (by simpa using hΨy)).elim
    · let i₀ : Fin m := ⟨0, hm⟩
      have htan : ∀ i, HasWeightedApproximateTangentSpaceAt n Y (fun _ => (1:ℝ)) y
          (LinearMap.range (fderiv ℝ (G (k i)) (w i)).toLinearMap) := by
        intro i
        have hyEk : y ∉ Ek (k i) := fun h => hyE (Or.inr (mem_iUnion.mpr ⟨k i, h⟩))
        have hmem : y ∈ Y ∩ G (k i) '' O (k i) := ⟨hyY, w i, (hi i).1, (hi i).2.1⟩
        have hT : TY (k i) y := by
          by_contra hc
          exact hyEk ⟨hc, hmem⟩
        exact hT (w i) (hi i).1 (hi i).2.1
      have hspan : ∀ i, Submodule.span ℝ (range (σ i₀)) = Submodule.span ℝ (range (σ i)) := by
        intro i
        rw [(hi i₀).2.2.2, (hi i).2.2.2]
        exact Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt.unique
          (by simp) (htan i₀) (htan i)
      have hε : ∀ i, ∃ e : ℤ, simpleNVector (σ i) = (e : ℝ) • simpleNVector (σ i₀) := by
        intro i
        rcases hsign Q n (σ i₀) (σ i) (hi i₀).2.2.1 (hi i).2.2.1 (hspan i) with h | h
        · exact ⟨1, by rw [h, Int.cast_one, one_smul]⟩
        · exact ⟨-1, by rw [h, Int.cast_neg, Int.cast_one]; exact (neg_one_smul ℝ (simpleNVector (σ i₀))).symm⟩
      choose e he using hε
      refine ⟨∑ i, a i * e i, k i₀, w i₀, σ i₀, (hi i₀).1, (hi i₀).2.1, (hi i₀).2.2.1,
        (hi i₀).2.2.2, ?_⟩
      rw [hΨy, Int.cast_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [he i, smul_smul, Int.cast_mul]
  -- Step 3: the new triple
  let M' : Set (Eucl Q) := (Y ∩ {y | ‖Ψ y‖ ≠ 0}) \ E
  let θ' : Eucl Q → ℝ := fun y => ‖Ψ y‖
  let ξ' : Eucl Q → NVector (Eucl Q) n := fun y => ‖Ψ y‖⁻¹ • Ψ y
  have hM'Y : M' ⊆ Y := fun y hy => hy.1.1
  have hM'mem : ∀ y ∈ M', y ∈ Y ∧ y ∉ E ∧ Ψ y ≠ 0 :=
    fun y hy => ⟨hy.1.1, hy.2, fun h0 => (show ‖Ψ y‖ ≠ 0 from hy.1.2) (by rw [h0]; exact ContinuousLinearMap.opNorm_zero)⟩
  have hdata : ∀ y ∈ M', ∃ (c : ℤ) (k₀ : ℕ) (w₀ : Eucl n) (σ₀ : Fin n → Eucl Q),
      w₀ ∈ O k₀ ∧ G k₀ w₀ = y ∧ Orthonormal ℝ σ₀ ∧
      Submodule.span ℝ (range σ₀) = LinearMap.range (fderiv ℝ (G k₀) w₀).toLinearMap ∧
      θ' y = (c.natAbs : ℝ) ∧ (ξ' y = simpleNVector σ₀ ∨ ξ' y = -simpleNVector σ₀) := by
    intro y hy
    obtain ⟨hyY, hyE, hΨ0⟩ := hM'mem y hy
    obtain ⟨c, k₀, w₀, σ₀, hw₀, hGw₀, hσ₀, hspan₀, hΨc⟩ := key y hyY hyE hΨ0
    have hnorm : ‖Ψ y‖ = |(c : ℝ)| := by
      haveI : NormSMulClass ℝ (NVector (Eucl Q) n) :=
        @NormedSpace.toNormSMulClass ℝ (NVector (Eucl Q) n) _ _ _
      rw [hΨc, norm_smul, hunit Q n σ₀ hσ₀, mul_one, Real.norm_eq_abs]
    have hc0 : (c : ℝ) ≠ 0 := by
      intro h; apply hΨ0; rw [hΨc, h, zero_smul]
    refine ⟨c, k₀, w₀, σ₀, hw₀, hGw₀, hσ₀, hspan₀, ?_, ?_⟩
    · show ‖Ψ y‖ = _
      rw [hnorm, Nat.cast_natAbs, Int.cast_abs]
    · show ‖Ψ y‖⁻¹ • Ψ y = _ ∨ ‖Ψ y‖⁻¹ • Ψ y = _
      rw [hnorm, hΨc, smul_smul]
      rcases lt_or_gt_of_ne hc0 with hneg | hpos
      · right
        rw [abs_of_neg hneg, inv_neg, neg_mul, inv_mul_cancel₀ hc0]; exact neg_one_smul ℝ (simpleNVector σ₀)
      · left
        rw [abs_of_pos hpos, inv_mul_cancel₀ hc0, one_smul]
  -- nullMeasurableSet
  have hnormΨ : AEStronglyMeasurable (fun y => ‖Ψ y‖) (μ.restrict Y) :=
    (@continuous_norm (NVector (Eucl Q) n) _).comp_aestronglyMeasurable hΨm
  have hM'nm : NullMeasurableSet M' μ := by
    have hg := hnormΨ.aemeasurable
    have hgm : Measurable (hg.mk _) := hg.measurable_mk
    have hae : ∀ᵐ y ∂μ, y ∈ Y → ‖Ψ y‖ = hg.mk _ y := (ae_restrict_iff'₀ hY).mp hg.ae_eq_mk
    have h1 : NullMeasurableSet (Y ∩ (hg.mk _) ⁻¹' {0}ᶜ) μ :=
      hY.inter (hgm (measurableSet_singleton 0).compl).nullMeasurableSet
    have h2 : NullMeasurableSet (Y ∩ {y | ‖Ψ y‖ ≠ 0}) μ := by
      refine h1.congr ?_
      filter_upwards [hae] with y hy
      change (y ∈ Y ∧ hg.mk _ y ≠ 0) = (y ∈ Y ∧ ‖Ψ y‖ ≠ 0)
      apply propext
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [hy h1]⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [← hy h1]⟩
    exact h2.diff (NullMeasurableSet.of_null hE)
  -- countablyRectifiable
  have hM'cov : M' ⊆ ⋃ k, G k '' O k := by
    intro y hy
    obtain ⟨c, k₀, w₀, σ₀, hw₀, hGw₀, -⟩ := hdata y hy
    exact mem_iUnion.mpr ⟨k₀, w₀, hw₀, hGw₀⟩
  have hCR : CountablyRectifiable n M' :=
    (Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion _ (fun k =>
      Submission.lpf_pi_chart_image_rectifiable Q n (G k) (O k) (hO k) (hG k).contDiffOn)).mono hM'cov
  have hθ'pos : ∀ y ∈ M', 0 < θ' y := fun y hy => show 0 < ‖Ψ y‖ from
    lt_of_le_of_ne (norm_nonneg (Ψ y)) (Ne.symm (show ‖Ψ y‖ ≠ 0 from hy.1.2))
  have hθ'int : ∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → IntegrableOn θ' (M' ∩ K) μ :=
    fun K hK hKV => (hΨint K hK hKV).mono_set (inter_subset_inter_left _ hM'Y)
  have hξ' : AEStronglyMeasurable ξ' (μ.restrict M') :=
    ((hnormΨ.aemeasurable.inv.aestronglyMeasurable).smul hΨm).mono_measure
      (Measure.restrict_mono hM'Y le_rfl)
  -- orients
  let TM : ℕ → Eucl Q → Prop := fun k y => ∀ w ∈ O k, G k w = y →
      HasWeightedApproximateTangentSpaceAt n M' θ' y (LinearMap.range (fderiv ℝ (G k) w).toLinearMap)
  have hWM : ∀ k, ∀ᵐ y ∂(μ.restrict (M' ∩ G k '' O k)), TM k y := fun k =>
    hWTC Q n V M' θ' (G k) (O k) hV (hM'Y.trans hYV) hM'nm hθ'pos hθ'int (hO k) (hG k) (hanti k)
  let E'k : ℕ → Set (Eucl Q) := fun k => {y | ¬ TM k y} ∩ (M' ∩ G k '' O k)
  have hE'k : ∀ k, μ (E'k k) = 0 := by
    intro k
    have h1 : μ.restrict (M' ∩ G k '' O k) {y | ¬ TM k y} = 0 := ae_iff.mp (hWM k)
    exact le_antisymm ((Measure.le_restrict_apply _ _).trans h1.le) bot_le
  have hE' : μ (⋃ k, E'k k) = 0 := measure_iUnion_null hE'k
  have horients : ∀ᵐ y ∂(μ.restrict M'), ∃ τ : Fin n → Eucl Q, Orthonormal ℝ τ ∧
      HasWeightedApproximateTangentSpaceAt n M' θ' y (Submodule.span ℝ (range τ)) ∧
      (ξ' y = simpleNVector τ ∨ ξ' y = -simpleNVector τ) := by
    have h1 : ∀ᵐ y ∂(μ.restrict M'), y ∉ ⋃ k, E'k k :=
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hE')
    filter_upwards [h1, ae_restrict_mem₀ hM'nm] with y hyE' hyM'
    obtain ⟨c, k₀, w₀, σ₀, hw₀, hGw₀, hσ₀, hspan₀, -, hξ⟩ := hdata y hyM'
    refine ⟨σ₀, hσ₀, ?_, hξ⟩
    have hT : TM k₀ y := by
      by_contra hc
      exact hyE' (mem_iUnion.mpr ⟨k₀, hc, hyM', w₀, hw₀, hGw₀⟩)
    rw [hspan₀]
    exact hT w₀ hw₀ hGw₀
  -- representation
  have hrep : ∀ ω : TestFormOn V n, S ω = tauAction n M' θ' ξ' ω := by
    intro ω
    rw [hS ω]
    unfold tauAction
    rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hY hM'Y ?_]
    · refine setIntegral_congr_fun₀ hM'nm ?_
      intro y hy
      have hne : ‖Ψ y‖ ≠ 0 := hy.1.2
      show Ψ y _ = ‖Ψ y‖ * ((‖Ψ y‖⁻¹ • Ψ y) _)
      rw [ContinuousLinearMap.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hE] with y hyE hy
      have h0 : ‖Ψ y‖ = 0 := by
        by_contra hc
        exact hy.2 ⟨⟨hy.1, hc⟩, hyE⟩
      have hΨ0 : Ψ y = 0 := (norm_eq_zero (E := NVector (Eucl Q) n) (a := Ψ y)).mp h0
      rw [hΨ0]
      rfl
  refine ⟨M', θ', ξ', ⟨hM'Y.trans hYV, hM'nm, hCR, hθ'pos, hθ'int, hξ', horients⟩, ?_, hrep⟩
  intro y hy
  obtain ⟨c, -, -, -, -, -, -, -, hθc, -⟩ := hdata y hy
  exact ⟨c.natAbs, hθc⟩
```

## Key steps

1. (WTC) on (Y, 1) for every chart G_k: outside a null set E, each chart through y has tangent plane T_y(Y, 1)
2. Uniqueness of T_y(Y, 1) + sign rigidity (sibling) ⇒ Ψ(y) = c(y) • simpleNVector σ_1 with c(y) ∈ ℤ, ‖Ψ(y)‖ = |c(y)|
3. M′ = {Ψ ≠ 0} ∖ E, θ′ = ‖Ψ‖ ∈ ℕ, ξ′ = Ψ/‖Ψ‖ = ±simpleNVector σ_1; S = τ(M′, θ′, ξ′)
4. Verify the triple: measurability and integrability from Ψ; rectifiability since M′ ⊆ ⋃ G_k(O_k), each countably rectifiable (sibling)
5. orients via (WTC) applied to (M′, θ′) on each chart

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
