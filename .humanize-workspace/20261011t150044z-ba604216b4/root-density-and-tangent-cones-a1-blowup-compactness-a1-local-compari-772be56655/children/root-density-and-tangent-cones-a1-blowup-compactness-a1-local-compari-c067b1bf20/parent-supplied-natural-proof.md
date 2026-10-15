# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1.gradient_field-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof (Simon Ch. 3, Definition 2.1: ∇^M f := ∇^{N_j} f on the j-th piece), with step 2(a)'s removal of the null set where the bound |∇^M f| ≤ L fails, and the null-image remark of Simon's proof of Ch. 3, 2.4 ("if φ is locally Lipschitz and B has Hⁿ-measure zero then Hⁿ(φ(B)) = 0").
Notation: K_j := closure(Y_j) (compact, K_j ⊆ V_j); L^d := volume on ℝ^d; H^d := μHE[d]; B̄_r(y) := closedBall(y, r).

1. (Chart constants.) For each j, ψ_j is C¹, injective on K_j ⊆ V_j, and Dψ_j(y) is injective for y ∈ K_j ⊆ V_j. By chart_bilipschitz there are m_j > 0 and Λ_j with m_j|a − b| ≤ |ψ_j(a) − ψ_j(b)| ≤ Λ_j|a − b| for all a, b ∈ K_j. With Λ_j⁺ := max(Λ_j, 0) ∈ [0, ∞), ψ_j is Λ_j⁺-Lipschitz on K_j (LipschitzOnWith).
2. (Pointwise gradients.) By chart_gradient applied to (ψ_j, F_j, V_j) there is h_j : ℝ^d → ℝ^P, continuous on V_j, with h_j(y) ∈ range Dψ_j(y) and ⟨h_j(y), Dψ_j(y)e⟩ = DF_j(y)e for every y ∈ V_j and e ∈ ℝ^d.
3. (Bound at density points.) Let y ∈ Y_j be a Lebesgue density point of Y_j, i.e. L^d(Y_j ∩ B̄_r(y))/L^d(B̄_r(y)) → 1 as r ↓ 0. ψ_j and F_j are differentiable at y (C¹) and f∘ψ_j = F_j on Y_j, so density_gradient_bound gives |DF_j(y)e| ≤ L|Dψ_j(y)e| for every e. By step 2 (y ∈ Y_j ⊆ V_j) write h_j(y) = Dψ_j(y)w. Then
 |h_j(y)|² = ⟨h_j(y), Dψ_j(y)w⟩ = DF_j(y)w ≤ L|Dψ_j(y)w| = L|h_j(y)|,
 hence |h_j(y)| ≤ L (trivial if h_j(y) = 0; otherwise divide by |h_j(y)|).
4. (Trimmed pieces.) Define Y′_j := {y ∈ Y_j : |h_j(y)| ≤ L}.
 (a) Y′_j ⊆ Y_j.
 (b) Y′_j is Borel: h_j is continuous on the closed set K_j ⊆ V_j, so C_j := K_j ∩ h_j⁻¹(B̄_L(0)) is closed (ContinuousOn.preimage_isClosed_of_isClosed), and Y′_j = Y_j ∩ C_j because Y_j ⊆ K_j.
 (c) L^d(Y_j ∖ Y′_j) = 0. By Lebesgue's density theorem (Besicovitch.ae_tendsto_measure_inter_div for the locally finite measure L^d on ℝ^d and the set Y_j), L^d-a.e. point of Y_j is a density point of Y_j; this is an a.e. statement for L^d restricted to Y_j, and since Y_j is measurable, ae_restrict_iff' turns it into: the set of points of Y_j which are not density points of Y_j is L^d-null. By step 3 every point of Y_j ∖ Y′_j is such a point, so L^d(Y_j ∖ Y′_j) = 0.
 (d) H^d(ψ_j(Y_j ∖ Y′_j)) = 0. Y_j ∖ Y′_j ⊆ K_j and ψ_j is Λ_j⁺-Lipschitz there, so H^d(ψ_j(Y_j ∖ Y′_j)) ≤ (Λ_j⁺)^d·H^d(Y_j ∖ Y′_j) (SimonGMT Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn); and H^d = L^d on ℝ^d (EuclideanSpace.euclideanHausdorffMeasure_eq_volume), so the right side is (Λ_j⁺)^d·0 = 0.
5. (Images.) A′_j := ψ_j(Y′_j) is Borel by the Lusin–Souslin theorem (MeasurableSet.image_of_continuousOn_injOn: Y′_j is Borel in the Polish space ℝ^d, ψ_j is continuous and injective on Y′_j ⊆ V_j). The A′_j are pairwise disjoint because A′_j ⊆ ψ_j(Y_j).
6. (Null remainder.) If x ∈ M lies in no A′_j, then either x lies in no ψ_j(Y_j), or x = ψ_j(y) for some j and y ∈ Y_j ∖ Y′_j. Hence
 M ∖ ⋃_j A′_j ⊆ (M ∖ ⋃_j ψ_j(Y_j)) ∪ ⋃_j ψ_j(Y_j ∖ Y′_j).
 Both sets on the right are H^d-null (hypothesis; step 4(d) and countable subadditivity), so H^d(M ∖ ⋃_j A′_j) = 0.
7. (Inverse charts.) Let φ_j := invFunOn ψ_j Y′_j : ℝ^P → ℝ^d (ℝ^d is nonempty). Since ψ_j is injective on Y′_j, φ_j(ψ_j(y)) = y for y ∈ Y′_j (InjOn.leftInvOn_invFunOn), so φ_j maps A′_j into Y′_j. For x = ψ_j(y) and x′ = ψ_j(y′) in A′_j (y, y′ ∈ Y′_j ⊆ K_j), step 1 gives |φ_j(x) − φ_j(x′)| = |y − y′| ≤ m_j⁻¹|x − x′|. So φ_j is Lipschitz, hence continuous, on A′_j, and g_j := h_j ∘ φ_j is continuous on A′_j (ContinuousOn.comp: h_j is continuous on Y′_j ⊆ V_j and φ_j(A′_j) ⊆ Y′_j).
8. (Definition of G.) For x ∈ ℝ^P: if x ∈ A′_j for some j (this j is unique by step 5), put G(x) := g_j(x); otherwise put G(x) := 0. [For instance G(x) := if h : ∃ j, x ∈ A′_j then g_{Nat.find h}(x) else 0.]
 (a) For every j and y ∈ Y′_j: ψ_j(y) ∈ A′_j, so G(ψ_j(y)) = h_j(φ_j(ψ_j(y))) = h_j(y). By step 2 (y ∈ V_j): G(ψ_j(y)) ∈ range Dψ_j(y) and ⟨G(ψ_j(y)), Dψ_j(y)e⟩ = DF_j(y)e for every e.
 (b) |G(x)| ≤ L for every x: if x ∈ A′_j then x = ψ_j(y) with y ∈ Y′_j and G(x) = h_j(y), and |h_j(y)| ≤ L by definition of Y′_j; otherwise G(x) = 0 and 0 ≤ L.
9. (G is Borel.) For each j, G_j := A′_j.piecewise g_j 0 is Borel by ContinuousOn.measurable_piecewise (g_j is continuous on the Borel set A′_j, and the zero map is continuous). G agrees with G_j on A′_j and vanishes on ℝ^P ∖ ⋃_k A′_k. Hence for every Borel O ⊆ ℝ^P,
 G⁻¹(O) = ⋃_j (A′_j ∩ G_j⁻¹(O)) ∪ {x ∈ ℝ^P ∖ ⋃_k A′_k : 0 ∈ O},
 a countable union of Borel sets, so G is Borel. (Equivalently: apply Measurable.find to the Borel maps G_j and the Borel predicates p_j(x) :⟺ x ∈ A′_j ∨ x ∉ ⋃_k A′_k; the resulting map is G.)
10. Steps 4(a)(b), 5, 6, 8 and 9 give all assertions. ∎

Lean realization note. The verified code below follows steps 1–10, defining Y′_j := Y_j ∩ (closure(Y_j) ∩ h_j⁻¹(closedBall(0, L))) and building G by the Measurable.find variant of step 9 (helper aux_measurable_find, stated without Nat.find to avoid clashing decidability instances); disjointness of the ψ_j(Y_j) is used exactly to identify the selected index at ψ_j(y). The algebra of step 3 is the helper aux_norm_le_of_inner.

Appendix (verified Lean realization of the proof above). The code below compiles with Lean v4.35.0-rc3, Mathlib 25730c7c and simongmt 2b36630 when placed after `import GMT.Ch07.Submission` in the frozen contract scope (inside `namespace GMT.Ch07` with the contract's `open` commands, after the contract's `noncomputable section … end`), i.e. where accepted `theorem Submission.…` declarations live in GMT/Ch07/Submission.lean. It refers to the sibling declarations Submission.dtc_bc_lc_sl_co_chart_bilipschitz, Submission.dtc_bc_lc_sl_co_chart_gradient and Submission.dtc_bc_lc_sl_co_density_gradient_bound (each with its exact frozen type, introduced by `have h_<key> : <type> := Submission.<name>` at the start of the proof). Auxiliary lemmas are named `Submission.dtc_bc_lc_sl_co_gradient_field_aux_norm_le_of_inner`, `Submission.dtc_bc_lc_sl_co_gradient_field_aux_measurable_find` to stay globally unique; they may be renamed or inlined. It was checked twice: (i) with the exact frozen sibling types as hypotheses, giving no errors and no warnings and `#print axioms` = [propext, Classical.choice, Quot.sound]; (ii) end to end, in one file containing all eight new children of dtc_bc_lc_sl_coarea in dependency order, the parent theorem proved from them, and `sorry` placeholders only for the reused accepted declarations and the parent's resolved dependencies (no warning from any child declaration). `Submission.dtc_bc_lc_sl_co_gradient_field` has exactly the frozen type of this child.

```lean
/-- Step 3 algebra: a gradient vector `v = Dψ w` with `⟨v, Dψ e⟩ = DF e` and
`|DF e| ≤ L |Dψ e|` has `|v| ≤ L`. -/
theorem Submission.dtc_bc_lc_sl_co_gradient_field_aux_norm_le_of_inner {P d : ℕ} (A : Euclid d →L[ℝ] Euclid P) (B : Euclid d →L[ℝ] ℝ)
    (L : NNReal) (v : Euclid P) (hv : v ∈ LinearMap.range (A : Euclid d →ₗ[ℝ] Euclid P))
    (hinner : ∀ e, inner ℝ v (A e) = B e) (hb : ∀ e, |B e| ≤ L * ‖A e‖) : ‖v‖ ≤ L := by
  obtain ⟨w, hw⟩ := hv
  have hw' : A w = v := hw
  have h1 := hinner w
  rw [hw', real_inner_self_eq_norm_sq] at h1
  have h2 := hb w
  rw [hw'] at h2
  have h3 : ‖v‖ ^ 2 ≤ L * ‖v‖ := by rw [h1]; exact (le_abs_self _).trans h2
  have h4 : (0 : ℝ) ≤ L := NNReal.coe_nonneg L
  nlinarith [norm_nonneg v]

/-- Measurable countable selection (via `Measurable.find`), stated without `Nat.find`. -/
theorem Submission.dtc_bc_lc_sl_co_gradient_field_aux_measurable_find {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : ℕ → α → β} {p : ℕ → α → Prop} (hf : ∀ n, Measurable (f n))
    (hp : ∀ n, MeasurableSet {x | p n x}) (h : ∀ x, ∃ n, p n x) :
    ∃ G : α → β, Measurable G ∧ ∀ x, ∃ n, p n x ∧ G x = f n x := by
  classical
  exact ⟨fun x => f (Nat.find (h x)) x, Measurable.find hf hp h,
    fun x => ⟨Nat.find (h x), Nat.find_spec (h x), rfl⟩⟩

theorem Submission.dtc_bc_lc_sl_co_gradient_field : ∀ (P d : ℕ) (M : Set (Euclid P)) (f : Euclid P → ℝ) (L : NNReal) (ψ : ℕ → Euclid d → Euclid P) (V Y : ℕ → Set (Euclid d)) (F : ℕ → Euclid d → ℝ), LipschitzWith L f → (∀ j, ContDiff ℝ 1 (ψ j)) → (∀ j, InjOn (ψ j) (V j)) → (∀ j, ∀ y ∈ V j, Injective (fderiv ℝ (ψ j) y)) → (∀ j, ContDiff ℝ 1 (F j)) → (∀ j, MeasurableSet (Y j)) → (∀ j, IsCompact (closure (Y j))) → (∀ j, closure (Y j) ⊆ V j) → (∀ j, ∀ y ∈ Y j, f (ψ j y) = F j y) → Pairwise (fun i j => Disjoint (ψ i '' Y i) (ψ j '' Y j)) → μHE[d] (M \ ⋃ j, ψ j '' Y j) = 0 → ∃ (Y' : ℕ → Set (Euclid d)) (G : Euclid P → Euclid P), (∀ j, Y' j ⊆ Y j) ∧ (∀ j, MeasurableSet (Y' j)) ∧ (∀ j, MeasurableSet (ψ j '' Y' j)) ∧ μHE[d] (M \ ⋃ j, ψ j '' Y' j) = 0 ∧ Measurable G ∧ (∀ x, ‖G x‖ ≤ L) ∧ ∀ j, ∀ y ∈ Y' j, G (ψ j y) ∈ LinearMap.range (fderiv ℝ (ψ j) y : Euclid d →ₗ[ℝ] Euclid P) ∧ ∀ e : Euclid d, inner ℝ (G (ψ j y)) (fderiv ℝ (ψ j) y e) = fderiv ℝ (F j) y e := by
  have h_chart_bilipschitz : (∀ (P d : ℕ) (ψ : Euclid d → Euclid P) (K : Set (Euclid d)), ContDiff ℝ 1 ψ → IsCompact K → InjOn ψ K → (∀ y ∈ K, Injective (fderiv ℝ ψ y)) → ∃ m Λ : ℝ, 0 < m ∧ ∀ a ∈ K, ∀ b ∈ K, m * ‖a - b‖ ≤ ‖ψ a - ψ b‖ ∧ ‖ψ a - ψ b‖ ≤ Λ * ‖a - b‖) := Submission.dtc_bc_lc_sl_co_chart_bilipschitz
  have h_chart_gradient : (∀ (P d : ℕ) (ψ : Euclid d → Euclid P) (F : Euclid d → ℝ) (V : Set (Euclid d)), ContDiff ℝ 1 ψ → ContDiff ℝ 1 F → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → ∃ h : Euclid d → Euclid P, ContinuousOn h V ∧ ∀ y ∈ V, h y ∈ LinearMap.range (fderiv ℝ ψ y : Euclid d →ₗ[ℝ] Euclid P) ∧ ∀ e : Euclid d, inner ℝ (h y) (fderiv ℝ ψ y e) = fderiv ℝ F y e) := Submission.dtc_bc_lc_sl_co_chart_gradient
  have h_density_gradient_bound : (∀ (d P : ℕ) (f : Euclid P → ℝ) (L : NNReal) (ψ : Euclid d → Euclid P) (F : Euclid d → ℝ) (Y : Set (Euclid d)) (y : Euclid d), LipschitzWith L f → y ∈ Y → DifferentiableAt ℝ ψ y → DifferentiableAt ℝ F y → (∀ z ∈ Y, f (ψ z) = F z) → Tendsto (fun r => volume (Y ∩ closedBall y r) / volume (closedBall y r)) (𝓝[>] 0) (𝓝 1) → ∀ e : Euclid d, |fderiv ℝ F y e| ≤ L * ‖fderiv ℝ ψ y e‖) := Submission.dtc_bc_lc_sl_co_density_gradient_bound
  intro P d M f L ψ V Y F hf hψ hinj hdψ hF hYm hYc hYV hfY hdisj hM
  classical
  -- Step 1: chart constants
  have hK : ∀ j, ∃ m Λ : ℝ, 0 < m ∧ ∀ a ∈ closure (Y j), ∀ b ∈ closure (Y j),
      m * ‖a - b‖ ≤ ‖ψ j a - ψ j b‖ ∧ ‖ψ j a - ψ j b‖ ≤ Λ * ‖a - b‖ := fun j =>
    h_chart_bilipschitz P d (ψ j) (closure (Y j)) (hψ j) (hYc j) ((hinj j).mono (hYV j))
      (fun y hy => hdψ j y (hYV j hy))
  choose m Λ hm hmΛ using hK
  -- Step 2: pointwise gradients
  have hH : ∀ j, ∃ h : Euclid d → Euclid P, ContinuousOn h (V j) ∧ ∀ y ∈ V j,
      h y ∈ LinearMap.range (fderiv ℝ (ψ j) y : Euclid d →ₗ[ℝ] Euclid P) ∧
        ∀ e : Euclid d, inner ℝ (h y) (fderiv ℝ (ψ j) y e) = fderiv ℝ (F j) y e := fun j =>
    h_chart_gradient P d (ψ j) (F j) (V j) (hψ j) (hF j) (hdψ j)
  choose h hhc hh using hH
  -- Step 3: the bound at density points
  have hbound : ∀ j, ∀ y ∈ Y j, Tendsto (fun r => volume (Y j ∩ closedBall y r) /
      volume (closedBall y r)) (𝓝[>] 0) (𝓝 1) → ‖h j y‖ ≤ L := by
    intro j y hy hdens
    have hyV : y ∈ V j := hYV j (subset_closure hy)
    exact Submission.dtc_bc_lc_sl_co_gradient_field_aux_norm_le_of_inner (fderiv ℝ (ψ j) y) (fderiv ℝ (F j) y) L (h j y) (hh j y hyV).1
      (hh j y hyV).2
      (h_density_gradient_bound d P f L (ψ j) (F j) (Y j) y hf hy
        ((hψ j).differentiable one_ne_zero y) ((hF j).differentiable one_ne_zero y) (hfY j) hdens)
  -- Step 4: trimmed pieces `Y' j = {y ∈ Y j : ‖h j y‖ ≤ L}`
  obtain ⟨Y', hY'⟩ : ∃ Y' : ℕ → Set (Euclid d),
      ∀ j, Y' j = Y j ∩ (closure (Y j) ∩ h j ⁻¹' closedBall 0 L) := ⟨_, fun j => rfl⟩
  have hY'mem : ∀ j y, y ∈ Y' j ↔ y ∈ Y j ∧ ‖h j y‖ ≤ L := by
    intro j y
    rw [hY' j]
    simp only [mem_inter_iff, mem_preimage, mem_closedBall_zero_iff]
    constructor
    · rintro ⟨h1, -, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨h1, subset_closure h1, h3⟩
  have hY'Y : ∀ j, Y' j ⊆ Y j := fun j y hy => ((hY'mem j y).1 hy).1
  have hY'V : ∀ j, Y' j ⊆ V j := fun j => (hY'Y j).trans (subset_closure.trans (hYV j))
  have hY'L : ∀ j, ∀ y ∈ Y' j, ‖h j y‖ ≤ L := fun j y hy => ((hY'mem j y).1 hy).2
  have hY'm : ∀ j, MeasurableSet (Y' j) := by
    intro j
    rw [hY' j]
    exact (hYm j).inter (((hhc j).mono (hYV j)).preimage_isClosed_of_isClosed isClosed_closure
      isClosed_closedBall).measurableSet
  -- 4(c): Lebesgue density theorem
  have hnull : ∀ j, volume (Y j \ Y' j) = 0 := by
    intro j
    have hae := Besicovitch.ae_tendsto_measure_inter_div (volume : Measure (Euclid d)) (Y j)
    rw [ae_restrict_iff' (hYm j), ae_iff] at hae
    refine measure_mono_null ?_ hae
    intro y hy
    simp only [Set.mem_ofPred_eq]
    intro hcon
    exact hy.2 ((hY'mem j y).2 ⟨hy.1, hbound j y hy.1 (hcon hy.1)⟩)
  -- 4(d): null images
  have hLip : ∀ j, LipschitzOnWith (Real.toNNReal (Λ j)) (ψ j) (closure (Y j)) := by
    intro j
    apply LipschitzOnWith.of_dist_le_mul
    intro a ha b hb
    rw [dist_eq_norm, dist_eq_norm]
    calc ‖ψ j a - ψ j b‖ ≤ Λ j * ‖a - b‖ := (hmΛ j a ha b hb).2
      _ ≤ (Real.toNNReal (Λ j) : ℝ) * ‖a - b‖ :=
        mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (norm_nonneg _)
  have hnullimg : ∀ j, μHE[d] (ψ j '' (Y j \ Y' j)) = 0 := by
    intro j
    have hL' : LipschitzOnWith (Real.toNNReal (Λ j)) (ψ j) (Y j \ Y' j) :=
      (hLip j).mono (Set.sdiff_subset.trans subset_closure)
    have h1 := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn d hL'
    have h2 : μHE[d] (Y j \ Y' j) = 0 := by
      rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]; exact hnull j
    rw [h2, mul_zero] at h1
    exact le_antisymm h1 zero_le
  -- Step 5: images are Borel (Lusin--Souslin)
  have hA'm : ∀ j, MeasurableSet (ψ j '' Y' j) := fun j =>
    (hY'm j).image_of_continuousOn_injOn (hψ j).continuous.continuousOn
      ((hinj j).mono (hY'V j))
  -- Step 6: null remainder
  have hrem : μHE[d] (M \ ⋃ j, ψ j '' Y' j) = 0 := by
    have hsub : M \ ⋃ j, ψ j '' Y' j ⊆ (M \ ⋃ j, ψ j '' Y j) ∪ ⋃ j, ψ j '' (Y j \ Y' j) := by
      rintro x ⟨hxM, hx⟩
      by_cases hx' : x ∈ ⋃ j, ψ j '' Y j
      · right
        obtain ⟨j, y, hy, rfl⟩ := mem_iUnion.1 hx'
        exact mem_iUnion.2 ⟨j, y, ⟨hy, fun hy' => hx (mem_iUnion.2 ⟨j, y, hy', rfl⟩)⟩, rfl⟩
      · left; exact ⟨hxM, hx'⟩
    exact measure_mono_null hsub (measure_union_null hM (measure_iUnion_null hnullimg))
  -- Step 7: inverse charts
  obtain ⟨φ, hφ⟩ : ∃ φ : ℕ → Euclid P → Euclid d, ∀ j, ∀ y ∈ Y' j, φ j (ψ j y) = y :=
    ⟨fun j => Function.invFunOn (ψ j) (Y' j), fun j y hy =>
      ((hinj j).mono (hY'V j)).leftInvOn_invFunOn hy⟩
  have hφcont : ∀ j, ContinuousOn (φ j) (ψ j '' Y' j) := by
    intro j
    have hL : LipschitzOnWith (Real.toNNReal (m j)⁻¹) (φ j) (ψ j '' Y' j) := by
      apply LipschitzOnWith.of_dist_le_mul
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [hφ j a ha, hφ j b hb, dist_eq_norm, dist_eq_norm,
        Real.coe_toNNReal _ (inv_nonneg.2 (hm j).le)]
      have hab := (hmΛ j a (subset_closure (hY'Y j ha)) b (subset_closure (hY'Y j hb))).1
      rw [inv_mul_eq_div, le_div_iff₀ (hm j)]
      linarith [mul_comm (m j) ‖a - b‖]
    exact hL.continuousOn
  have hgcont : ∀ j, ContinuousOn (fun x => h j (φ j x)) (ψ j '' Y' j) := by
    intro j
    refine ((hhc j).mono (hY'V j)).comp (hφcont j) ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [hφ j y hy]
    exact hy
  -- Step 8/9: the pieces `G_j` and the glued field `G`
  obtain ⟨Gj, hGjm, hGjin, hGjout⟩ : ∃ Gj : ℕ → Euclid P → Euclid P, (∀ j, Measurable (Gj j)) ∧
      (∀ j, ∀ y ∈ Y' j, Gj j (ψ j y) = h j y) ∧ (∀ j x, x ∉ ψ j '' Y' j → Gj j x = 0) := by
    refine ⟨fun j => (ψ j '' Y' j).piecewise (fun x => h j (φ j x)) 0,
      fun j => (hgcont j).measurable_piecewise continuousOn_const (hA'm j), ?_, ?_⟩
    · intro j y hy
      show (ψ j '' Y' j).piecewise (fun x => h j (φ j x)) 0 (ψ j y) = h j y
      rw [piecewise_eq_of_mem _ _ _ (mem_image_of_mem _ hy)]
      exact congrArg (h j) (hφ j y hy)
    · intro j x hx
      show (ψ j '' Y' j).piecewise (fun x => h j (φ j x)) 0 x = 0
      rw [piecewise_eq_of_notMem _ _ _ hx, Pi.zero_apply]
  have hGjL : ∀ j x, ‖Gj j x‖ ≤ L := by
    intro j x
    by_cases hx : x ∈ ψ j '' Y' j
    · obtain ⟨y, hy, rfl⟩ := hx
      rw [hGjin j y hy]
      exact hY'L j y hy
    · rw [hGjout j x hx, norm_zero]
      exact NNReal.coe_nonneg L
  have hex : ∀ x, ∃ n, x ∈ ψ n '' Y' n ∨ x ∉ ⋃ k, ψ k '' Y' k := by
    intro x
    by_cases hx : x ∈ ⋃ k, ψ k '' Y' k
    · obtain ⟨n, hn⟩ := mem_iUnion.1 hx
      exact ⟨n, Or.inl hn⟩
    · exact ⟨0, Or.inr hx⟩
  obtain ⟨G, hGm, hG⟩ := Submission.dtc_bc_lc_sl_co_gradient_field_aux_measurable_find (p := fun n x => x ∈ ψ n '' Y' n ∨ x ∉ ⋃ k, ψ k '' Y' k)
    hGjm (fun n => (hA'm n).union (MeasurableSet.iUnion hA'm).compl) hex
  refine ⟨Y', G, hY'Y, hY'm, hA'm, hrem, hGm, ?_, ?_⟩
  · intro x
    obtain ⟨n, -, hn⟩ := hG x
    rw [hn]
    exact hGjL n x
  · intro j y hy
    obtain ⟨n, hpn, hn⟩ := hG (ψ j y)
    have hmem : ψ j y ∈ ψ j '' Y' j := mem_image_of_mem _ hy
    have hnj : n = j := by
      rcases hpn with hpn | hpn
      · by_contra hne
        exact Set.disjoint_left.1 (hdisj hne) (Set.image_mono (hY'Y n) hpn)
          (Set.image_mono (hY'Y j) hmem)
      · exact absurd (mem_iUnion.2 ⟨j, hmem⟩) hpn
    rw [hn, hnj, hGjin j y hy]
    exact hh j y (hY'V j hy)
```

## Key steps

1. chart_bilipschitz on K_j = closure(Y_j): m_j > 0 and Λ_j bounding ψ_j from below and above.
2. chart_gradient: h_j continuous on V_j with h_j(y) ∈ range Dψ_j(y) and ⟨h_j(y), Dψ_j(y)e⟩ = DF_j(y)e.
3. density_gradient_bound at Lebesgue density points y ∈ Y_j gives |h_j(y)| ≤ L.
4. Y′_j := {y ∈ Y_j : |h_j(y)| ≤ L} is Borel and L^d(Y_j ∖ Y′_j) = 0 (density theorem), so H^d(ψ_j(Y_j ∖ Y′_j)) = 0 (Lipschitz image) and M ∖ ⋃_j ψ_j(Y′_j) is null.
5. ψ_j(Y′_j) Borel (Lusin–Souslin) and disjoint; the inverse chart is continuous on it (lower bound).
6. G := h_j ∘ ψ_j⁻¹ on ψ_j(Y′_j), 0 elsewhere: Borel (countable piecewise of ContinuousOn pieces), |G| ≤ L, gradient identities on Y′_j.
7. Verified Lean realization supplied in the appendix (compiles warning-free; standard axioms only).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db1, mathlib 25730c7c); diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); cat .lake/packages manifest (simongmt 2b36630)`
- `python3 -I scans of dag.json (1523 nodes): slicing-a1 subtree and statuses; frozen types of chart_pieces, chart_coarea, eilenberg, im_calculus; nodes matching bi-Lipschitz|immersion|density point|Lebesgue density|blowUpMap|tangential gradient|co-area|Injective (fderiv; the dor_lmb...slicing-a1.slice_family-a1 subtree (lipschitz_chart_pieces, density_directions, piece_coarea, piece_slice_tangent, tangential_gradient)`
- `git show <commit>:GMT/Ch07/Submission.lean and whitespace-normalised type comparison for cmc_imRep_locality_restrict_sub (2af75d6), codim1_rdo_c1cov_local_lower_lipschitz (12e74ed), rsd_tendsto_closedBall_density_of_approxTangent (dbef2c1), dor_lmb_approx_tangent_locality (53d4678): all MATCH; nodes/*/accepted-candidate.json comparator_passed = true`
- `grep -c dtc_bc_lc_sl_co_ dag.json (0); git log --all -S 'dtc_bc_lc_sl_co_' over 6410 refs (no match); survey of 400 accepted candidate commits: added declarations are theorem Submission.*`
- `grep in the snapshot Mathlib: Besicovitch.ae_tendsto_measure_inter_div, MeasurableSet.image_of_continuousOn_injOn, LipschitzOnWith.hausdorffMeasure_image_le, Convex.norm_image_sub_le_of_norm_fderiv_le, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_smul, Measure.addHaar_closedBall, measure_inter_add_sdiff, lintegral_iUnion, lintegral_tsum, ENNReal.Tendsto.sub, ContinuousOn.measurable_piecewise, Measurable.find, ContinuousOn.preimage_isClosed_of_isClosed, InjOn.leftInvOn_invFunOn, ae_restrict_iUnion_iff, ae_restrict_union_iff, ae_restrict_iff', ae_lt_top', NormedRing.inverse_continuousAt, ContinuousLinearMap.adjoint_inner_left, toDual_symm_apply, IsCompact.exists_bound_of_continuousOn, LinearMap.isUnit_iff_ker_eq_bot`
- `grep in SimonGMT: Chapter03/Rectifiable.lean (CountablyRectifiable, blowUpMap, HasApproximateTangentSpaceAt, .unique, countablyRectifiable_iUnion, countablyRectifiable_of_measure_zero, CountablyRectifiable.mono); Chapter02/Lipschitz.lean (euclideanHausdorffMeasure_image_le_of_lipschitzOn); Chapter04/TangentDensity.lean; no nonlinear co-area, tangential gradient or slicing declarations`
- `sed book/chapter-03.txt lines 300-460 (Remark 1.8, 2.1-2.10) and book/chapter-06.txt lines 1140-1200 (Lemma 4.1)`
- `Lean checks through a persistent LSP worker: #check availability file under import GMT.Ch07.Submission; /tmp/coarea_split/v2/ch/Challenge_<key>.lean (11 modules from gmt-compare.py child_modules, contract mode); /tmp/coarea_split/asm/Assembly3.lean; /tmp/coarea_split/agents/{A,B,C,D,E} hypothesis-form proofs; /tmp/coarea_split/e2e2/E2E_from_json.lean and E2E_solution.lean (end to end, comparator form)`
- `sed /runtime/flows/gmt-claude-3b0b44b19c6a/_recursive_lean/runtime.py (_decompose depth gate, _dependency_problem, _existing_lean_name_problem) and prompts.py (DECOMPOSITION_AUDIT, RLCR_LEAN_TASK, LEAN_AUDIT, SPECULATIVE_PARENT_TASK)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-772be56655/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-09907e06c7/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-im-calculus-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-unweighted-density-one-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-ec0e4b9204/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-3b0b44b19c6a/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-3b0b44b19c6a/_recursive_lean/prompts.py`
- `/tmp/coarea_split/v2/ch`
- `/tmp/coarea_split/asm/Assembly3.lean`
- `/tmp/coarea_split/e2e2/E2E_from_json.lean`
- `/tmp/coarea_split/e2e2/E2E_solution.lean`

Neither the pinned SimonGMT library nor Mathlib has a nonlinear co-area formula, a tangential gradient of Lipschitz functions on rectifiable sets, or slicing. They do supply every tool cited in the child proofs: the Lebesgue density theorem, Lusin–Souslin, the Lipschitz image bound, the mean value inequality, Haar scaling, adjoints, continuity of Ring.inverse, and the countable-rectifiability lemmas. Three comparator-accepted DAG declarations are reused with identical types: cmc_imRep_locality_restrict_sub, codim1_rdo_c1cov_local_lower_lipschitz and rsd_tendsto_closedBall_density_of_approxTangent. dor_lmbsf_density_directions (accepted) overlaps one step of density_gradient_bound but is not needed. The eight new names are unreserved. All 11 types elaborate in the exact comparator challenge modules. Every new child is proved in Lean exactly as typed, both in hypothesis form and end to end. The exact frozen parent type is proved from the children and its resolved dependencies, using only propext, Classical.choice and Quot.sound.
