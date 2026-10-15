# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.truncated_compactness-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.truncated_compactness-a1.weak_compactness-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, Lemma 2.15 and the remark after Theorem 3.11 (chapter-06.txt lines 318–333 and 889–891): currents with locally bounded mass have a weakly convergent subsequence. Simon derives 2.15 from the Banach–Alaoglu theorem in the spaces M_n(W) (after representing the T_q by measures, 2.7); here, for U = ℝ^P and convergence on smooth test forms (2.13), the same conclusion is proved directly by a separability and diagonal argument, so no representation theorem is needed.
Siblings: eval_mass_bound (E1); covector_equiv (NE).
Notation: 𝒟ⁿ := TestFormOn ℝ^P n; |α| := covectorEuclideanNorm α; B_R := ball(0, R); c_R := (sup_j M_{B_R}(T_j)).toReal ∈ [0, ∞) for R ∈ ℝ (the supremum is finite by hypothesis). By (NE) fix d ∈ ℕ and a continuous linear equivalence c from n-covectors (Mathlib's operator-norm space) onto ℝ^d with |α| = ‖c(α)‖ for all α, and let κ := ‖c‖ ≥ 0 (operator norm), so |α| ≤ κ‖α‖.

1. (Uniform evaluation bound.) If R ∈ ℝ, ω ∈ 𝒟ⁿ, tsupport ω ⊆ B_R and |ω(x)| ≤ r for all x, then |T_j(ω)| ≤ r·c_R for every j. Indeed M_{B_R}(T_j) ≤ sup_j M_{B_R}(T_j) < ∞, so (E1) (with U = ℝ^P, W = B_R) gives |T_j(ω)| ≤ r·(M_{B_R}(T_j)).toReal, and (M_{B_R}(T_j)).toReal ≤ c_R because toReal is monotone on finite values; r ≥ |ω(0)| ≥ 0.

2. (Test forms are bounded and supported in balls.) Let ω ∈ 𝒟ⁿ. Its tsupport is compact, hence bounded, so tsupport ω ⊆ B_R for some R ∈ ℕ. The map x ↦ c(ω(x)) is continuous (ω is smooth, c continuous) with compact support (c(0) = 0), hence bounded: there is r with |ω(x)| = ‖c(ω(x))‖ ≤ r for all x. By step 1, |T_j(ω)| ≤ B_ω := r·c_R for every j.

3. (Separability.) Fix R ∈ ℕ, let 𝒯_R := {ω ∈ 𝒟ⁿ : tsupport ω ⊆ B_R} and K_R := closedBall(0, R) (compact). Define ι : 𝒟ⁿ → C(K_R, ℝ^d) by ι(ω)(x) := c(ω(x)). The space C(K_R, ℝ^d) is second countable (Mathlib ContinuousMap.instSecondCountableTopology in Mathlib.Topology.ContinuousMap.SecondCountableSpace: K_R is second countable and locally compact, ℝ^d is second countable), and on the compact domain K_R its topology is that of the sup metric dist(f, g) = sup_{x∈K_R} ‖f(x) − g(x)‖ (ContinuousMap.instMetricSpace). So it is separable, its subset ι(𝒯_R) is separable (IsSeparable.of_separableSpace), and since the space is metrizable there is a countable t ⊆ ι(𝒯_R) with ι(𝒯_R) ⊆ closure t (IsSeparable.exists_countable_dense_subset). For each g ∈ t choose ω_g ∈ 𝒯_R with ι(ω_g) = g, and let D_R := {ω_g : g ∈ t}, a countable subset of 𝒯_R.
 Claim: for every ω ∈ 𝒯_R and ε > 0 there is ω′ ∈ D_R with |ω(x) − ω′(x)| < ε for all x ∈ ℝ^P. Since ι(ω) ∈ closure t, there is g ∈ t with dist(ι(ω), g) < ε (Metric.mem_closure_iff); put ω′ := ω_g. For x ∈ K_R: |ω(x) − ω′(x)| = ‖c(ω(x)) − c(ω′(x))‖ = dist(ι(ω)(x), ι(ω′)(x)) ≤ dist(ι(ω), ι(ω′)) < ε (ContinuousMap.dist_apply_le_dist). For x ∉ K_R: x lies outside tsupport ω and tsupport ω′ (both ⊆ B_R ⊆ K_R), so ω(x) = ω′(x) = 0 and |0| = 0 < ε.

4. (Diagonal subsequence.) D := ⋃_{R∈ℕ} D_R is countable. For j ∈ ℕ put X_j(ω) := T_j(ω) (ω ∈ D), an element of ℝ^D. By step 2 every X_j lies in Π_{ω∈D}[−B_ω, B_ω], which is compact by Tychonoff's theorem (isCompact_univ_pi), and ℝ^D (product topology) is first countable because D is countable. Hence (IsCompact.tendsto_subseq) there are a ∈ ℝ^D and a strictly increasing φ : ℕ → ℕ with X_{φ(i)} → a, i.e. T_{φ(i)}(ω) → a(ω) for every ω ∈ D (tendsto_pi_nhds). (This is the Cantor diagonal argument.)

5. (Convergence on every test form.) Let ω ∈ 𝒟ⁿ and ε > 0. Pick R ∈ ℕ with ω ∈ 𝒯_R (step 2) and put δ := ε/(4(c_R + 1)) > 0, so δ·c_R ≤ ε/4. By step 3 pick ω′ ∈ D_R ⊆ D with |ω(x) − ω′(x)| < δ for all x. The test form ω − ω′ has tsupport ⊆ tsupport ω ∪ tsupport ω′ ⊆ B_R (tsupport_sub), so by step 1 and linearity, |T_j(ω) − T_j(ω′)| = |T_j(ω − ω′)| ≤ δ·c_R ≤ ε/4 for every j. As (T_{φ(i)}(ω′))_i converges (step 4), it is Cauchy: there is N with |T_{φ(i)}(ω′) − T_{φ(i′)}(ω′)| < ε/2 for i, i′ ≥ N. By the triangle inequality |T_{φ(i)}(ω) − T_{φ(i′)}(ω)| < ε/4 + ε/2 + ε/4 = ε for i, i′ ≥ N. So (T_{φ(i)}(ω))_i is a Cauchy sequence of reals and converges (cauchySeq_tendsto_of_complete); let ℓ(ω) be its limit.

6. (Linearity and bound.) By uniqueness of limits and the linearity of each T_{φ(i)}, ℓ(ω + η) = ℓ(ω) + ℓ(η) and ℓ(tω) = t·ℓ(ω); thus ℓ : 𝒟ⁿ → ℝ is ℝ-linear. Passing to the limit in step 1 (|T_{φ(i)}(ω)| → |ℓ(ω)|, le_of_tendsto'): if tsupport ω ⊆ B_R and |ω(x)| ≤ r for all x, then |ℓ(ω)| ≤ r·c_R.

7. (Continuity.) Let ω_q → 0 in 𝒟ⁿ (TestFormOnConverges): there is a compact K with tsupport ω_q ⊆ K for all q, and iteratedFDeriv ℝ k ω_q → 0 uniformly on K for every k. Choose R ∈ ℝ with K ⊆ B_R (K is bounded). For k = 0, ‖iteratedFDeriv ℝ 0 f x‖ = ‖f(x)‖ (norm_iteratedFDeriv_zero) and iteratedFDeriv ℝ 0 of the zero form vanishes, so sup_{x∈K} ‖ω_q(x)‖ → 0 (operator norm). Given ε > 0, let η := ε/(2(κ + 1)(c_R + 1)) > 0 and q₀ such that ‖ω_q(x)‖ < η for all x ∈ K and q ≥ q₀. Then for q ≥ q₀ and every x: if x ∈ K, |ω_q(x)| = ‖c(ω_q(x))‖ ≤ κ‖ω_q(x)‖ ≤ κη; if x ∉ K, then x ∉ tsupport ω_q, so ω_q(x) = 0 (image_eq_zero_of_notMem_tsupport). By step 6, |ℓ(ω_q)| ≤ κη·c_R ≤ η(κ + 1)(c_R + 1) = ε/2 < ε. Hence ℓ(ω_q) → 0.

8. (Conclusion.) By steps 6 and 7, ℓ together with this continuity property is a current C ∈ 𝒟_n(ℝ^P) (GeometricCurrentOn: a linear functional with the sequential continuity of step 7), and by step 5, T_{φ(i)}(ω) → C(ω) for every ω ∈ 𝒟ⁿ, i.e. WeaklyConvergesOn (i ↦ T_{φ(i)}) C, with φ strictly increasing. ∎

Appendix (verified Lean realization of the numbered proof above; not part of the proof). Compiled in this decomposition session with Lean v4.35.0-rc3, Mathlib 25730c7c and SimonGMT 2b366308 after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the frozen contract's `open` commands (after its `noncomputable section ... end`). The file must import `Mathlib.Topology.ContinuousMap.SecondCountableSpace` (add the import line to the Lean target). The sibling declarations are used through their accepted names `Submission.<lean_name>`; with them as hypotheses `#print axioms` reports only propext, Classical.choice and Quot.sound.

```lean
theorem Submission.dimred_mbl_tc_weak_compactness : ∀ (P n : ℕ) (T : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) n), (∀ R : ℝ, ⨆ j, (T j).massOn (ball (0 : Euclid P) R) < ∞) → ∃ (φ : ℕ → ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n), StrictMono φ ∧ WeaklyConvergesOn (fun i => T (φ i)) C := by
  have hE1 := Submission.cmr_abs_apply_le_massOn
  have hNE := Submission.cmr_covector_euclidean_equiv
  intro P n T hT
  obtain ⟨d, c, hc⟩ := hNE P n
  -- c_R := (sup_j M_{B_R}(T_j)).toReal
  let cR : ℝ → ℝ := fun R => (⨆ j, (T j).massOn (ball (0 : Euclid P) R)).toReal
  -- (a) uniform evaluation bound (E1)
  have hev : ∀ (R : ℝ) (ω : TestFormOn (univ : Set (Euclid P)) n) (r : ℝ),
      tsupport (ω : DifferentialForm (Euclid P) n) ⊆ ball 0 R →
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ r) →
      ∀ j, |T j ω| ≤ r * cR R := by
    intro R ω r hsupp hr j
    have hle : (T j).massOn (ball 0 R) ≤ ⨆ j, (T j).massOn (ball (0 : Euclid P) R) :=
      le_iSup (fun j => (T j).massOn (ball (0 : Euclid P) R)) j
    have hne : (T j).massOn (ball 0 R) ≠ ∞ := ne_top_of_le_ne_top (hT R).ne hle
    have h1 := hE1 P n univ (ball 0 R) (T j) ω r hne hsupp hr
    have hr0 : 0 ≤ r := (covectorEuclideanNorm_nonneg _).trans (hr 0)
    exact h1.trans (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (hT R).ne hle) hr0)
  -- every test form has tsupport in a ball and bounded coefficient norm
  have hsupp : ∀ ω : TestFormOn (univ : Set (Euclid P)) n, ∃ R : ℕ,
      tsupport (ω : DifferentialForm (Euclid P) n) ⊆ ball 0 R := by
    intro ω
    obtain ⟨r, hr⟩ := ω.property.1.2.isCompact.isBounded.subset_ball (0 : Euclid P)
    obtain ⟨R, hR⟩ := exists_nat_gt r
    exact ⟨R, hr.trans (ball_subset_ball hR.le)⟩
  have hbdd : ∀ ω : TestFormOn (univ : Set (Euclid P)) n, ∃ r : ℝ,
      ∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ r := by
    intro ω
    have hcont : Continuous (fun x => c ((ω : DifferentialForm (Euclid P) n) x)) :=
      c.continuous.comp ω.property.1.1.continuous
    have hcs : HasCompactSupport (fun x => c ((ω : DifferentialForm (Euclid P) n) x)) :=
      ω.property.1.2.comp_left (map_zero c)
    obtain ⟨r, hr⟩ := hcont.bounded_above_of_compact_support hcs
    exact ⟨r, fun x => by rw [hc]; exact hr x⟩
  -- (b) separability of the test forms supported in ball 0 R
  have hsep : ∀ R : ℕ, ∃ D : Set (TestFormOn (univ : Set (Euclid P)) n), D.Countable ∧
      (∀ ω ∈ D, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ ball 0 R) ∧
      ∀ ω : TestFormOn (univ : Set (Euclid P)) n,
        tsupport (ω : DifferentialForm (Euclid P) n) ⊆ ball 0 R →
        ∀ ε > 0, ∃ ω' ∈ D, ∀ x, covectorEuclideanNorm
          ((ω : DifferentialForm (Euclid P) n) x - (ω' : DifferentialForm (Euclid P) n) x) < ε := by
    intro R
    let ι : TestFormOn (univ : Set (Euclid P)) n →
        C(closedBall (0 : Euclid P) R, EuclideanSpace ℝ (Fin d)) := fun ω =>
      ⟨fun x => c ((ω : DifferentialForm (Euclid P) n) x),
        (c.continuous.comp ω.property.1.1.continuous).comp continuous_subtype_val⟩
    let 𝒯 : Set (TestFormOn (univ : Set (Euclid P)) n) :=
      {ω | tsupport (ω : DifferentialForm (Euclid P) n) ⊆ ball 0 R}
    obtain ⟨t, hts, htc, hdense⟩ :=
      (TopologicalSpace.IsSeparable.of_separableSpace (ι '' 𝒯)).exists_countable_dense_subset
    have hpre : ∀ g ∈ t, ∃ ω ∈ 𝒯, ι ω = g := fun g hg => hts hg
    choose! pre hpre𝒯 hpreι using hpre
    refine ⟨pre '' t, htc.image _, ?_, ?_⟩
    · rintro _ ⟨g, hg, rfl⟩; exact hpre𝒯 g hg
    · intro ω hω ε hε
      have hmem : ι ω ∈ closure t := hdense ⟨ω, hω, rfl⟩
      obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.1 hmem ε hε
      refine ⟨pre g, ⟨g, hg, rfl⟩, fun x => ?_⟩
      by_cases hx : x ∈ closedBall (0 : Euclid P) R
      · have h1 := ContinuousMap.dist_apply_le_dist (f := ι ω) (g := ι (pre g)) ⟨x, hx⟩
        rw [← hpreι g hg] at hdist
        rw [hc, map_sub, ← dist_eq_norm]
        exact lt_of_le_of_lt h1 hdist
      · have h1 : (ω : DifferentialForm (Euclid P) n) x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h => hx (ball_subset_closedBall (hω h)))
        have h2 : ((pre g : TestFormOn (univ : Set (Euclid P)) n) :
            DifferentialForm (Euclid P) n) x = 0 :=
          image_eq_zero_of_notMem_tsupport
            (fun h => hx (ball_subset_closedBall (hpre𝒯 g hg h)))
        rw [h1, h2, sub_zero, covectorEuclideanNorm_zero]; exact hε
  choose D hDc hDsupp hDdense using hsep
  -- (c) diagonal subsequence on the countable set ⋃ D_R
  let Dall : Set (TestFormOn (univ : Set (Euclid P)) n) := ⋃ R : ℕ, D R
  have hDall : Dall.Countable := countable_iUnion hDc
  have : Countable Dall := hDall.to_subtype
  have hbound : ∀ ω : TestFormOn (univ : Set (Euclid P)) n, ∃ B : ℝ, ∀ j, |T j ω| ≤ B := by
    intro ω
    obtain ⟨R, hR⟩ := hsupp ω
    obtain ⟨r, hr⟩ := hbdd ω
    exact ⟨r * cR R, hev R ω r hR hr⟩
  choose B hB using hbound
  let X : ℕ → (Dall → ℝ) := fun j ω => T j ω
  have hXmem : ∀ j, X j ∈ Set.pi univ (fun ω : Dall => Icc (-B ω) (B ω)) := by
    intro j ω _
    exact abs_le.1 (hB ω j)
  obtain ⟨a, -, φ, hφ, hlimD⟩ :=
    (isCompact_univ_pi (fun ω : Dall => isCompact_Icc)).tendsto_subseq hXmem
  have hconvD : ∀ ω ∈ Dall, ∃ l, Tendsto (fun i => T (φ i) ω) atTop (𝓝 l) := by
    intro ω hω
    exact ⟨a ⟨ω, hω⟩, tendsto_pi_nhds.1 hlimD ⟨ω, hω⟩⟩
  -- (d) Cauchy property on every test form
  have hconv : ∀ ω : TestFormOn (univ : Set (Euclid P)) n,
      ∃ l, Tendsto (fun i => T (φ i) ω) atTop (𝓝 l) := by
    intro ω
    apply cauchySeq_tendsto_of_complete
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨R, hR⟩ := hsupp ω
    have hM0 : 0 ≤ cR R := ENNReal.toReal_nonneg
    set δ : ℝ := ε / (4 * (cR R + 1)) with hδ
    have hδpos : 0 < δ := by positivity
    have hδM : δ * cR R ≤ ε / 4 := by
      have : δ * (cR R + 1) = ε / 4 := by rw [hδ]; field_simp
      nlinarith
    obtain ⟨ω', hω'D, hω'⟩ := hDdense R ω hR δ hδpos
    obtain ⟨l, hl⟩ := hconvD ω' (mem_iUnion.2 ⟨R, hω'D⟩)
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hl.cauchySeq (ε / 2) (by positivity)
    refine ⟨N, fun i hi i' hi' => ?_⟩
    have hdiff : ∀ j, |T j ω - T j ω'| ≤ δ * cR R := by
      intro j
      rw [← map_sub]
      apply hev R (ω - ω') δ
      · exact (tsupport_sub _ _).trans (union_subset hR (hDsupp R ω' hω'D))
      · intro x; exact (hω' x).le
    have h1 := abs_le.1 (hdiff (φ i))
    have h2 := abs_le.1 (hdiff (φ i'))
    have h3 := hN i hi i' hi'
    rw [Real.dist_eq] at h3 ⊢
    have h3' := abs_lt.1 h3
    rw [abs_lt]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3'.1, h3'.2]
  -- (e) the limit current
  choose l hl using hconv
  have hadd : ∀ ω η, l (ω + η) = l ω + l η := fun ω η =>
    tendsto_nhds_unique (hl (ω + η)) (by simpa [map_add] using (hl ω).add (hl η))
  have hsmul : ∀ (r : ℝ) ω, l (r • ω) = r * l ω := fun r ω =>
    tendsto_nhds_unique (hl (r • ω)) (by simpa [map_smul] using (hl ω).const_mul r)
  let L : TestFormOn (univ : Set (Euclid P)) n →ₗ[ℝ] ℝ :=
    { toFun := l
      map_add' := hadd
      map_smul' := fun r ω => by simp [hsmul] }
  have hLbound : ∀ (R : ℝ) (ω : TestFormOn (univ : Set (Euclid P)) n) (r : ℝ),
      tsupport (ω : DifferentialForm (Euclid P) n) ⊆ ball 0 R →
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ r) →
      |l ω| ≤ r * cR R := fun R ω r hs hr =>
    le_of_tendsto' (hl ω).abs (fun i => hev R ω r hs hr (φ i))
  have hcont : ∀ ωs : ℕ → TestFormOn (univ : Set (Euclid P)) n, TestFormOnConverges ωs 0 →
      Tendsto (fun j => L (ωs j)) atTop (𝓝 0) := by
    intro ωs hωs
    obtain ⟨K, hK, -, hKsupp, -, hunif⟩ := hωs
    obtain ⟨r, hr⟩ := hK.isBounded.subset_ball (0 : Euclid P)
    have h0 := Metric.tendstoUniformlyOn_iff.1 (hunif 0)
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨cn, hcn0, hcnle⟩ : ∃ cn : ℝ, 0 ≤ cn ∧ ∀ α : Covector (Euclid P) n, ‖c α‖ ≤ cn * ‖α‖ :=
      ⟨‖(c : Covector (Euclid P) n →L[ℝ] EuclideanSpace ℝ (Fin d))‖,
        (c : Covector (Euclid P) n →L[ℝ] EuclideanSpace ℝ (Fin d)).opNorm_nonneg,
        fun α => (c : Covector (Euclid P) n →L[ℝ] EuclideanSpace ℝ (Fin d)).le_opNorm α⟩
    have hM0 : 0 ≤ cR r := ENNReal.toReal_nonneg
    set η : ℝ := ε / (2 * ((cn + 1) * (cR r + 1))) with hη
    have hηpos : 0 < η := by positivity
    obtain ⟨N, hN⟩ := eventually_atTop.1 (h0 η hηpos)
    refine ⟨N, fun j hj => ?_⟩
    have hpt : ∀ x, covectorEuclideanNorm ((ωs j : DifferentialForm (Euclid P) n) x) ≤ cn * η := by
      intro x
      by_cases hx : x ∈ K
      · have h1 := hN j hj x hx
        have e0 : iteratedFDeriv ℝ 0
            ((0 : TestFormOn (univ : Set (Euclid P)) n) : DifferentialForm (Euclid P) n) x = 0 := by
          rw [← norm_eq_zero, norm_iteratedFDeriv_zero]; simp
        rw [e0, dist_zero_left, norm_iteratedFDeriv_zero] at h1
        rw [hc]
        calc ‖c ((ωs j : DifferentialForm (Euclid P) n) x)‖
            ≤ cn * ‖(ωs j : DifferentialForm (Euclid P) n) x‖ := hcnle _
          _ ≤ cn * η := mul_le_mul_of_nonneg_left h1.le hcn0
      · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hKsupp j h)),
          covectorEuclideanNorm_zero]
        positivity
    have hb := hLbound r (ωs j) (cn * η) ((hKsupp j).trans hr) hpt
    rw [Real.dist_eq, sub_zero]
    show |l (ωs j)| < ε
    have hkey : cn * η * cR r ≤ ε / 2 := by
      have h1 : cn * cR r ≤ (cn + 1) * (cR r + 1) := by nlinarith
      have h2 : η * ((cn + 1) * (cR r + 1)) = ε / 2 := by rw [hη]; field_simp
      nlinarith
    linarith
  exact ⟨φ, ⟨L, hcont⟩, hφ, fun ω => hl ω⟩
```

## Key steps

1. (E1): |T_j(ω)| ≤ r·c_R whenever tsupport ω ⊆ B_R and |ω| ≤ r, with c_R := (sup_j M_{B_R}(T_j)).toReal.
2. Via the isometry c of (NE), test forms supported in B_R embed in the second countable metric space C(closedBall(0, R), ℝ^d); a countable D_R is sup-norm dense in them.
3. Tychonoff on Π_{ω∈D}[−B_ω, B_ω] (D := ⋃ D_R countable, so ℝ^D is first countable) gives φ with T_{φ(i)}(ω) convergent for ω ∈ D.
4. Density plus the uniform bound make (T_{φ(i)}(ω))_i Cauchy for every test form ω; the limit ℓ is linear with |ℓ(ω)| ≤ r·c_R.
5. TestFormOnConverges to 0 gives uniform convergence of ω_q (k = 0), hence ℓ(ω_q) → 0: ℓ is a current C with T_{φ(i)} ⇀ C.

## Reference use

### local-project

Queries:
- `cat RUN/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `python3 scans of RUN/dag.json: selected node, parent root.dimension_reduction_results-a1.moving_blowups-a1 and its children, dependency types (dor_imrep_massOn_eq_measure_and_support, dimred_mbl_current_foundations, dimred_mbl_slice_mass_bounds, dimred_mbl_closure_and_boundary_rectifiability), accepted declarations mentioning massOn/IMRep/compact/diagonal/separab, collisions for dimred_mbl_tc_*`
- `rg -n 'Banach|Alaoglu|SecondCountableTopology|IsSeparable|diagonal|extraction' lake-packages/simongmt/Poincare/SimonGMT/Chapter06 (no match); rg -n 'WeaklyConvergesOn|Banach' SNAPSHOT/project --glob '*.lean'`
- `rg -n 'instSecondCountableTopology|theorem extraction_forall_of_eventually|IsSeparable.exists_countable_dense_subset|Filter.EventuallyEq.extDeriv_eq' SNAPSHOT/mathlib/Mathlib; grep of setLIntegral_congr_fun, lipschitzWith_one_norm, ContDiffBump API, tsupport_sub, norm_iteratedFDeriv_zero`
- `sed -n on book/chapter-06.txt lines 284–333 (2.9, 2.13–2.15), 755–767 (3.2), 875–895 (3.11), 1330–1380 (4.6–4.10)`
- `grep -n _existing_lean_name_problem _overlay_accepted_children _accepted_checkpoint ensure in /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py and store.py; contract_scope in verifier/gmt-compare.py`
- `lake env lean on Types/Final.lean (7 child types), Assembly.lean (conditional parent), LT.lean, TR.lean, WC.lean (child proofs from sibling types), SubForm.lean and SubParent.lean (Submission-form compile), all with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-truncated-compactness-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-eva-463e096c91/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-cov-64249b6f60/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-im-calculus-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1-imrep-1bd5f15878/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Metrizable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/tmp/tc-decomp-x7k2/lean/Assembly.lean`
- `/tmp/tc-decomp-x7k2/lean/TR.lean`
- `/tmp/tc-decomp-x7k2/lean/WC.lean`
- `/tmp/tc-decomp-x7k2/lean/LT.lean`

Pins match: HEAD b4d606d, Mathlib 25730c7c, SimonGMT 2b366308, and Submission.lean is byte-identical to Contract.lean. Neither the pinned libraries nor any accepted DAG node proves weak compactness of currents. SimonGMT Chapter06 has no match. The project snapshot states Simon 2.15 only as the unproved Ch06 contract conjunct CompactnessUnderMassBounds (GMT/Ch06/Contract.lean:194–205), a different problem. So weak_compactness is a new child. Its Lean route exists in Mathlib: ContinuousMap.instSecondCountableTopology (separate import), IsSeparable.exists_countable_dense_subset, IsCompact.tendsto_subseq on a countable product, and norm_iteratedFDeriv_zero. The cut-off uses ContDiffBump and Filter.EventuallyEq.extDeriv_eq. Step 1 uses Filter.extraction_forall_of_eventually. Four accepted declarations are reused with identical frozen types: cmr_abs_apply_le_massOn, cmr_covector_euclidean_equiv, cmc_imRep_locality_restrict_sub and lcmp_imRep_measure_restrict. The new names dimred_mbl_tc_* collide with nothing. All child types elaborate. The conditional assembly proves the exact parent type, and each new child is proved in Lean from its sibling types. All of these depend only on propext, Classical.choice and Quot.sound.
