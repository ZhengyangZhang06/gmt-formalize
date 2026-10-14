# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.lipschitz_approx-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.lipschitz_approx-a1.local_approx-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 3–7 of the parent proof carried out for a single graph chart (the parent's L = 1 case): coordinate function (step 3), mollification (step 4), ambient approximant β·g_k∘pr(· − p) (step 5), uniform convergence (step 6), tangential derivatives, the pointwise bound and the transfer of the L² error to the chart ball (steps 7a–7d). Sibling children used: graph_chart, tangent_uniqueness, lipschitz_transfer, mollify, rademacher, locally_closed. Notation: P_x := starProjection of span(tangentSpace M x), e_j := EuclideanSpace.single j 1, H^m = μHE[m], L^m = volume, B_s := open ball, cthickening/thickening as in Mathlib.

1. (The neighbourhood W.) Child graph_chart at p gives pr, G, r, W, Λ: W open, p ∈ W, ‖pr‖ ≤ 1, G C¹ and Λ-Lipschitz on B_r(0), M ∩ W = G(B_r(0)), pr(G(a) − p) = a and pr∘DG(a) = id and tangentSpace M (G a) = range DG(a) for a ∈ B_r(0). This W is the asserted open neighbourhood of p. Consequences: G(a) ∈ M ∩ W for a ∈ B_r(0); every x ∈ M ∩ W equals G(a) with a = pr(x − p) ∈ B_r(0). M is Borel (locally_closed). Now fix ζ, locally Lipschitz on M, and a compact C ⊆ M ∩ W with ζ = 0 on M \ C.
2. (Parameter sets.) S := {pr(x − p) : x ∈ C} is compact and S ⊆ B_r(0) (step 1). Choose δ₀ > 0 with cthickening δ₀ S ⊆ B_r(0) (IsCompact.exists_cthickening_subset_open), put δ := δ₀/2 and T := cthickening δ S. T is compact and S ⊆ T ⊆ B_r(0).
3. (The coordinate function.) g(a) := ζ(G(a)) for a ∈ B_r(0), g(a) := 0 otherwise.
 (a) g = 0 off S: if a ∈ B_r(0) \ S then G(a) ∈ M and G(a) ∉ C (otherwise a = pr(G(a) − p) ∈ S), so g(a) = ζ(G(a)) = 0.
 (b) ζ∘G is locally Lipschitz on B_r(0): for a in the ball, ζ is K-Lipschitz on some t ∈ 𝓝[M] G(a); since G is continuous on the ball and G(B_r(0)) ⊆ M, the set G⁻¹(t) ∩ B_r(0) belongs to 𝓝[B_r(0)] a, and ζ∘G is KΛ-Lipschitz on it. Hence ζ∘G is K₁-Lipschitz on the compact set T ⊆ B_r(0) for some K₁ (LocallyLipschitzOn.exists_lipschitzOnWith_of_compact), and |ζ∘G| ≤ B on T for some B (continuity on a compact set).
 (c) g is Lipschitz on ℝ^m with constant max(K₁, B/δ): if a, b ∈ T, |g(a) − g(b)| = |ζ(G(a)) − ζ(G(b))| ≤ K₁|a − b|. If neither a nor b lies in S, both values are 0. If a ∈ S and b ∉ T, then |a − b| > δ (otherwise b ∈ cthickening δ S), g(b) = 0 and |g(a) − g(b)| = |g(a)| ≤ B ≤ (B/δ)|a − b|; the case b ∈ S, a ∉ T is symmetric. These cases exhaust all pairs.
4. (Mollification.) Child mollify, applied to g, its Lipschitz constant, S and δ, gives C^∞ functions g_k with g_k = 0 off T = cthickening δ S, g_k → g uniformly on ℝ^m, and ∫ ofReal(‖Dg_k − Dg‖²) dL^m → 0, where Dg = fderiv ℝ g.
5. (Cutoff.) K' := G(T) is compact (continuous image) and K' ⊆ M ∩ W. Choose ε > 0 with cthickening ε K' ⊆ W. By the smooth Urysohn lemma (exists_contDiff_support_eq_eq_one_iff for the open set thickening ε K' and the closed set cthickening (ε/2) K' ⊆ thickening ε K') there is a C^∞ function β with values in [0,1], support β = thickening ε K' and β = 1 exactly on cthickening (ε/2) K'. Then tsupport β ⊆ cthickening ε K' ⊆ W is compact, and β = 1 on the open set thickening (ε/2) K' ⊇ K'.
6. (Approximants.) ζ_k(z) := β(z)·g_k(pr(z − p)). Each ζ_k is C^∞ (products and compositions of C^∞ maps; z ↦ pr(z − p) is affine) and has compact support (β has). Put C' := K' = G(T), a compact subset of M.
7. (Vanishing off C'.) Let x ∈ M \ C'. If x ∈ W, then x = G(a) with a = pr(x − p), a ∉ T (else x ∈ G(T)), so g_k(a) = 0 and ζ_k(x) = 0. If x ∉ W, then x ∉ tsupport β, so β(x) = 0 and ζ_k(x) = 0.
8. (Uniform convergence on M.) Let x ∈ M. If x ∈ W, x = G(a) with a = pr(x − p) ∈ B_r(0) and ζ(x) = g(a). If a ∈ T, then x ∈ K', β(x) = 1 and |ζ_k(x) − ζ(x)| = |g_k(a) − g(a)|; if a ∉ T, then g_k(a) = 0 and g(a) = 0 (a ∉ S), so ζ_k(x) = ζ(x) = 0. If x ∉ W, then ζ_k(x) = 0 = ζ(x) (x ∉ C ⊆ W). Hence sup_M |ζ_k − ζ| ≤ sup_{ℝ^m} |g_k − g| → 0, i.e. ζ_k → ζ uniformly on M.
9. (A projection inequality.) For every linear λ : ℝ^m → ℝ and x ∈ ℝ^P: Σ_j λ(pr(P_xe_j))² ≤ ‖λ‖². Indeed let ℓ := λ∘pr∘P_x and u ∈ ℝ^P its Riesz vector (ℓ(v) = ⟨u, v⟩). Then λ(pr(P_xe_j)) = ℓ(e_j) = u_j, so Σ_j λ(pr(P_xe_j))² = ‖u‖² = ‖ℓ‖² ≤ (‖λ‖·‖pr‖·‖P_x‖)² ≤ ‖λ‖² (‖pr‖ ≤ 1, ‖P_x‖ ≤ 1).
10. (Pointwise bound.) Let H_k(z) := ofReal(‖Dg_k(pr(z − p)) − Dg(pr(z − p))‖²), a Borel function on ℝ^P (measurable_fderiv). Claim: for H^m-a.e. x ∈ M,
 ofReal(Σ_j (Dζ_k(x)(P_xe_j) − d^M_xζ(P_xe_j))²) ≤ 1_W(x)·H_k(x).
 By child rademacher it suffices to take x ∈ M where ζ is differentiable within M; put L := fderivWithin ℝ ζ M x.
 Case x ∈ W. Write x = G(a), a = pr(x − p) ∈ B_r(0).
 (i) G has derivative DG(a) at a and maps B_r(0) into M, so ζ∘G has derivative L∘DG(a) at a (chain rule within B_r(0), a neighbourhood of a); g = ζ∘G near a, hence Dg(a) = L∘DG(a).
 (ii) Dζ_k(x) = Dg_k(a)∘pr: if a ∈ T, then x ∈ K' ⊆ thickening (ε/2) K', an open set on which β = 1, so ζ_k = g_k∘pr(· − p) near x and the chain rule applies. If a ∉ T, then g_k = 0 on the open neighbourhood ℝ^m \ T of a, so Dg_k(a) = 0, and ζ_k = 0 on the open neighbourhood {z : pr(z − p) ∉ T} of x, so Dζ_k(x) = 0.
 (iii) P_xe_j ∈ span(tangentSpace M x) ⊆ range DG(a) (tangentSpace M x = range DG(a)), so P_xe_j = DG(a)h with h = pr(P_xe_j) (pr∘DG(a) = id).
 (iv) By (i)–(iii), Dζ_k(x)(P_xe_j) − L(P_xe_j) = Dg_k(a)(pr P_xe_j) − L(DG(a)(pr P_xe_j)) = (Dg_k(a) − Dg(a))(pr(P_xe_j)), and step 9 (λ := Dg_k(a) − Dg(a)) bounds the sum of squares by ‖Dg_k(a) − Dg(a)‖², which is H_k(x) since a = pr(x − p).
 Case x ∉ W. Then x ∉ tsupport β, so ζ_k = 0 near x and Dζ_k(x) = 0. Also x ∉ C (C ⊆ W); C is closed and ζ = 0 on M \ C, which is a neighbourhood of x in M, so ζ has derivative 0 within M at x; by child tangent_uniqueness, L(P_xe_j) = 0 because P_xe_j ∈ span(tangentSpace M x). Every term vanishes and the left side is 0.
11. (Integration.) By step 10, monotonicity of the lower integral, W measurable, M ∩ W = G(B_r(0)), child lipschitz_transfer part (b) with D = B_r(0) and H = H_k, and H_k(G(a)) = ofReal(‖Dg_k(a) − Dg(a)‖²) for a ∈ B_r(0) (pr(G(a) − p) = a):
 ∫_M ofReal(Σ_j (Dζ_k(x)(P_xe_j) − d^M_xζ(P_xe_j))²) dH^m ≤ ∫_M 1_W H_k dH^m = ∫_{G(B_r(0))} H_k dH^m ≤ Λ^m ∫_{B_r(0)} H_k∘G dL^m = Λ^m ∫_{B_r(0)} ofReal(‖Dg_k − Dg‖²) dL^m ≤ Λ^m ∫ ofReal(‖Dg_k − Dg‖²) dL^m.
 The right side tends to Λ^m·0 = 0 by step 4 (Λ^m < ∞), so the left side tends to 0.
12. Steps 6, 7, 8 and 11 give C', the functions ζ_k and all asserted properties. ∎

Formal check (scratch validation by the decomposition author; not part of the frozen contract). The tactic proof below of `theorem Submission.codim1_hcp_lsa_local_chart_approx : <exactly the frozen lean_statement> := by`, after `import GMT.Ch07.Submission` inside `namespace GMT.Ch07` with the contract's opens and with the siblings Submission.dimred_rpd_embedded_locally_closed, Submission.codim1_hcp_lsa_c1_graph_chart, Submission.codim1_hcp_lsa_fderivWithin_eq_on_tangent_span, Submission.codim1_hcp_lsa_lipschitz_image_lintegral_le, Submission.codim1_hcp_lsa_mollify_lipschitz_compact_support and Submission.codim1_hcp_lsa_rademacher_on_submanifold present with their frozen types, compiled with Lean v4.35.0-rc3 / Mathlib 25730c7c (only deprecation warnings); #print axioms: propext, Classical.choice, Quot.sound and those six siblings.
```lean
  classical
  intro P m M hM p hp
  obtain ⟨pr, G, r, W, Λ, hr, hWo, hpW, hpr, hG0, hGc, hGL, hMW, hleft, hderiv, htan⟩ :=
    Submission.codim1_hcp_lsa_c1_graph_chart P m M p hM hp
  have hMmeas : MeasurableSet M := (Submission.dimred_rpd_embedded_locally_closed P 1 m M hM).1
  refine ⟨W, hWo, hpW, ?_⟩
  rintro ζ hζ ⟨C, hCc, hCMW, hζC⟩
  -- chart facts
  have hGMW : ∀ a ∈ ball (0 : Euclid m) r, G a ∈ M ∩ W := fun a ha => by
    rw [hMW]; exact mem_image_of_mem G ha
  have hrep : ∀ x ∈ M ∩ W, pr (x - p) ∈ ball (0 : Euclid m) r ∧ G (pr (x - p)) = x := by
    intro x hx
    rw [hMW] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [hleft a ha]; exact ⟨ha, rfl⟩
  have hGcont : ContinuousOn G (ball 0 r) := hGc.continuousOn
  -- the compact parameter set `S` of `C`
  set S : Set (Euclid m) := (fun x => pr (x - p)) '' C with hS
  have hSc : IsCompact S := hCc.image (by fun_prop)
  have hSball : S ⊆ ball 0 r := by
    rintro _ ⟨x, hx, rfl⟩; exact (hrep x (hCMW hx)).1
  obtain ⟨δ₀, hδ₀, hδ₀sub⟩ := hSc.exists_cthickening_subset_open isOpen_ball hSball
  set δ : ℝ := δ₀ / 2 with hδ
  have hδpos : 0 < δ := by positivity
  set T : Set (Euclid m) := Metric.cthickening δ S with hT
  have hTc : IsCompact T := hSc.cthickening
  have hTball : T ⊆ ball 0 r := (Metric.cthickening_mono (by linarith) S).trans hδ₀sub
  have hST : S ⊆ T := Metric.self_subset_cthickening S
  -- the coordinate function `g`
  set g : Euclid m → ℝ := fun a => if a ∈ ball (0 : Euclid m) r then ζ (G a) else 0 with hg
  have hg_ball : ∀ a ∈ ball (0 : Euclid m) r, g a = ζ (G a) := fun a ha => if_pos ha
  have hg0 : ∀ a, a ∉ S → g a = 0 := by
    intro a ha
    by_cases hab : a ∈ ball (0 : Euclid m) r
    · rw [hg_ball a hab]
      refine hζC (G a) (hGMW a hab).1 fun hGC => ha ?_
      exact ⟨G a, hGC, hleft a hab⟩
    · exact if_neg hab
  -- `ζ ∘ G` is locally Lipschitz on the ball
  have hζG : LocallyLipschitzOn (ball (0 : Euclid m) r) (ζ ∘ G) := by
    intro a ha
    obtain ⟨K, t, ht, hKt⟩ := hζ (hGMW a ha).1
    have ht' : t ∈ 𝓝[G '' ball 0 r] (G a) :=
      nhdsWithin_mono _ (fun y hy => by rw [← hMW] at hy; exact hy.1) ht
    refine ⟨K * Λ, G ⁻¹' t ∩ ball 0 r, ?_, ?_⟩
    · exact inter_mem ((hGcont a ha).preimage_mem_nhdsWithin' ht') self_mem_nhdsWithin
    · exact hKt.comp (hGL.mono inter_subset_right) fun b hb => hb.1
  obtain ⟨K₁, hK₁⟩ := (hζG.mono hTball).exists_lipschitzOnWith_of_compact hTc
  obtain ⟨B, hB⟩ := hTc.exists_bound_of_continuousOn (hK₁.continuousOn)
  -- `g` is globally Lipschitz
  have hgLip : LipschitzWith (max K₁ (Real.toNNReal (B / δ))) g := by
    have hgT : ∀ a ∈ T, g a = ζ (G a) := fun a ha => hg_ball a (hTball ha)
    have hfar : ∀ a b, a ∈ S → b ∉ T → dist (g a) (g b) ≤ max K₁ (Real.toNNReal (B / δ)) * dist a b := by
      intro a b ha hb
      have hgb : g b = 0 := hg0 b fun h => hb (hST h)
      have hdist : δ < dist a b := by
        by_contra hle
        exact hb (Metric.mem_cthickening_of_dist_le b a δ S ha (by rw [dist_comm]; linarith))
      rw [hgb, dist_zero_right]
      have hBa : ‖g a‖ ≤ B := by rw [hgT a (hST ha)]; exact hB a (hST ha)
      have hB0 : 0 ≤ B := le_trans (norm_nonneg _) hBa
      calc ‖g a‖ ≤ B := hBa
        _ ≤ B / δ * dist a b := by
            rw [div_mul_eq_mul_div, le_div_iff₀ hδpos]
            exact mul_le_mul_of_nonneg_left hdist.le hB0
        _ ≤ (Real.toNNReal (B / δ) : ℝ) * dist a b :=
            mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) dist_nonneg
        _ ≤ (max K₁ (Real.toNNReal (B / δ)) : ℝ) * dist a b := by
            gcongr; exact le_max_right _ _
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    by_cases ha : a ∈ T <;> by_cases hb : b ∈ T
    · rw [hgT a ha, hgT b hb]
      calc dist (ζ (G a)) (ζ (G b)) ≤ K₁ * dist a b := hK₁.dist_le_mul a ha b hb
        _ ≤ _ := by gcongr; exact le_max_left _ _
    · by_cases haS : a ∈ S
      · exact hfar a b haS hb
      · rw [hg0 a haS, hg0 b fun h => hb (hST h), dist_self]; positivity
    · by_cases hbS : b ∈ S
      · rw [dist_comm, dist_comm a b]; exact hfar b a hbS ha
      · rw [hg0 a fun h => ha (hST h), hg0 b hbS, dist_self]; positivity
    · rw [hg0 a fun h => ha (hST h), hg0 b fun h => hb (hST h), dist_self]; positivity
  -- mollification (child `mollify`)
  obtain ⟨gs, hgs_smooth, hgs_supp, hgs_unif, hgs_L2⟩ :=
    Submission.codim1_hcp_lsa_mollify_lipschitz_compact_support m g _ S δ hgLip hSc hg0 hδpos
  -- the cutoff `β`: smooth, `= 1` near `G(T)`, support inside `W`
  set K' : Set (Euclid P) := G '' T with hK'
  have hK'c : IsCompact K' := hTc.image_of_continuousOn (hGcont.mono hTball)
  have hK'MW : K' ⊆ M ∩ W := by rintro _ ⟨a, ha, rfl⟩; exact hGMW a (hTball ha)
  obtain ⟨ε, hε, hεW⟩ := hK'c.exists_cthickening_subset_open hWo fun x hx => (hK'MW hx).2
  obtain ⟨β, hβs, hβr, hβsupp, hβ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
    (Metric.isOpen_thickening (δ := ε) (E := K')) (Metric.isClosed_cthickening (δ := ε / 2) (E := K'))
    (Metric.cthickening_subset_thickening' hε (by linarith) K')
  have htsβ : tsupport β ⊆ Metric.cthickening ε K' := by
    rw [tsupport, hβsupp]; exact Metric.closure_thickening_subset_cthickening ε K'
  have hβcs : HasCompactSupport β := hK'c.cthickening.of_isClosed_subset (isClosed_tsupport β) htsβ
  have hβ0 : ∀ x, x ∉ W → x ∉ tsupport β := fun x hx h => hx (hεW (htsβ h))
  have hβone : ∀ x ∈ Metric.thickening (ε / 2) K', β x = 1 := fun x hx =>
    (hβ1 x).1 (Metric.thickening_subset_cthickening _ _ hx)
  have hK'thick : K' ⊆ Metric.thickening (ε / 2) K' := Metric.self_subset_thickening (by positivity) K'
  have hprc : ContDiff ℝ (⊤ : ℕ∞) (fun z : Euclid P => pr (z - p)) := by fun_prop
  refine ⟨K', fun k z => β z * gs k (pr (z - p)), hK'c, fun x hx => (hK'MW hx).1,
    fun k => ⟨hβs.mul ((hgs_smooth k).comp hprc), hβcs.mul_right⟩, ?_, ?_, ?_⟩
  · -- vanishing off `K'`
    intro k x hxM hxK
    by_cases hxW : x ∈ W
    · obtain ⟨ha, hGa⟩ := hrep x ⟨hxM, hxW⟩
      have haT : pr (x - p) ∉ T := fun h => hxK ⟨_, h, hGa⟩
      simp only [hgs_supp k _ haT, mul_zero]
    · simp only [image_eq_zero_of_notMem_tsupport (hβ0 x hxW), zero_mul]
  · -- uniform convergence on `M`
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε' hε'
    filter_upwards [Metric.tendstoUniformly_iff.1 hgs_unif ε' hε'] with k hk x hxM
    by_cases hxW : x ∈ W
    · obtain ⟨ha, hGa⟩ := hrep x ⟨hxM, hxW⟩
      have hζx : ζ x = g (pr (x - p)) := by rw [hg_ball _ ha, hGa]
      by_cases haT : pr (x - p) ∈ T
      · rw [hβone x (hK'thick ⟨_, haT, hGa⟩), one_mul, hζx]; exact hk _
      · rw [hgs_supp k _ haT, mul_zero, hζx, hg0 _ fun h => haT (hST h), dist_self]; exact hε'
    · rw [image_eq_zero_of_notMem_tsupport (hβ0 x hxW), zero_mul,
        hζC x hxM fun h => hxW (hCMW h).2, dist_self]
      exact hε'
  · -- the gradient error
    set w : Euclid P → Fin P → Euclid P := fun x j =>
      (Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1) with hw
    -- algebra: `∑ⱼ λ(pr(Pₓ eⱼ))² ≤ ‖λ‖²`
    have halg : ∀ (l : Euclid m →L[ℝ] ℝ) (x : Euclid P), ∑ j : Fin P, (l (pr (w x j))) ^ 2 ≤ ‖l‖ ^ 2 := by
      intro l x
      set ℓ : Euclid P →L[ℝ] ℝ := (l.comp pr).comp (Submodule.span ℝ (tangentSpace M x)).starProjection
      set u : Euclid P := (InnerProductSpace.toDual ℝ (Euclid P)).symm ℓ
      have hu : ∀ v, ℓ v = inner ℝ u v := fun v => (InnerProductSpace.toDual_symm_apply).symm
      have hcoord : ∀ j : Fin P, l (pr (w x j)) = u j := by
        intro j
        have := hu (EuclideanSpace.single j 1)
        rw [EuclideanSpace.inner_single_right] at this
        simpa [ℓ, w] using this
      have hnorm : ‖u‖ = ‖ℓ‖ := LinearIsometryEquiv.norm_map _ _
      have hℓ : ‖ℓ‖ ≤ ‖l‖ := by
        calc ‖ℓ‖ ≤ ‖l.comp pr‖ * ‖(Submodule.span ℝ (tangentSpace M x)).starProjection‖ :=
              ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ (‖l‖ * ‖pr‖) * 1 := by
              gcongr
              · exact ContinuousLinearMap.opNorm_comp_le _ _
              · exact Submodule.starProjection_norm_le _
          _ ≤ ‖l‖ * 1 * 1 := by gcongr
          _ = ‖l‖ := by ring
      calc ∑ j : Fin P, (l (pr (w x j))) ^ 2 = ∑ j : Fin P, (u j) ^ 2 := by simp_rw [hcoord]
        _ = ‖u‖ ^ 2 := (EuclideanSpace.real_norm_sq_eq u).symm
        _ ≤ ‖l‖ ^ 2 := by rw [hnorm]; gcongr
    -- the measurable chart majorant
    set H : ℕ → Euclid P → ℝ≥0∞ := fun k z =>
      ENNReal.ofReal (‖fderiv ℝ (gs k) (pr (z - p)) - fderiv ℝ g (pr (z - p))‖ ^ 2) with hH
    have hHm : ∀ k, Measurable (H k) := by
      intro k
      have h1 : Measurable fun z : Euclid P => fderiv ℝ (gs k) (pr (z - p)) :=
        (measurable_fderiv ℝ (gs k)).comp (by fun_prop)
      have h2 : Measurable fun z : Euclid P => fderiv ℝ g (pr (z - p)) :=
        (measurable_fderiv ℝ g).comp (by fun_prop)
      exact ((h1.sub h2).norm.pow_const 2).ennreal_ofReal
    have hζdiff := Submission.codim1_hcp_lsa_rademacher_on_submanifold P m M ζ hM hζ
    -- pointwise bound, a.e. on `M`
    have hpt : ∀ k, ∀ᵐ x ∂(μHE[m].restrict M), ENNReal.ofReal (∑ j : Fin P,
        (fderiv ℝ (fun z => β z * gs k (pr (z - p))) x (w x j) - fderivWithin ℝ ζ M x (w x j)) ^ 2)
          ≤ W.indicator (H k) x := by
      intro k
      filter_upwards [hζdiff, ae_restrict_mem hMmeas] with x hxd hxM
      by_cases hxW : x ∈ W
      · rw [indicator_of_mem hxW]
        obtain ⟨ha, hGa⟩ := hrep x ⟨hxM, hxW⟩
        set a := pr (x - p) with ha_def
        -- (i) the chart derivative of `ζ`
        have hGd : HasFDerivAt G (fderiv ℝ G a) a :=
          ((hGc.contDiffAt (isOpen_ball.mem_nhds ha)).differentiableAt one_ne_zero).hasFDerivAt
        have hGM : MapsTo G (ball 0 r) M := fun b hb => (hGMW b hb).1
        have hcomp : HasFDerivAt (ζ ∘ G) ((fderivWithin ℝ ζ M x).comp (fderiv ℝ G a)) a := by
          have hxd' : HasFDerivWithinAt ζ (fderivWithin ℝ ζ M x) M (G a) := by
            rw [hGa]; exact hxd.hasFDerivWithinAt
          exact (hxd'.comp a hGd.hasFDerivWithinAt hGM).hasFDerivAt (isOpen_ball.mem_nhds ha)
        have hgeq : g =ᶠ[𝓝 a] ζ ∘ G := by
          filter_upwards [isOpen_ball.mem_nhds ha] with b hb
          exact hg_ball b hb
        have hDg : fderiv ℝ g a = (fderivWithin ℝ ζ M x).comp (fderiv ℝ G a) :=
          (hcomp.congr_of_eventuallyEq hgeq).fderiv
        -- (ii) the derivative of the approximant
        have hDζs : fderiv ℝ (fun z => β z * gs k (pr (z - p))) x = (fderiv ℝ (gs k) a).comp pr := by
          have hprd : HasFDerivAt (fun z : Euclid P => pr (z - p)) pr x := by
            have h := (pr.hasFDerivAt (x := x - p)).comp x ((hasFDerivAt_id x).sub_const p)
            rw [ContinuousLinearMap.comp_id] at h
            exact h
          by_cases haT : a ∈ T
          · have hxK : x ∈ Metric.thickening (ε / 2) K' := hK'thick ⟨a, haT, hGa⟩
            have heq : (fun z => β z * gs k (pr (z - p))) =ᶠ[𝓝 x] fun z => gs k (pr (z - p)) := by
              filter_upwards [Metric.isOpen_thickening.mem_nhds hxK] with z hz
              rw [hβone z hz, one_mul]
            rw [heq.fderiv_eq]
            have hgsd : HasFDerivAt (gs k) (fderiv ℝ (gs k) a) a :=
              ((hgs_smooth k).differentiable (by simp) a).hasFDerivAt
            exact (hgsd.comp x hprd).fderiv
          · have hnhds : (fun z : Euclid P => pr (z - p)) ⁻¹' Tᶜ ∈ 𝓝 x :=
              (Metric.isClosed_cthickening.isOpen_compl.preimage (by fun_prop)).mem_nhds haT
            have heq : (fun z => β z * gs k (pr (z - p))) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
              filter_upwards [hnhds] with z hz
              rw [hgs_supp k _ hz, mul_zero]
            have hga : gs k =ᶠ[𝓝 a] fun _ => (0 : ℝ) := by
              filter_upwards [Metric.isClosed_cthickening.isOpen_compl.mem_nhds haT] with b hb
              exact hgs_supp k b hb
            rw [heq.fderiv_eq, hga.fderiv_eq]
            simp
        -- (iii) tangent vectors are images of their `pr`-coordinates
        have hwj : ∀ j, fderiv ℝ G a (pr (w x j)) = w x j := by
          intro j
          have hmem0 := Submodule.starProjection_apply_mem (Submodule.span ℝ (tangentSpace M x))
            (EuclideanSpace.single j (1 : ℝ))
          have hle : Submodule.span ℝ (tangentSpace M x) ≤
              LinearMap.range ((fderiv ℝ G a : Euclid m →L[ℝ] Euclid P) : Euclid m →ₗ[ℝ] Euclid P) := by
            rw [Submodule.span_le, ← hGa, htan a ha]
            rintro _ ⟨y, rfl⟩
            exact ⟨y, rfl⟩
          obtain ⟨h, hh⟩ := LinearMap.mem_range.1 (hle hmem0)
          have hh' : fderiv ℝ G a h = w x j := hh
          rw [← hh']
          congr 1
          have := congrArg (fun T => T h) (hderiv a ha)
          simpa using this
        have herr : ∀ j, fderiv ℝ (fun z => β z * gs k (pr (z - p))) x (w x j) -
            fderivWithin ℝ ζ M x (w x j) = (fderiv ℝ (gs k) a - fderiv ℝ g a) (pr (w x j)) := by
          intro j
          rw [hDζs, hDg]
          simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, hwj j]
        simp_rw [herr]
        exact ENNReal.ofReal_le_ofReal (halg _ x)
      · rw [indicator_of_notMem hxW]
        -- both derivatives vanish on the relevant vectors
        have hxC : x ∉ C := fun h => hxW (hCMW h).2
        have hz1 : (fun z => β z * gs k (pr (z - p))) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
          filter_upwards [(notMem_tsupport_iff_eventuallyEq.1 (hβ0 x hxW))] with z hz
          rw [hz, Pi.zero_apply, zero_mul]
        have hz2 : HasFDerivWithinAt ζ (0 : Euclid P →L[ℝ] ℝ) M x := by
          have h0 : HasFDerivWithinAt (fun _ : Euclid P => (0 : ℝ)) (0 : Euclid P →L[ℝ] ℝ) M x :=
            hasFDerivWithinAt_const 0 x M
          refine h0.congr_of_eventuallyEq ?_ (hζC x hxM hxC)
          filter_upwards [inter_mem_nhdsWithin M (hCc.isClosed.isOpen_compl.mem_nhds hxC)] with y hy
          exact hζC y hy.1 hy.2
        have hterm : ∀ j, fderiv ℝ (fun z => β z * gs k (pr (z - p))) x (w x j) -
            fderivWithin ℝ ζ M x (w x j) = 0 := by
          intro j
          rw [hz1.fderiv_eq,
            Submission.codim1_hcp_lsa_fderivWithin_eq_on_tangent_span P M ζ 0 x (w x j) hz2
              (Submodule.starProjection_apply_mem _ _)]
          simp
        have hsum0 : ∑ j : Fin P, (fderiv ℝ (fun z => β z * gs k (pr (z - p))) x (w x j) -
            fderivWithin ℝ ζ M x (w x j)) ^ 2 = 0 := by
          simp only [hterm]; simp
        rw [hsum0, ENNReal.ofReal_zero]
    -- integrate: transfer to the chart ball and pass to the limit
    have hint : ∀ k, ∫⁻ x in M, ENNReal.ofReal (∑ j : Fin P,
        (fderiv ℝ (fun z => β z * gs k (pr (z - p))) x (w x j) - fderivWithin ℝ ζ M x (w x j)) ^ 2)
          ∂μHE[m] ≤ (Λ : ℝ≥0∞) ^ m *
            ∫⁻ a, ENNReal.ofReal (‖fderiv ℝ (gs k) a - fderiv ℝ g a‖ ^ 2) := by
      intro k
      have hWm : MeasurableSet W := hWo.measurableSet
      calc _ ≤ ∫⁻ x in M, W.indicator (H k) x ∂μHE[m] := lintegral_mono_ae (hpt k)
        _ = ∫⁻ x in G '' ball 0 r, H k x ∂μHE[m] := by
            rw [lintegral_indicator hWm, Measure.restrict_restrict hWm, inter_comm, hMW]
        _ ≤ (Λ : ℝ≥0∞) ^ m * ∫⁻ a in ball (0 : Euclid m) r, H k (G a) :=
            (Submission.codim1_hcp_lsa_lipschitz_image_lintegral_le m P G (ball 0 r) Λ hGL).2
              measurableSet_ball (H k) (hHm k)
        _ = (Λ : ℝ≥0∞) ^ m * ∫⁻ a in ball (0 : Euclid m) r,
              ENNReal.ofReal (‖fderiv ℝ (gs k) a - fderiv ℝ g a‖ ^ 2) := by
            congr 1
            refine setLIntegral_congr_fun measurableSet_ball fun a ha => ?_
            simp only [hH, hleft a ha]
        _ ≤ _ := mul_le_mul_right (setLIntegral_le_lintegral _ _) _
    have hlim : Tendsto (fun k => (Λ : ℝ≥0∞) ^ m *
        ∫⁻ a, ENNReal.ofReal (‖fderiv ℝ (gs k) a - fderiv ℝ g a‖ ^ 2)) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (a := (Λ : ℝ≥0∞) ^ m) hgs_L2
        (Or.inr (ENNReal.pow_ne_top ENNReal.coe_ne_top))
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun k => zero_le) hint
```

Integration check: this proof was also compiled together with the proofs of all eight new sibling children and the assembly of the parent theorem in a single file (only the four reused accepted declarations taken as axioms); the file compiled without errors or `sorry`.

## Key steps

1. W is a graph-chart domain. g := ζ∘G on the chart ball (0 outside) is globally Lipschitz and vanishes off the compact S = pr(C − p).
2. mollify gives g_k. Put ζ_k := β·g_k∘pr(· − p), with a smooth cutoff β = 1 near G(T) and tsupport β ⊆ W.
3. Uniform convergence and vanishing off C' = G(T) are read off in chart coordinates.
4. A.e. on M ∩ W the error is (Dg_k(a) − Dg(a))(pr P_xe_j), and its squares sum to at most ‖Dg_k(a) − Dg(a)‖². Off W the error vanishes by tangent_uniqueness.
5. lipschitz_transfer moves the integral to the chart ball, where it tends to 0 by mollify.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; sha256sum GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `sed -n 1,457p GMT/Ch07/Contract.lean (Euclid, IsEmbeddedSubmanifold, tangentSpace, μHE usage)`
- `python3 scans of dag.json: selected node (depth 5, max_depth 6), parent hypercone_plane and its decomposition-v1.json, accepted nodes whose statements mention Lipschitz/mollif/convol/graph chart/starProjection/tangentSpace, lean_name collision scan for codim1_hcp_lsa_*`
- `runtime.py: _decompose (max_depth), _existing_lean_name_problem (reuse of accepted declarations by identical name and type)`
- `git show <candidate>:GMT/Ch07/Submission.lean for 93f7ea7a3650 (codim1_rdo_gc_local_inverse_c2, dsmc_chart_inverse_continuity), d25d2377 (codim1_zsl_pc_mollify_indicator_l1), and the handoffs of codim1_zsl_gc_local_inverse and dsmc_chart_inverse_continuity`
- `grep -rn in local-references/123e8435b4a2469b/mathlib/Mathlib: euclideanHausdorffMeasure, ae_differentiableWithinAt_of_mem, LipschitzWith.ae_differentiableAt, measurable_fderiv, tangentConeAt, HasFDerivWithinAt.unique_on, mem_tangentConeAt_of_seq, hasFDerivAt_convolution_left, contDiff_convolution_left, ae_convolution_tendsto_right_of_locallyIntegrable, LocallyLipschitzOn.exists_lipschitzOnWith_of_compact, LocallyLipschitzOn.mul, exists_isSubordinate, exists_contDiff_support_eq_eq_one_iff, sq_sum_le_card_mul_sum_sq, measurePreserving_sub_left`
- `lean #check probes in the GMT.Ch07.Submission import closure (Imp*.lean, Inst5.lean): SmoothPartitionOfUnity.exists_isSubordinate, ContDiffBump API, ContDiffBump.normed (missing), VitaliFamily.ae_tendsto_average_norm_sub, Besicovitch.tendsto_filterAt, tendsto_integral_smul_of_tendsto_average_norm_sub, aestronglyMeasurable_iUnion_iff, Submodule.eq_starProjection_of_mem_of_inner_eq_zero, NormedRing.inverse_continuousAt, instances HasContDiffBump/HasBesicovitchCovering (Euclid m)`
- `lean -DautoImplicit=false /tmp/lsa-split/check/{TypesAll,Assembly,N1,N2,N3,N4,N5,N6,N7,N8,Integration}.lean (LEAN_PATH = .lake/build/lib/lean plus every package's .lake/build/lib/lean)`
- `git for-each-ref | xargs git grep -l codim1_hcp_lsa -- 'GMT/*.lean' (no match); grep codim1_hcp_lsa dag.json (0); grep -rn codim1_hcp_lsa simongmt (no match)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-e9797ac1a5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-b5d5990773/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-2511ff6312/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ch-0f11358db9/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-252c8df06c56/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/TangentCone/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Uniform.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/tmp/lsa-split/check/TypesAll.lean`
- `/tmp/lsa-split/check/Assembly.lean`
- `/tmp/lsa-split/check/Integration.lean`

Pins match: manifest project b4d606db and Mathlib 25730c7c equal workspace HEAD and .lake/packages/mathlib, and the snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…). The node has depth 5 with max_depth 6, so the children are leaves. Reuse: four accepted declarations (chart_tangentSpace_eq_range_fderiv, dimred_rpd_embedded_locally_closed, codim1_zsl_gc_local_inverse, dsmc_chart_inverse_continuity) are taken with byte-identical frozen types. The C² graph-chart and tangent-projection lemmas (codim1_rdo_gc_graph_over_tangent, submanifold_tangentProjection_c1_extension, dor_lmb_ret_tangent_projection) do not apply to C¹ M. No C¹ graph chart, Rademacher-on-M, tangent-projection continuity or L²-gradient mollification lemma exists in the DAG, SimonGMT or the snapshot, and the 8 codim1_hcp_lsa_ names are unused everywhere. Mathlib in the Submission import closure provides Rademacher (LipschitzOnWith.ae_differentiableWithinAt_of_mem), measurable_fderiv, HasFDerivWithinAt.unique_on with mem_tangentConeAt_of_seq, LipschitzOnWith.hausdorffMeasure_image_le with EuclideanSpace.euclideanHausdorffMeasure_eq_volume, convolution smoothness, ContDiffBump, Besicovitch Lebesgue differentiation, SmoothPartitionOfUnity and exists_contDiff_support_eq_eq_one_iff. It lacks ContDiffBump.normed, ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable and sq_sum_le_card_mul_sum_sq; the mollify proof rebuilds the first two by hand, and the assembly uses Finset.sum_mul_sq_le_sq_mul_sq. Lean: all 12 child types elaborate. The selected type is kernel-checked from the child types as axioms. Every new child is proved from exactly its declared siblings. The integrated file (8 proofs plus assembly, only the 4 reused declarations as axioms) compiles without errors or sorry.
