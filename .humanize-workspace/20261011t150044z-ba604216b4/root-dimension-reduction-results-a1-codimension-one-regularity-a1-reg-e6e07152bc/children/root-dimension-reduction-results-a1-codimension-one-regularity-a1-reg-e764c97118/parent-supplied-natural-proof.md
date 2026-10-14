# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.graph_chart-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.graph_chart-a1.graph_over_tangent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 2–5 of the parent proof of codim1_rdo_graph_chart: (1b) the chart is a homeomorphism, (1c) range Dψ(z₀) = Π, (1d) the graph map from the inverse function theorem and the choice of δ₁, δ₂, and the verification 5(a)–(d). Here the plane Π = T_xN is given through an arbitrary isometric parametrization ι, and the dimension is a general d (the parent uses d = n + 1). Siblings used: chart_tangent_range (accepted Submission.dsmc_chart_tangentSpace_eq_range) for parent steps 2–3, and local_inverse_c2 (Submission.codim1_rdo_gc_local_inverse_c2) for the inverse function theorem of step 4. Additionally the proof records Du(0) = 0, which the parent derives in step 4 and uses in step 6.

Notation. ι* := adjoint of ι (ι.toContinuousLinearMap.adjoint : ℝ^P → ℝ^d), so ⟨ιw, h⟩ = ⟨w, ι*h⟩ for w ∈ ℝ^d, h ∈ ℝ^P. "h ⊥ range ι" means ⟨ιw, h⟩ = 0 for all w.

Proof.
1. (Adjoint facts.)
 (a) ι*(ιw) = w for every w: for every w', ⟨w', ι*ιw⟩ = ⟨ιw', ιw⟩ = ⟨w', w⟩ because ι preserves inner products (LinearIsometry.inner_map_map).
 (b) If h ⊥ range ι then ι*h = 0: ⟨w, ι*h⟩ = ⟨ιw, h⟩ = 0 for all w.
 (c) If ι*h = 0 then h ⊥ range ι: ⟨ιw, h⟩ = ⟨w, ι*h⟩ = 0.
2. (Chart; parent (1b).) IsEmbeddedSubmanifold 2 d N at x ∈ N gives open V ⊆ ℝ^d and open W ⊆ ℝ^P with x ∈ W, and ψ : ℝ^d → ℝ^P that is C² and injective on V, with ψ(V) = W ∩ N, V ∩ ψ⁻¹(K) compact for every compact K ⊆ W, and Dψ(z) injective for every z ∈ V. Since x ∈ W ∩ N = ψ(V), fix z₀ ∈ V with ψ(z₀) = x.
3. (Tangent plane and continuity of the inverse chart; parent (1b)–(1c).) The accepted lemma chart_tangent_range (dsmc_chart_tangentSpace_eq_range, with r = 2 ≥ 1, applied to the chart data of step 2 at z₀) gives:
 (i) tangentSpace N x = range Dψ(z₀);
 (ii) for every ε > 0 there is δ > 0 such that every z ∈ V with |ψ(z) − x| < δ satisfies |z − z₀| < ε. (This is the continuity of ψ⁻¹ at x, the consequence of properness that the parent derives in step 2.)
 With the hypothesis range ι = tangentSpace N x, (i) gives range Dψ(z₀) = range ι.
4. (The map φ; parent (1d).) Define φ(z) := ι*(ψ(z) − x). φ is C² on V (the continuous linear map ι* composed with ψ − x), and φ(z₀) = ι*(x − x) = 0. By the chain rule Dφ(z₀) = ι*∘Dψ(z₀). Dφ(z₀) is injective: let ι*Dψ(z₀)a₁ = ι*Dψ(z₀)a₂ and a := a₁ − a₂, so ι*Dψ(z₀)a = 0. As Dψ(z₀)a ∈ range Dψ(z₀) = range ι, write Dψ(z₀)a = ιw; then w = ι*ιw = ι*Dψ(z₀)a = 0 by 1(a), so Dψ(z₀)a = 0 = Dψ(z₀)0, and a = 0 because Dψ(z₀) is injective.
5. (Local inverse.) local_inverse_c2 applied to φ, V, z₀ gives open V₀, O ⊆ ℝ^d and g : ℝ^d → ℝ^d with z₀ ∈ V₀ ⊆ V, g C² on O, g(O) ⊆ V₀, φ(g(y)) = y for y ∈ O, and φ(z) ∈ O, g(φ(z)) = z for z ∈ V₀. Taking z = z₀: 0 = φ(z₀) ∈ O and g(0) = z₀.
6. (The graph map u; parent (★).) Define u(v) := ψ(g(v)) − x − ιv for every v ∈ ℝ^d.
 (a) (★) x + ιv + u(v) = ψ(g(v)) for every v.
 (b) u(0) = ψ(z₀) − x − ι0 = 0.
 (c) u is C² on O: g is C² on O with g(O) ⊆ V₀ ⊆ V and ψ is C² on V, so ψ∘g is C² on O; subtracting the constant x and the linear map ι keeps it C².
 (d) For v ∈ O: ι*u(v) = ι*(ψ(g(v)) − x) − ι*ιv = φ(g(v)) − v = v − v = 0, so u(v) ⊥ range ι by 1(c).
 (e) For v ∈ O: g(v) ∈ V, so x + ιv + u(v) = ψ(g(v)) ∈ ψ(V) = W ∩ N ⊆ N.
7. (Du(0) = 0; parent (1d).) Since u is C² on the open set O, it is differentiable at every point of O; g is differentiable at 0 ∈ O and ψ at g(0) = z₀ ∈ V.
 (a) Fix w ∈ ℝ^d. The real function v ↦ ⟨ιw, u(v)⟩ vanishes on the open neighbourhood O of 0 by 6(d), so its derivative at 0, namely a ↦ ⟨ιw, Du(0)a⟩, equals the derivative of the zero function, i.e. 0 (HasFDerivAt.congr_of_eventuallyEq and uniqueness of derivatives). Thus Du(0)a ⊥ range ι for every a.
 (b) By the chain rule, Du(0) = Dψ(z₀)∘Dg(0) − ι. For a ∈ ℝ^d, Dψ(z₀)(Dg(0)a) ∈ range Dψ(z₀) = range ι, say Dψ(z₀)(Dg(0)a) = ιw₁; so Du(0)a = ιw₁ − ιa = ι(w₁ − a).
 (c) By (a) with w = w₁ − a: ‖Du(0)a‖² = ⟨ι(w₁ − a), Du(0)a⟩ = 0. Hence Du(0)a = 0 for every a, i.e. Du(0) = 0.
8. (N near x lies in ψ(V₀); parent step 2.) V₀ is open and z₀ ∈ V₀, so choose ε > 0 with ball(z₀, ε) ⊆ V₀, and let δ_C > 0 correspond to this ε by 3(ii). Choose ρ_W > 0 with ball(x, ρ_W) ⊆ W and ρ_U > 0 with ball(x, ρ_U) ⊆ U (W, U open, x ∈ W ∩ U). Put s := min(ρ_W, δ_C, ρ_U) > 0. Claim: if q ∈ N and |q − x| < s, then q = ψ(z) for some z ∈ V₀. Indeed q ∈ ball(x, ρ_W) ⊆ W, so q ∈ W ∩ N = ψ(V) and q = ψ(z) with z ∈ V; |ψ(z) − x| < δ_C gives |z − z₀| < ε, so z ∈ V₀.
9. (Choice of δ₁, δ₂; parent step 4, last item.) Put r₁ := s/4 > 0 and δ₂ := r₁.
 - u is continuous at 0 (6(c)) with u(0) = 0, so there is ρ₁ > 0 with ‖u(v)‖ < r₁/2 whenever ‖v‖ < ρ₁.
 - Du is continuous on the open set O (u is C² on O; ContDiffOn.continuousOn_fderiv_of_isOpen) and Du(0) = 0, so there is ρ₂ > 0 with ‖Du(v)‖ < 1 whenever ‖v‖ < ρ₂.
 - O is open with 0 ∈ O, so there is ρ₃ > 0 with ball(0, ρ₃) ⊆ O.
 Put δ₁ := min(ρ₁, ρ₂, ρ₃, r₁) > 0.
10. (Verification; parent step 5.)
 (a) If |q − x| ≤ δ₁ + δ₂ then |q − x| ≤ 2r₁ = s/2 < s ≤ ρ_U, so q ∈ U. Hence closedBall(x, δ₁ + δ₂) ⊆ U.
 (b) u(0) = 0 (6(b)), Du(0) = 0 (step 7), and u is C² on ball(0, δ₁) ⊆ ball(0, ρ₃) ⊆ O (6(c)).
 (c) Let v ∈ ball(0, δ₁), so v ∈ O, ‖v‖ < ρ₁ and ‖v‖ < ρ₂. Then u(v) ⊥ range ι (6(d)), ‖Du(v)‖ ≤ 1, ‖u(v)‖ < r₁/2 = δ₂/2, and x + ιv + u(v) ∈ N (6(e)).
 (d) (Uniqueness; parent 5(d).) Let ‖v‖ < δ₁, ‖h‖ < δ₂, h ⊥ range ι, and q := x + ιv + h ∈ N. Then |q − x| = ‖ιv + h‖ ≤ ‖ιv‖ + ‖h‖ = ‖v‖ + ‖h‖ < δ₁ + δ₂ ≤ 2r₁ < s. By step 8, q = ψ(z) with z ∈ V₀. Then φ(z) = ι*(q − x) = ι*(ιv + h) = ι*ιv + ι*h = v + 0 = v by 1(a) and 1(b). By step 5, z = g(φ(z)) = g(v). By (★), x + ιv + u(v) = ψ(g(v)) = ψ(z) = q = x + ιv + h, hence h = u(v). (The parent uses ‖q − x‖² = ‖v‖² + ‖h‖²; the triangle inequality suffices.) ∎

Formalization note (verified). The following Lean proof was compiled against the frozen import closure of GMT/Ch07/Submission.lean (Lean 4.35.0-rc3, Mathlib 25730c7c), with the accepted Submission.dsmc_chart_tangentSpace_eq_range and the sibling Submission.codim1_rdo_gc_local_inverse_c2 present, as a single appended declaration inside namespace GMT.Ch07 before main_theorem; #print axioms gives propext, Classical.choice, Quot.sound; it passes the runtime leaf-delta check (check_source_delta). It may be used verbatim:

theorem Submission.codim1_rdo_gc_graph_over_tangent : ∀ (P d : ℕ) (U N : Set (Euclid P)) (x : Euclid P) (ι : Euclid d →ₗᵢ[ℝ] Euclid P), IsOpen U → IsEmbeddedSubmanifold 2 d N → x ∈ N ∩ U → Set.range ι = tangentSpace N x → ∃ (u : Euclid d → Euclid P) (δ₁ δ₂ : ℝ), 0 < δ₁ ∧ 0 < δ₂ ∧ closedBall x (δ₁ + δ₂) ⊆ U ∧ u 0 = 0 ∧ fderiv ℝ u 0 = 0 ∧ ContDiffOn ℝ 2 u (ball 0 δ₁) ∧ (∀ v ∈ ball (0 : Euclid d) δ₁, (∀ w : Euclid d, inner ℝ (ι w) (u v) = 0) ∧ ‖fderiv ℝ u v‖ ≤ 1 ∧ ‖u v‖ < δ₂ / 2 ∧ x + ι v + u v ∈ N) ∧ ∀ (v : Euclid d) (h : Euclid P), ‖v‖ < δ₁ → ‖h‖ < δ₂ → (∀ w : Euclid d, inner ℝ (ι w) h = 0) → x + ι v + h ∈ N → h = u v := by
  intro P d U N x ι hU hN hx hι
  obtain ⟨V, W, ψ, hV, hW, hxW, hψ, hψinj, hψimg, hprop, hDψ⟩ := hN x hx.1
  obtain ⟨z₀, hz₀V, hψz₀⟩ : x ∈ ψ '' V := by rw [hψimg]; exact ⟨hxW, hx.1⟩
  obtain ⟨htan, hinvc, -⟩ := Submission.dsmc_chart_tangentSpace_eq_range P 2 d N V W ψ
    (by norm_num) hV hW hψ hψinj hψimg hprop hDψ z₀ hz₀V
  rw [hψz₀] at htan hinvc
  have hrangeψ : Set.range (fderiv ℝ ψ z₀) = Set.range ι := by rw [← htan, hι]
  have hψ2 : ContDiffOn ℝ 2 ψ V := by exact_mod_cast hψ
  -- the adjoint of ι
  set ιs : Euclid P →L[ℝ] Euclid d := ι.toContinuousLinearMap.adjoint with hιs
  have hadj : ∀ w h, inner ℝ (ι w) h = inner ℝ w (ιs h) := fun w h => by
    rw [hιs, ContinuousLinearMap.adjoint_inner_right]; rfl
  have hιsι : ∀ w, ιs (ι w) = w := by
    intro w
    apply ext_inner_left ℝ
    intro w'
    rw [← hadj, LinearIsometry.inner_map_map]
  have hιs0 : ∀ h, (∀ w, inner ℝ (ι w) h = 0) → ιs h = 0 := by
    intro h hh
    apply ext_inner_left ℝ
    intro w
    rw [← hadj, hh w, inner_zero_right]
  -- the map φ = ι*(ψ - x) and its derivative at z₀
  have hψdiff : ∀ z ∈ V, HasFDerivAt ψ (fderiv ℝ ψ z) z := fun z hz =>
    ((hψ2.contDiffAt (hV.mem_nhds hz)).differentiableAt (by norm_num)).hasFDerivAt
  let φ : Euclid d → Euclid d := fun z => ιs (ψ z - x)
  have hφ : ContDiffOn ℝ 2 φ V := ιs.contDiff.comp_contDiffOn (hψ2.sub contDiffOn_const)
  have hφderiv : HasFDerivAt φ (ιs.comp (fderiv ℝ ψ z₀)) z₀ :=
    ιs.hasFDerivAt.comp z₀ ((hψdiff z₀ hz₀V).sub_const x)
  have hφinj : Injective (fderiv ℝ φ z₀) := by
    rw [hφderiv.fderiv]
    intro a₁ a₂ h
    have h1 : ιs (fderiv ℝ ψ z₀ (a₁ - a₂)) = 0 := by
      have h' : ιs (fderiv ℝ ψ z₀ a₁) = ιs (fderiv ℝ ψ z₀ a₂) := h
      rw [map_sub, map_sub, h', sub_self]
    obtain ⟨w, hw⟩ : fderiv ℝ ψ z₀ (a₁ - a₂) ∈ Set.range ι := hrangeψ ▸ ⟨a₁ - a₂, rfl⟩
    rw [← hw, hιsι] at h1
    have h2 : fderiv ℝ ψ z₀ (a₁ - a₂) = fderiv ℝ ψ z₀ 0 := by rw [← hw, h1, map_zero, map_zero]
    exact sub_eq_zero.mp (hDψ z₀ hz₀V h2)
  obtain ⟨V₀, O, g, hV₀, hO, hz₀V₀, hV₀V, hg, hgmaps, hφg, hgφ⟩ :=
    Submission.codim1_rdo_gc_local_inverse_c2 d φ V z₀ hV hz₀V hφ hφinj
  have hφz₀ : φ z₀ = 0 := by simp [φ, hψz₀]
  obtain ⟨h0O, hg0⟩ := hgφ z₀ hz₀V₀
  rw [hφz₀] at h0O hg0
  -- the graph map u
  let u : Euclid d → Euclid P := fun v => ψ (g v) - x - ι v
  have hGu : ∀ v, x + ι v + u v = ψ (g v) := fun v => by simp only [u]; abel
  have hu0 : u 0 = 0 := by simp [u, hg0, hψz₀]
  have hgV : MapsTo g O V := fun y hy => hV₀V (hgmaps hy)
  have huC2 : ContDiffOn ℝ 2 u O :=
    ((hψ2.comp hg hgV).sub contDiffOn_const).sub ι.toContinuousLinearMap.contDiff.contDiffOn
  have hιsu : ∀ v ∈ O, ιs (u v) = 0 := by
    intro v hv
    have h1 : ιs (ψ (g v) - x) = v := hφg v hv
    simp only [u, map_sub, hιsι]
    rw [← map_sub, h1, sub_self]
  have horthO : ∀ v ∈ O, ∀ w, inner ℝ (ι w) (u v) = 0 := by
    intro v hv w
    rw [hadj, hιsu v hv, inner_zero_right]
  have hmemO : ∀ v ∈ O, x + ι v + u v ∈ N := fun v hv => by
    rw [hGu]
    have h1 : ψ (g v) ∈ ψ '' V := ⟨g v, hgV hv, rfl⟩
    rw [hψimg] at h1
    exact h1.2
  have hudiff : ∀ v ∈ O, HasFDerivAt u (fderiv ℝ u v) v := fun v hv =>
    ((huC2.contDiffAt (hO.mem_nhds hv)).differentiableAt (by norm_num)).hasFDerivAt
  -- Du(0) = 0
  have hDu0 : fderiv ℝ u 0 = 0 := by
    have hgdiff : HasFDerivAt g (fderiv ℝ g 0) 0 :=
      ((hg.contDiffAt (hO.mem_nhds h0O)).differentiableAt (by norm_num)).hasFDerivAt
    have hψg : HasFDerivAt (fun v => ψ (g v)) ((fderiv ℝ ψ z₀).comp (fderiv ℝ g 0)) 0 := by
      have h' : HasFDerivAt ψ (fderiv ℝ ψ z₀) (g 0) := by rw [hg0]; exact hψdiff z₀ hz₀V
      exact h'.comp 0 hgdiff
    have huder : HasFDerivAt u ((fderiv ℝ ψ z₀).comp (fderiv ℝ g 0) - ι.toContinuousLinearMap) 0 :=
      (hψg.sub_const x).sub ι.toContinuousLinearMap.hasFDerivAt
    ext1 c
    -- orthogonality of the derivative
    have horthD : ∀ w, inner ℝ (ι w) (fderiv ℝ u 0 c) = 0 := by
      intro w
      have hloc : (fun v' => inner ℝ (ι w) (u v')) =ᶠ[𝓝 0] fun _ => (0 : ℝ) :=
        Filter.eventually_of_mem (hO.mem_nhds h0O) (fun v' hv' => horthO v' hv' w)
      have hd : HasFDerivAt (fun v' => inner ℝ (ι w) (u v'))
          ((innerSL ℝ (ι w)).comp (fderiv ℝ u 0)) 0 :=
        (innerSL ℝ (ι w)).hasFDerivAt.comp 0 (hudiff 0 h0O)
      have hd0 : HasFDerivAt (fun v' => inner ℝ (ι w) (u v')) (0 : Euclid d →L[ℝ] ℝ) 0 :=
        (hasFDerivAt_const (0 : ℝ) 0).congr_of_eventuallyEq hloc
      have h2 := congrArg (fun L => L c) (hd.unique hd0)
      simpa using h2
    -- the derivative lies in the range of ι
    obtain ⟨w₁, hw₁⟩ : fderiv ℝ ψ z₀ (fderiv ℝ g 0 c) ∈ Set.range ι :=
      hrangeψ ▸ ⟨fderiv ℝ g 0 c, rfl⟩
    have hDuc : fderiv ℝ u 0 c = ι (w₁ - c) := by
      rw [huder.fderiv, map_sub]
      simp [hw₁]
    have h3 := horthD (w₁ - c)
    rw [← hDuc, real_inner_self_eq_norm_sq] at h3
    simpa using h3
  -- neighbourhood of x in N is covered by ψ(V₀)
  obtain ⟨ε, hε, hballV₀⟩ := Metric.isOpen_iff.mp hV₀ z₀ hz₀V₀
  obtain ⟨δC, hδC, hδCprop⟩ := hinvc ε hε
  obtain ⟨ρW, hρW, hballW⟩ := Metric.isOpen_iff.mp hW x hxW
  obtain ⟨ρU, hρU, hballU⟩ := Metric.isOpen_iff.mp hU x hx.2
  set s := min (min ρW δC) ρU with hs
  have hspos : 0 < s := lt_min (lt_min hρW hδC) hρU
  have hNball : ∀ q ∈ N, dist q x < s → ∃ z ∈ V₀, ψ z = q := by
    intro q hq hqx
    have hqW : q ∈ W :=
      hballW (lt_of_lt_of_le hqx (le_trans (min_le_left _ _) (min_le_left _ _)))
    obtain ⟨z, hzV, rfl⟩ : q ∈ ψ '' V := by rw [hψimg]; exact ⟨hqW, hq⟩
    have h1 := hδCprop z hzV (lt_of_lt_of_le hqx (le_trans (min_le_left _ _) (min_le_right _ _)))
    exact ⟨z, hballV₀ h1, rfl⟩
  set r₁ := s / 4 with hr₁eq
  have hr₁ : 0 < r₁ := by positivity
  -- smallness of u and Du near 0
  have hucont : ContinuousAt u 0 := huC2.continuousOn.continuousAt (hO.mem_nhds h0O)
  have hDucont : ContinuousAt (fderiv ℝ u) 0 :=
    (huC2.continuousOn_fderiv_of_isOpen hO (by norm_num)).continuousAt (hO.mem_nhds h0O)
  obtain ⟨ρ₁, hρ₁, hρ₁prop⟩ := Metric.continuousAt_iff.mp hucont (r₁ / 2) (by positivity)
  obtain ⟨ρ₂, hρ₂, hρ₂prop⟩ := Metric.continuousAt_iff.mp hDucont 1 one_pos
  obtain ⟨ρ₃, hρ₃, hρ₃O⟩ := Metric.isOpen_iff.mp hO 0 h0O
  set δ₁ := min (min (min ρ₁ ρ₂) ρ₃) r₁ with hδ₁eq
  have hδ₁pos : 0 < δ₁ := lt_min (lt_min (lt_min hρ₁ hρ₂) hρ₃) hr₁
  have hδ₁ρ₁ : δ₁ ≤ ρ₁ := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδ₁ρ₂ : δ₁ ≤ ρ₂ := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδ₁ρ₃ : δ₁ ≤ ρ₃ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ₁r₁ : δ₁ ≤ r₁ := min_le_right _ _
  have hballO : ball (0 : Euclid d) δ₁ ⊆ O := (ball_subset_ball hδ₁ρ₃).trans hρ₃O
  refine ⟨u, δ₁, r₁, hδ₁pos, hr₁, ?_, hu0, hDu0, huC2.mono hballO, ?_, ?_⟩
  · -- closed ball inside U
    intro q hq
    apply hballU
    rw [mem_closedBall] at hq
    rw [mem_ball]
    have : s ≤ ρU := min_le_right _ _
    linarith
  · intro v hv
    have hvO := hballO hv
    have hv0 : dist v 0 < δ₁ := hv
    refine ⟨horthO v hvO, ?_, ?_, hmemO v hvO⟩
    · have h1 := hρ₂prop (lt_of_lt_of_le hv0 hδ₁ρ₂)
      rw [hDu0, dist_zero_right] at h1
      exact h1.le
    · have h1 := hρ₁prop (lt_of_lt_of_le hv0 hδ₁ρ₁)
      rw [hu0, dist_zero_right] at h1
      exact h1
  · intro v h hv hh horthh hq
    have hvO : v ∈ O := hballO (by rw [mem_ball, dist_zero_right]; exact hv)
    have hqx : dist (x + ι v + h) x < s := by
      rw [dist_eq_norm, show x + ι v + h - x = ι v + h by abel]
      calc ‖ι v + h‖ ≤ ‖ι v‖ + ‖h‖ := norm_add_le _ _
        _ = ‖v‖ + ‖h‖ := by rw [LinearIsometry.norm_map]
        _ < δ₁ + r₁ := add_lt_add hv hh
        _ ≤ r₁ + r₁ := by linarith
        _ < s := by rw [hr₁eq]; linarith
    obtain ⟨z, hzV₀, hψz⟩ := hNball _ hq hqx
    have hφz : φ z = v := by
      show ιs (ψ z - x) = v
      rw [hψz, show x + ι v + h - x = ι v + h by abel, map_add, hιsι, hιs0 h horthh, add_zero]
    have hgz : g v = z := by rw [← hφz]; exact (hgφ z hzV₀).2
    have h1 := hGu v
    rw [hgz, hψz] at h1
    exact (add_left_cancel h1).symm

## Key steps

1. Chart ψ at x with ψ(z₀) = x; the accepted dsmc_chart_tangentSpace_eq_range gives range Dψ(z₀) = T_xN = range ι and continuity of ψ⁻¹ at x.
2. φ := ι*(ψ − x) is C² on V with injective Dφ(z₀) = ι*Dψ(z₀); local_inverse_c2 gives V₀, O, g.
3. u(v) := ψ(g v) − x − ιv is C² on O, u(0) = 0, ι*u = 0 on O, and x + ιv + u(v) = ψ(g v) ∈ N.
4. Du(0)a is both orthogonal to range ι and in range ι, so Du(0) = 0.
5. Continuity of ψ⁻¹ puts N ∩ B_s(x) inside ψ(V₀); take δ₂ = s/4 and δ₁ small enough that ‖u‖ < δ₂/2, ‖Du‖ ≤ 1 and ball(0, δ₁) ⊆ O.
6. Uniqueness: q = x + ιv + h ∈ N near x equals ψ(z) with φ(z) = v, so z = g(v) and h = u(v).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `python3 scans of dag.json: accepted lean_statements containing tangentSpace, IsEmbeddedSubmanifold, IsOrientation, IsUnitOrientationOf, Matrix.det, .det, InjOn, fderiv; lean_name lookups chart_tangentSpace_eq_range_fderiv, dsmc_chart_tangentSpace_eq_range, dsmc_chart_inverse_continuity, dsmc_chart_range_subset_tangentSpace, dgoj_unitOrientation_of_injective, dgoj_exists_continuous_covector_eval, dgoj_exists_det_covector, dgoj_covector_eq_det_mul_of_mem_span, dgoj_det_adjoint_comp_eq_det_sq, dpf_exists_orthonormal_frame_det_gram, rsdic_unitOrientation_eq_or_eq_neg, dor_ims_unitOrientation_dual, dgcr_graph_orientation_jacobian, regcomp_unit_orientation_pairing, unit_orientations_common_unit_covector; collision check for the five codim1_rdo_gc_* names`
- `grep in snapshot mathlib: to_localInverse, toOpenPartialHomeomorph, contDiffAt_symm, isOpen_injective, isometryOfOrthonormal, coe_toBasis, constr_range, norm_image_sub_le, ContinuousAlternatingMap.apply`
- `grep -rln 'toOpenPartialHomeomorph|localInverse|InverseFunctionTheorem|contDiffAt_symm' simongmt (--include=*.lean); import lines of simongmt Chapter03/Rectifiable.lean and Chapter06/{Mass,CurrentLocalEquality,AffineCurrentPushforward}.lean`
- `lean -DautoImplicit=false /tmp/gc-split-check/Probe.lean and Probe2.lean (#print Covector, MultiVector; #check ContDiffAt.to_localInverse, HasStrictFDerivAt.toOpenPartialHomeomorph, OpenPartialHomeomorph.contDiffAt_symm, ContDiffAt.hasStrictFDerivAt', ContinuousLinearMap.isOpen_injective, ContDiffOn.continuousOn_fderiv_of_isOpen, Convex.isPreconnected, ContinuousAlternatingMap.map_update_smul, LinearMap.det_toMatrix)`
- `lean -DautoImplicit=false /tmp/gc-split-check/Types.lean (all 12 child types plus the parent assembly; #print axioms)`
- `lean -DautoImplicit=false /tmp/gc-split-check/{Prove124b,Prove1,Prove3,Prove5}.lean (new child proofs against stubs of their prerequisites)`
- `git show <commit>:GMT/Ch07/Submission.lean for fe95347b, 9c8432cb, 44afba4d, 8f402cb9, 05029c89, 93ec31ab, 73310ec9; git merge-base --is-ancestor 8f402cb9 44afba4d; lean -DautoImplicit=false /tmp/gc-split-check/FullCheck.lean with #print axioms`
- `python3: _recursive_lean.leaf_verification.check_source_delta on each new proof and the assembly; _recursive_lean.lean_contract.validate_lean_statement on all 12 types; acyclicity and byte-identity of reused types against dag.json`
- `sed -n of /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py (_decompose, _existing_lean_name_problem, _solve_children, _install_parent_supplied_child_handoff, _overlay_accepted_children, _accepted_checkpoint), __init__.py limits, swarm-project.json (max_depth 6, max_children 12, max_nodes 1000), verifier/gmt-compare.py header`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Basis/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-e6e07152bc/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-e6e07152bc/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ch-f0862c44ef/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ch-751a76913b/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-ea8963379b/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-orientati-ce923d2f7f/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-integer-combination-a1-orientation-sign-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-unit-or-24edf309fb/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/ConstancyNormalCharts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/gc-split-check/Types.lean`
- `/tmp/gc-split-check/Prove124b.lean`
- `/tmp/gc-split-check/Prove3.lean`
- `/tmp/gc-split-check/Prove5.lean`
- `/tmp/gc-split-check/FullCheck.lean`

Pins match:
- manifest project b4d606db and Mathlib 25730c7c equal workspace HEAD and .lake/packages/mathlib; simongmt is 2b366308;
- the snapshot Contract.lean, workspace Contract.lean and Submission.lean share sha256 e4148e7f9503aa28….

Library (import closure of GMT.Ch07.Submission):
- Present: HasStrictFDerivAt.toOpenPartialHomeomorph (InverseFunctionTheorem/FDeriv.lean:117), OpenPartialHomeomorph.contDiffAt_symm (ContDiff/Operations.lean:881), ContinuousLinearMap.isOpen_injective (Normed/Module/FiniteDimension.lean:263), LinearMap.isometryOfOrthonormal (InnerProductSpace/Orthonormal.lean:330), Module.Basis.constr_range (Basis/Defs.lean:547), ContinuousAlternatingMap.map_update_smul.
- Missing: ContDiffAt.to_localInverse (InverseFunctionTheorem/ContDiff.lean). #check reports an unknown constant; SimonGMT uses it only in Chapter08/ConstancyNormalCharts.lean, which the contract does not import. It also gives C² only at the image point, so the neighbourhood inverse function theorem becomes the new child local_inverse_c2.

DAG (683 nodes):
- 7 accepted declarations are reused with byte-identical frozen types and non-empty candidate commits: dsmc_chart_tangentSpace_eq_range 44afba4d, dsmc_chart_range_subset_tangentSpace 8f402cb9 (an ancestor of 44afba4d), dgoj_exists_continuous_covector_eval 05029c89, dpf_exists_orthonormal_frame_det_gram 93ec31ab, dgoj_covector_eq_det_mul_of_mem_span 73310ec9, rsdic_unitOrientation_eq_or_eq_neg fe95347b, dor_ims_unitOrientation_dual 9c8432cb.
- The runtime allows reusing accepted checkpoints with an identical type (_existing_lean_name_problem, _accepted_checkpoint) and merges prerequisite candidate commits (_overlay_accepted_children).
- The five codim1_rdo_gc_* names occur nowhere in dag.json.
- No accepted node gives a neighbourhood C² inverse function theorem, the Gram-matrix form of the unit-orientation lemma (dgoj_unitOrientation_of_injective uses det(F*∘F)), or the orientation normal form of step 1.

Lean:
- All 12 child types elaborate after import GMT.Ch07.Submission in the contract scope.
- FullCheck.lean compiles; it contains the frozen Submission, the accepted reused proofs taken from their candidate commits, the 5 new child proofs and the parent assembly.
- #print axioms for Submission.codim1_rdo_graph_chart and all five new children gives [propext, Classical.choice, Quot.sound].
- Each new proof and the assembly pass check_source_delta, and every type passes validate_lean_statement.
