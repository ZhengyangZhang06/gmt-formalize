# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.boundary_im-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.boundary_im-a1.slice_localization-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Steps 1–5 and the first half of Step 10 (Simon Ch. 6, 4.5(1)–(2): for a Lipschitz f, T⌞{f < t} has boundary of finite mass for L¹-a.e. t; 6.2, general case: cut T at such a level so that the piece has finite boundary mass). Uses the siblings lcmp_imRep_measure_restrict (key imrep_restrict) and lcmp_massOn_le_of_vanish_off_compact (key vanish_off_compact), both comparator-accepted declarations reused at their frozen types.
Notation: |α| = covectorEuclideanNorm α. M_W(X) = X.massOn W is the supremum of ofReal X(ω) over the ω ∈ 𝒟^k(U) with tsupport ω ⊆ W and |ω(x)| ≤ 1 for all x ("admissible for M_W"). M(X) = M_U(X) (GeometricCurrentOn.mass). B_t(x₀) = ball x₀ t, H = μHE[d + 1], and ξ(ω) denotes x ↦ ξ(x)(ω(x)).
Change from the supplied text: step 5 takes the good radius from the integrated bound of (SL), not from the measure-convergence tool (MM) of cbr_measure_convergence_tools applied to the constant sequence μ_j = μ. The integrated bound gives a radius directly and needs no measurability of t ↦ M_G(∂A_t − B_t).
0. Mass is bounded by a representing measure (Step 0(iii) of the parent proof). Let k ∈ ℕ, X ∈ 𝒟_k(U), ν a measure on ℝ^P and ζ : ℝ^P → Λ_k(ℝ^P). Assume |ζ(x)(α)| ≤ |α| for ν-a.e. x and all k-covectors α, and X(ω) = ∫ ζ(ω) dν for every ω ∈ 𝒟^k(U). Then M_W(X) ≤ ν(W) for every W ⊆ ℝ^P. Proof: let ω be admissible for M_W and g := ζ(ω). Then ofReal(X(ω)) = ofReal(∫ g dν) ≤ ‖∫ g dν‖ₑ ≤ ∫⁻ ‖g‖ₑ dν (enorm_integral_le_lintegral_enorm). This holds without integrability, because the Bochner integral of a non-integrable function is 0. Now take ν-a.e. x. If x ∈ W, then ‖g(x)‖ₑ = ofReal|ζ(x)(ω(x))| ≤ ofReal|ω(x)| ≤ 1. If x ∉ W, then x ∉ tsupport ω, so ω(x) = 0 and g(x) = ζ(x)(0) = 0. Hence ‖g‖ₑ ≤ 1_W ν-a.e., and ∫⁻ ‖g‖ₑ dν ≤ ∫⁻ 1_W dν ≤ ν(W) (lintegral_mono_ae, lintegral_indicator_one_le; W need not be measurable). Taking the supremum over admissible ω proves the claim.
1. Representation of R. R is integer multiplicity, so some IMRep R₀ = (M, θ, ξ) of U represents R: R(ω) = ∫_M θ ξ(ω) dH for ω ∈ 𝒟^{d+1}(U). Put μ := R₀.measure = (H⌞M).withDensity θ. By lcmp_imRep_measure_restrict:
 (a) μ ≪ H⌞M;
 (b) ξ is μ-a.e. strongly measurable;
 (c) R′.action(ω) = ∫_E ξ(ω) dμ for every Borel E ⊆ ℝ^P, every IMRep R′ of U with carrier M ∩ E, multiplicity θ and orientation ξ, and every (d+1)-form ω.
 μ is finite on compact subsets of U. Let K ⊆ U be compact. K is closed, hence Borel, so μ(K) = ∫⁻_K θ d(H⌞M) = ∫⁻_{M∩K} θ dH (withDensity_apply, Measure.restrict_restrict). The IMRep field locallyIntegrable_mult makes this finite.
 By (IMC)(d), |ξ(x)(α)| ≤ |α| for all α and H⌞M-a.e. x; by (a) this also holds for μ-a.e. x (AbsolutelyContinuous.ae_le).
 Finally take E := ℝ^P and R′ := R₀ in (c); this is allowed because the carrier of R₀ is M = M ∩ ℝ^P. It gives R₀.action(ω) = ∫_{ℝ^P} ξ(ω) dμ = ∫ ξ(ω) dμ (Measure.restrict_univ). Hence R(ω) = ∫ ξ(ω) dμ for every ω ∈ 𝒟^{d+1}(U).
2. Representation of ∂R. ∂R ∈ 𝒟_d(U), and M_W(∂R) < ∞ for every open W with compact closure in U. So (REP) gives a measure μ' and ξ' : ℝ^P → Λ_d(ℝ^P) such that:
 - μ'(K) < ∞ for every compact K ⊆ U;
 - ξ' is μ'-a.e. strongly measurable;
 - |ξ'(x)(α)| ≤ |α| for all x and α;
 - ∂R(η) = ∫ ξ'(η) dμ' for every η ∈ 𝒟^d(U).
3. A radius r₀. U is open and x₀ ∈ U, so there is ε > 0 with B_ε(x₀) ⊆ U (Metric.isOpen_iff). Put r₀ := ε/2 > 0. Then closedBall(x₀, r₀) ⊆ B_ε(x₀) ⊆ U, and closedBall(x₀, r₀) is compact. By steps 1–2, μ(closedBall(x₀, r₀)) < ∞ and μ'(closedBall(x₀, r₀)) < ∞.
4. Slicing. Let f(x) := dist(x, x₀) = |x − x₀|. It is 1-Lipschitz (LipschitzWith.dist_left), {x : f(x) < t} = B_t(x₀) and {x : f(x) = t} = sphere(x₀, t). Apply (SL) with k := d, T := R, the pairs (μ, ξ) and (μ', ξ') of steps 1–2, f and L := 1. Its hypotheses hold:
 - U is open;
 - μ and μ' are finite on compact subsets of U;
 - ξ and ξ' are a.e. strongly measurable;
 - |ξ| ≤ |·| μ-a.e. (step 1), and |ξ'| ≤ |·| everywhere, hence μ'-a.e.;
 - R and ∂R are represented as required.
 This gives currents A_t ∈ 𝒟_{d+1}(U) and B_t ∈ 𝒟_d(U) (t ∈ ℝ) with:
 (i) A_t(ω) = ∫_{B_t(x₀)} ξ(ω) dμ for ω ∈ 𝒟^{d+1}(U);
 (ii) B_t(η) = ∫_{B_t(x₀)} ξ'(η) dμ' for η ∈ 𝒟^d(U);
 (iii) ∂A_t(η) = B_t(η) whenever tsupport η is disjoint from sphere(x₀, t);
 (iv) ∫⁻_{t∈(a,b)} M_W(∂A_t − B_t) dt ≤ μ(W ∩ {a < f < b}) for every open W and all a, b ∈ ℝ (as L = 1).
5. A good radius. Let G := B_{r₀}(x₀) and apply (iv) with W := G, a := 0, b := r₀. The right side is at most μ(closedBall(x₀, r₀)) < ∞, because G ∩ {0 < f < r₀} ⊆ G ⊆ closedBall(x₀, r₀). Suppose M_G(∂A_t − B_t) = ∞ for every t ∈ (0, r₀). Then the left side is ∫⁻_{(0,r₀)} ∞ dt = ∞·L¹((0, r₀)) = ∞·r₀ = ∞ (setLIntegral_congr_fun on the measurable set (0, r₀), lintegral_const, Real.volume_Ioo, r₀ > 0). This is a contradiction. Hence there is r ∈ (0, r₀) with M_G(Z) < ∞, where Z := ∂A_r − B_r ∈ 𝒟_d(U).
6. Total mass of Z. Let η ∈ 𝒟^d(U) have tsupport η disjoint from sphere(x₀, r). Then Z(η) = ∂A_r(η) − B_r(η) = 0 by (iii). The sphere is compact (isCompact_sphere) and lies in the open set G, because r < r₀. Apply lcmp_massOn_le_of_vanish_off_compact with C := sphere(x₀, r), V := G, X := Z and the arbitrary set U. It gives M(Z) = M_U(Z) ≤ M_G(Z) < ∞.
7. Mass of B_r. By (ii), B_r(η) = ∫ ξ'(η) d(μ'⌞B_r(x₀)) for η ∈ 𝒟^d(U). The bound |ξ'(x)(α)| ≤ |α| holds everywhere, hence μ'⌞B_r(x₀)-a.e. Step 0 with k := d, ν := μ'⌞B_r(x₀), ζ := ξ' and W := U gives M(B_r) ≤ (μ'⌞B_r(x₀))(U) ≤ μ'(B_r(x₀)) ≤ μ'(closedBall(x₀, r₀)) < ∞.
8. Mass of ∂A_r. For every η ∈ 𝒟^d(U), ∂A_r(η) = B_r(η) + Z(η), since Z(η) = ∂A_r(η) − B_r(η). Let η be admissible for M_U. Then ofReal(∂A_r(η)) ≤ ofReal(B_r(η)) + ofReal(Z(η)) (ENNReal.ofReal_add_le) ≤ M_U(B_r) + M_U(Z) (le_massOn). Taking the supremum, M(∂A_r) ≤ M(B_r) + M(Z), which is finite by steps 6–7.
9. A_r is represented by an IMRep with carrier in B_r(x₀). Apply (IMC)(b) to R₀ and E := B_r(x₀), which is open and hence Borel. It gives an IMRep R'' of U with carrier M ∩ B_r(x₀), multiplicity θ and orientation ξ. Let ω ∈ 𝒟^{d+1}(U). Step 1(c) with E := B_r(x₀) and R′ := R'' gives R''.action(ω) = ∫_{B_r(x₀)} ξ(ω) dμ, and this is A_r(ω) by (i). So R'' represents R' := A_r, and its carrier M ∩ B_r(x₀) is contained in B_r(x₀).
10. Mass of R'. By (i), A_r(ω) = ∫ ξ(ω) d(μ⌞B_r(x₀)). The bound |ξ(x)(α)| ≤ |α| holds μ-a.e. (step 1), hence μ⌞B_r(x₀)-a.e. (ae_restrict_of_ae). Step 0 with k := d + 1, ν := μ⌞B_r(x₀) and W := U gives M(R') ≤ (μ⌞B_r(x₀))(U) ≤ μ(B_r(x₀)) ≤ μ(closedBall(x₀, r₀)) < ∞.
11. Agreement with ∂R. Let η ∈ 𝒟^d(U) with tsupport η ⊆ B_r(x₀). Points of B_r(x₀) have distance < r from x₀, so tsupport η is disjoint from sphere(x₀, r). Hence ∂R'(η) = ∂A_r(η) = B_r(η) by (iii), and B_r(η) = ∫_{B_r(x₀)} ξ'(η) dμ' by (ii). This equals ∫ ξ'(η) dμ', because the integrand vanishes off B_r(x₀): there x ∉ tsupport η, so η(x) = 0 and ξ'(x)(0) = 0 (setIntegral_eq_integral_of_forall_compl_eq_zero). By step 2 it equals ∂R(η).
12. Conclusion. We have r > 0 and closedBall(x₀, r) ⊆ closedBall(x₀, r₀) ⊆ U, as r < r₀. Take R' = A_r and R''. Then R'' represents R' with carrier ⊆ B_r(x₀) (step 9), M(R') < ∞ (step 10) and M(∂R') < ∞ (step 8). Also ∂R'(η) = ∂R(η) for every η ∈ 𝒟^d(U) supported in B_r(x₀) (step 11). ∎

Lean note (verified realization of the numbered proof above; not part of the proof). The following tactic proof of `Submission.cbr_bim_slice_localization` compiles against the frozen contract (Lean v4.35.0-rc3, Mathlib 25730c7c, SimonGMT 2b366308). It is placed after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's `open` commands, with the reused sibling declarations `Submission.lcmp_imRep_measure_restrict` and `Submission.lcmp_massOn_le_of_vanish_off_compact` in scope. `#print axioms` reports only propext, Classical.choice and Quot.sound, and `exact Submission.cbr_bim_slice_localization` closes the frozen type in the comparator scope. Do not open the ContDiff scope, whose notation makes ω a token; smoothness is written ContDiff ℝ (⊤ : ℕ∞).
```lean
  intro hREP hIMCb hIMCd hSL P d U R x₀ hU hRim hbd hx₀
  -- the local mass of a current is bounded by any representing measure
  have hmassle : ∀ {k : ℕ} (X : GeometricCurrentOn U k) (ν : Measure (Euclid P))
      (ζ : Euclid P → MultiVector P k),
      (∀ᵐ x ∂ν, ∀ α : Covector (Euclid P) k, |ζ x α| ≤ covectorEuclideanNorm α) →
      (∀ ω : TestFormOn U k, X ω = ∫ x, ζ x ((ω : DifferentialForm (Euclid P) k) x) ∂ν) →
      ∀ W : Set (Euclid P), X.massOn W ≤ ν W := by
    intro k X ν ζ hζ hrep W
    apply sSup_le
    rintro _ ⟨ω, ⟨hsupp, hnorm⟩, rfl⟩
    change ENNReal.ofReal (X ω) ≤ ν W
    rw [hrep ω]
    calc ENNReal.ofReal (∫ x, ζ x ((ω : DifferentialForm (Euclid P) k) x) ∂ν)
        ≤ ‖∫ x, ζ x ((ω : DifferentialForm (Euclid P) k) x) ∂ν‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ x, ‖ζ x ((ω : DifferentialForm (Euclid P) k) x)‖ₑ ∂ν :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x, W.indicator 1 x ∂ν := by
          apply lintegral_mono_ae
          filter_upwards [hζ] with x hx
          by_cases hxW : x ∈ W
          · rw [indicator_of_mem hxW, Pi.one_apply, Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_le_one.mpr ((hx _).trans (hnorm x))
          · have : (ω : DifferentialForm (Euclid P) k) x = 0 :=
              image_eq_zero_of_notMem_tsupport (fun h => hxW (hsupp h))
            simp [this]
      _ ≤ ν W := lintegral_indicator_one_le W
  -- the representation of R by the weight of an IMRep
  obtain ⟨R₀, hR₀⟩ := hRim
  obtain ⟨hac, haesm, hrestr⟩ := Submission.lcmp_imRep_measure_restrict P (d + 1) U R₀
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → R₀.measure K < ∞ := by
    intro K hK hKU
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact lt_top_iff_ne_top.mpr (R₀.locallyIntegrable_mult K hK hKU)
  have hξb : ∀ᵐ x ∂R₀.measure, ∀ α : Covector (Euclid P) (d + 1),
      |R₀.orient x α| ≤ covectorEuclideanNorm α :=
    hac.ae_le (hIMCd P (d + 1) U R₀)
  have hRrep : ∀ ω : TestFormOn U (d + 1),
      R ω = ∫ x, R₀.orient x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂R₀.measure := by
    intro ω
    have h := (hrestr univ R₀ MeasurableSet.univ (inter_univ _).symm rfl rfl).2
      (ω : DifferentialForm (Euclid P) (d + 1))
    rw [Measure.restrict_univ] at h
    rw [hR₀ ω, h]
  -- the representation of ∂R
  obtain ⟨μ', ξ', -, hfin', -, haesm', hξ'b, hbrep, -⟩ := hREP P d U R.boundary hU hbd
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  have hr₀pos : 0 < ε / 2 := by positivity
  have hcb₀ : closedBall x₀ (ε / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hεU
  have hfL : LipschitzWith 1 (fun x : Euclid P => dist x x₀) := LipschitzWith.dist_left x₀
  -- slicing by the distance from x₀
  obtain ⟨A, B, hA, hB, hAB, -, hint5⟩ := hSL P d U R R₀.measure μ' R₀.orient ξ'
    (fun x => dist x x₀) 1 hU hfin hfin' haesm haesm' hξb (Eventually.of_forall hξ'b) hRrep hbrep hfL
  have hfinball : R₀.measure (closedBall x₀ (ε / 2)) < ∞ := hfin _ (isCompact_closedBall _ _) hcb₀
  have hfinball' : μ' (closedBall x₀ (ε / 2)) < ∞ := hfin' _ (isCompact_closedBall _ _) hcb₀
  -- a good radius
  obtain ⟨r, hr, hZr⟩ : ∃ r ∈ Ioo 0 (ε / 2),
      ((A r).boundary - B r).massOn (ball x₀ (ε / 2)) < ∞ := by
    by_contra hcon
    push Not at hcon
    have hlint := hint5 (ball x₀ (ε / 2)) 0 (ε / 2) isOpen_ball
    have htop : ∫⁻ t in Ioo 0 (ε / 2), ((A t).boundary - B t).massOn (ball x₀ (ε / 2)) = ∞ := by
      rw [setLIntegral_congr_fun measurableSet_Ioo (fun t ht => top_le_iff.mp (hcon t ht))]
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero]
      exact ENNReal.top_mul (by simpa using hr₀pos)
    rw [htop, ENNReal.coe_one, one_mul] at hlint
    have hle : R₀.measure (ball x₀ (ε / 2) ∩ {x | 0 < dist x x₀ ∧ dist x x₀ < ε / 2}) < ∞ :=
      lt_of_le_of_lt (measure_mono (inter_subset_left.trans ball_subset_closedBall)) hfinball
    exact absurd (lt_of_le_of_lt hlint hle) (lt_irrefl _)
  set Z := (A r).boundary - B r with hZ
  have hZvan : ∀ η : TestFormOn U d,
      Disjoint (tsupport (η : DifferentialForm (Euclid P) d)) (sphere x₀ r) → Z η = 0 := by
    intro η hη
    have := hAB r η hη
    change (A r).boundary η - B r η = 0
    rw [this, sub_self]
  have hsph : sphere x₀ r ⊆ ball x₀ (ε / 2) := fun y hy => by
    rw [mem_sphere] at hy; rw [mem_ball, hy]; exact hr.2
  -- the slice has finite total mass
  have hZU : Z.massOn U < ∞ :=
    lt_of_le_of_lt (Submission.lcmp_massOn_le_of_vanish_off_compact P d U (ball x₀ (ε / 2))
      (sphere x₀ r) Z (isCompact_sphere _ _) isOpen_ball hsph hZvan U) hZr
  have hBU : (B r).massOn U < ∞ := by
    refine lt_of_le_of_lt (hmassle (B r) (μ'.restrict (ball x₀ r)) ξ'
      (ae_restrict_of_ae (Eventually.of_forall hξ'b)) (fun η => hB r η) U) ?_
    refine lt_of_le_of_lt ?_ hfinball'
    calc μ'.restrict (ball x₀ r) U ≤ μ'.restrict (ball x₀ r) univ := measure_mono (subset_univ _)
      _ = μ' (ball x₀ r) := Measure.restrict_apply_univ _
      _ ≤ μ' (closedBall x₀ (ε / 2)) :=
          measure_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall hr.2.le))
  have hAbU : (A r).boundary.massOn U < ∞ := by
    refine lt_of_le_of_lt (b := (B r).massOn U + Z.massOn U) ?_ (ENNReal.add_lt_top.mpr ⟨hBU, hZU⟩)
    apply sSup_le
    rintro _ ⟨η, hη, rfl⟩
    have hsplit : (A r).boundary η = B r η + Z η := by
      change (A r).boundary η = B r η + ((A r).boundary η - B r η); ring
    change ENNReal.ofReal ((A r).boundary η) ≤ _
    rw [hsplit]
    exact ENNReal.ofReal_add_le.trans (add_le_add ((B r).le_massOn hη) (Z.le_massOn hη))
  -- R' := A r = R⌞B_r(x₀) is represented by the restricted IMRep
  obtain ⟨A', Rr, -, hcar, hmult, hor⟩ := hIMCb P (d + 1) U R₀ (ball x₀ r) hU measurableSet_ball
  have hRrA : Rr.Represents (A r) := by
    intro ω
    rw [hA r ω]
    exact ((hrestr (ball x₀ r) Rr measurableSet_ball hcar hmult hor).2 _).symm
  have hAU : (A r).massOn U < ∞ := by
    refine lt_of_le_of_lt (hmassle (A r) (R₀.measure.restrict (ball x₀ r)) R₀.orient
      (ae_restrict_of_ae hξb) (fun ω => hA r ω) U) ?_
    refine lt_of_le_of_lt ?_ hfinball
    calc R₀.measure.restrict (ball x₀ r) U ≤ R₀.measure.restrict (ball x₀ r) univ :=
          measure_mono (subset_univ _)
      _ = R₀.measure (ball x₀ r) := Measure.restrict_apply_univ _
      _ ≤ R₀.measure (closedBall x₀ (ε / 2)) :=
          measure_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall hr.2.le))
  refine ⟨r, hr.1, (closedBall_subset_closedBall hr.2.le).trans hcb₀, A r, Rr, hRrA, ?_, hAU, hAbU, ?_⟩
  · rw [hcar]; exact inter_subset_right
  · intro η hη
    have hdisj : Disjoint (tsupport (η : DifferentialForm (Euclid P) d)) (sphere x₀ r) := by
      refine Set.disjoint_left.mpr fun y hy hys => ?_
      have h1 := hη hy
      rw [mem_ball] at h1; rw [mem_sphere] at hys
      linarith
    rw [hAB r η hdisj, hB r η, hbrep η]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have : (η : DifferentialForm (Euclid P) d) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx (hη h))
    rw [this, map_zero]
```

## Key steps

1. Bound local masses by representing measures (step 0); represent R by μ = θH^{d+1}⌞M and ξ (lcmp_imRep_measure_restrict, local integrability of θ, (IMC)(d)), and ∂R by (μ', ξ') from (REP).
2. Slice by f = |· − x₀| with (SL), L = 1; the integrated bound on (0, r₀) gives r ∈ (0, r₀) with M_{B_{r₀}(x₀)}(∂A_r − B_r) < ∞.
3. ∂A_r − B_r vanishes off the compact sphere {f = r} ⊆ B_{r₀}(x₀), so its total mass is finite (lcmp_massOn_le_of_vanish_off_compact); M(B_r) ≤ μ'(B_r(x₀)) < ∞, hence M(∂A_r) < ∞.
4. (IMC)(b) with E = B_r(x₀) and lcmp_imRep_measure_restrict give an IMRep with carrier M ∩ B_r(x₀) representing R' := A_r, and M(R') ≤ μ(B_r(x₀)) < ∞.
5. For η supported in B_r(x₀): ∂R'(η) = B_r(η) = ∫ξ'(η)dμ' = ∂R(η).

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b = workspace HEAD, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp snapshot project/GMT/Ch07/Contract.lean with workspace GMT/Ch07/Contract.lean and Submission.lean (identical)`
- `rg -n 'cbr_bim_|cbr_boundary_isIntegerMultiplicity|rsd_mw_tfa_norm_props|cmr_abs_apply_le_massOn|lcmp_massOn_le_of_vanish_off_compact|lcmp_imRep_measure_restrict|dtc_extend_by_zero' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT (no match)`
- `rg -n in /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib for: 'theorem enorm_integral_le_lintegral_enorm', 'theorem lintegral_indicator_one_le', 'theorem setIntegral_eq_integral_of_forall_compl_eq_zero', 'theorem setLIntegral_congr_fun', 'theorem withDensity_apply ', 'theorem restrict_restrict (hs', 'protected theorem dist_left', 'theorem tendsto_pow_atTop_nhds_zero_of_lt_one', 'lemma squeeze_zero', 'image_eq_zero_of_notMem_tsupport', 'AbsolutelyContinuous.ae_le', 'theorem lintegral_const', 'theorem isCompact_sphere', 'theorem ae_restrict_of_ae ', 'theorem volume_Ioo', 'theorem tsupport_smul_subset_right', 'theorem withDensity_absolutelyContinuous', 'theorem integral_withDensity_eq_integral_smul', 'theorem restrict_withDensity'`
- `sed/grep of SimonGMT Chapter06 Currents.lean, Mass.lean, CurrentLocalEquality.lean (GeometricCurrentOn, boundary, boundary_boundary, WeaklyConvergesOn.boundary, massOn, mass, le_massOn, massOn_mono, restrictDomain, testFormOnInclusion, zeroRegion, support, exteriorDerivativeTestOn, tsupport_exteriorDerivative_subset)`
- `python3 scan of dag.json (1033 nodes): status, candidate_commit and frozen lean_statement of the five reused names and of the six dependency theorems, cbr_isIntegerMultiplicity_of_local and cbr_measure_convergence_tools; uniqueness of every proposed name; identical/near-identical types for the three new statements`
- `git show <commit>:GMT/Ch07/Submission.lean for f492ba4a00, 7a706164ba, a3cc98d1f0, ae810e9b4c, 2527748da7`
- `grep/sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_decompose, _solve_children node bound and in-memory audit, _existing_lean_name_problem, _accepted_checkpoint, _install_parent_supplied_child_handoff, _reference_use_problem) and store.py ensure; max_nodes history in .humanize/swarm-configs`
- `python3 -I build3.py: verifier/lean_contract.py validate_lean_statement on the 8 statements; verifier/gmt-compare.py contract_scope + child_modules(contract) challenge files`
- `lake env lean /tmp/bim-decomp-r3/lean/AllChallenges.lean (8 challenges elaborate), All.lean (reused accepted proofs + 3 new Lean notes + parent assembly), Hyp.lean (#print axioms CbrCheck_assembly: propext, Classical.choice, Quot.sound), Sol.lean (exact Submission.X closes all 8 challenges)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/VectorMeasure/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/AbsolutelyContinuous.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/ProperSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-10c568d35f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-10c568d35f/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-10c568d35f/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`

The snapshot (project b4d606d = workspace HEAD, Mathlib 25730c7c) has a Contract.lean byte-identical to the workspace Contract.lean and Submission.lean. No proposed or reused name occurs in the snapshot project. The five reused names each belong to exactly one DAG node, with status accepted, a candidate commit and a frozen type byte-identical to the proposed lean_statement. The three new cbr_bim_* names are unreserved among the 1033 DAG nodes, and no DAG node has an identical type. Every Mathlib lemma used by the child proofs exists in the snapshot (squeeze_zero is a lemma in Topology/MetricSpace/Pseudo/Lemmas.lean; AbsolutelyContinuous.ae_le is an alias in AbsolutelyContinuous.lean). Every SimonGMT declaration used exists in the pinned package. SimonGMT Chapter06 has no slicing, deformation or closure theorem, which justifies the hypotheses-as-arguments form and the split. All eight statements pass the verifier's lexical check and elaborate as comparator challenges. The reused accepted proofs, the three new Lean notes and the parent assembly compile together. A hypothesis-only assembly proves the exact frozen parent type from the eight children and the frozen type of the existing dependency cbr_isIntegerMultiplicity_of_local, with axioms propext, Classical.choice and Quot.sound only.
