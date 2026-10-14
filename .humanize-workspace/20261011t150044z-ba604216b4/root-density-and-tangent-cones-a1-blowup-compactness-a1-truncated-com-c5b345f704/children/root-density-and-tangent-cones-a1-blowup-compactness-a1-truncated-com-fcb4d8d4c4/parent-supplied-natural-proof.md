# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.boundary_im-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.boundary_im-a1.slice_localization-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: supplied proof, steps 1–3 and the first half of step 7 (Simon Ch. 6: slices 4.6–4.10, chapter-06.txt lines 1339–1377; and the general case of the proof of 6.2, lines 1986–1993, which applies 4.5(1)–(2) (lines 1235–1243) to cut an integer multiplicity current at a good level: "For L¹-a.e. λ > 0, 4.5 implies that T_λ ≡ T⌞{φ > λ} is such that M(∂T_λ) < ∞"). Uses the reused siblings lcmp_imRep_measure_restrict (key imrep_restrict) and lcmp_massOn_le_of_vanish_off_compact (key vanish_off_compact), comparator-accepted declarations taken at their frozen types.
Notation. |α| = covectorEuclideanNorm α. For X ∈ 𝒟_k(U) and W ⊆ ℝ^P, M_W(X) = X.massOn W is the supremum of ofReal X(ω) over the ω ∈ 𝒟^k(U) with tsupport ω ⊆ W and |ω(x)| ≤ 1 for all x ("admissible for M_W"); M(X) = M_U(X) (GeometricCurrentOn.mass). B_t(x₀) = ball x₀ t, H = μHE[d + 1], and ξ(ω) denotes x ↦ ξ(x)(ω(x)). spt X = U ∖ Z(X), where the zero region Z(X) is the union of the open sets W with closure(W) compact, closure(W) ⊆ U and X(ω) = 0 for every ω ∈ 𝒟^k(U) with tsupport ω ⊆ W (GeometricCurrentOn.support, zeroRegion, VanishesOn).
Departure from the supplied text: step 5 takes the good radius from the integrated slice bound, item (v) of (SL) below, which is the general-current form 4.10 (lines 1374–1377) of Simon's 4.5(1); Simon's general case of 6.2 obtains its cutting levels from 4.5 in the same way ("for L¹-a.e. λ"). The supplied text instead applies (MM) of the sibling foundations to the constant sequence μ_j = μ. That route also works: (MM) gives a measurable g with M_G(Z_t) ≤ g(t) for a.e. t ∈ (0, r₀) and ∫_{(0,r₀)} g ≤ μ(G ∩ {0 < f < r₀}) < ∞, so g < ∞ a.e. and a good radius exists. The integrated bound gives the radius in one step and is the shorter route; step 5 needs no measurability of t ↦ M_G(Z_t). The cut-off of the supplied step 2 ("a cut-off equal to 1 near the sphere {f = r} shows M(Z_r) ≤ M_G(Z_r)") is the reused lcmp_massOn_le_of_vanish_off_compact (step 6 below). Steps 9–11 give the conclusions of the supplied step 3 (R' IM with carrier M ∩ B_r(x₀), spt R' ⊆ B̄_r(x₀)).
0. (Mass is bounded by a representing measure.) Let k ∈ ℕ, X ∈ 𝒟_k(U), ν a measure on ℝ^P and ζ : ℝ^P → Λ_k(ℝ^P). Assume |ζ(x)(α)| ≤ |α| for ν-a.e. x and all k-covectors α, and X(ω) = ∫ ζ(ω) dν for every ω ∈ 𝒟^k(U). Then M_W(X) ≤ ν(W) for every W ⊆ ℝ^P. Proof: let ω be admissible for M_W and g := ζ(ω). Then ofReal(X(ω)) = ofReal(∫ g dν) ≤ ‖∫ g dν‖ₑ ≤ ∫⁻ ‖g‖ₑ dν (enorm_integral_le_lintegral_enorm; this holds without integrability, because the Bochner integral of a non-integrable function is 0). For ν-a.e. x: if x ∈ W, then ‖g(x)‖ₑ = ofReal|ζ(x)(ω(x))| ≤ ofReal|ω(x)| ≤ 1; if x ∉ W, then x ∉ tsupport ω, so ω(x) = 0 and g(x) = ζ(x)(0) = 0. Hence ‖g‖ₑ ≤ 1_W ν-a.e., and ∫⁻ ‖g‖ₑ dν ≤ ∫⁻ 1_W dν ≤ ν(W) (lintegral_mono_ae, lintegral_indicator_one_le; W need not be measurable). Taking the supremum over admissible ω proves the claim.
1. (Representation of R.) R is integer multiplicity, so some IMRep R₀ = (M, θ, ξ) of U represents R: R(ω) = ∫_M θ ξ(ω) dH for ω ∈ 𝒟^{d+1}(U). Put μ := R₀.measure = (H⌞M).withDensity θ. By lcmp_imRep_measure_restrict: (a) μ ≪ H⌞M; (b) ξ is μ-a.e. strongly measurable; (c) R′.action(ω) = ∫_E ξ(ω) dμ for every Borel E ⊆ ℝ^P, every IMRep R′ of U with carrier M ∩ E, multiplicity θ and orientation ξ, and every (d+1)-form ω. μ is finite on compact subsets of U: if K ⊆ U is compact, then K is closed, hence Borel, and μ(K) = ∫⁻_K θ d(H⌞M) = ∫⁻_{M∩K} θ dH (withDensity_apply, Measure.restrict_restrict), which is finite by the IMRep field locallyIntegrable_mult. By (IMC)(d), |ξ(x)(α)| ≤ |α| for all α and H⌞M-a.e. x; by (a) this also holds for μ-a.e. x (AbsolutelyContinuous.ae_le). Finally take E := ℝ^P and R′ := R₀ in (c) (allowed, as the carrier of R₀ is M = M ∩ ℝ^P): R₀.action(ω) = ∫ ξ(ω) dμ (Measure.restrict_univ). Hence R(ω) = ∫ ξ(ω) dμ for every ω ∈ 𝒟^{d+1}(U).
2. (Representation of ∂R.) ∂R ∈ 𝒟_d(U), U is open and M_W(∂R) < ∞ for every open W ⊂⊂ U, so (REP) gives a measure μ' and ξ' : ℝ^P → Λ_d(ℝ^P) such that μ'(K) < ∞ for every compact K ⊆ U, ξ' is μ'-a.e. strongly measurable, |ξ'(x)(α)| ≤ |α| for all x and α, and ∂R(η) = ∫ ξ'(η) dμ' for every η ∈ 𝒟^d(U).
3. (A radius r₀.) U is open and x₀ ∈ U, so there is ε > 0 with B_ε(x₀) ⊆ U (Metric.isOpen_iff). Put r₀ := ε/2 > 0. Then closedBall(x₀, r₀) ⊆ B_ε(x₀) ⊆ U and closedBall(x₀, r₀) is compact, so μ(closedBall(x₀, r₀)) < ∞ and μ'(closedBall(x₀, r₀)) < ∞ by steps 1–2.
4. (Slicing.) Let f(x) := dist(x, x₀) = |x − x₀|. It is 1-Lipschitz (LipschitzWith.dist_left), {x : f(x) < t} = B_t(x₀) and {x : f(x) = t} = sphere(x₀, t). Apply (SL) with k := d, T := R, the pairs (μ, ξ) and (μ', ξ') of steps 1–2, f and L := 1. Its hypotheses hold: U is open; μ and μ' are finite on compact subsets of U; ξ and ξ' are a.e. strongly measurable; |ξ| ≤ |·| μ-a.e. (step 1) and |ξ'| ≤ |·| everywhere, hence μ'-a.e.; R and ∂R are represented as required. This gives currents A_t ∈ 𝒟_{d+1}(U) and B_t ∈ 𝒟_d(U) (t ∈ ℝ) with: (i) A_t(ω) = ∫_{B_t(x₀)} ξ(ω) dμ for ω ∈ 𝒟^{d+1}(U); (ii) B_t(η) = ∫_{B_t(x₀)} ξ'(η) dμ' for η ∈ 𝒟^d(U); (iii) ∂A_t(η) = B_t(η) whenever tsupport η is disjoint from sphere(x₀, t); (iv) the pointwise bound M_W(∂A_t − B_t) ≤ liminf_{h↓0} h⁻¹μ(W ∩ {t − h < f < t}) for open W (not used); (v) ∫⁻_{t∈(a,b)} M_W(∂A_t − B_t) dt ≤ μ(W ∩ {a < f < b}) for every open W and all a, b ∈ ℝ (as L = 1).
5. (A good radius.) Let G := B_{r₀}(x₀) and apply (v) with W := G, a := 0, b := r₀. The right side is at most μ(closedBall(x₀, r₀)) < ∞, because G ∩ {0 < f < r₀} ⊆ G ⊆ closedBall(x₀, r₀). Suppose M_G(∂A_t − B_t) = ∞ for every t ∈ (0, r₀). Then the left side is ∫⁻_{(0,r₀)} ∞ dt = ∞·L¹((0, r₀)) = ∞·r₀ = ∞ (setLIntegral_congr_fun on the measurable set (0, r₀), lintegral_const, Real.volume_Ioo, r₀ > 0), a contradiction. Hence there is r ∈ (0, r₀) with M_G(Z) < ∞, where Z := ∂A_r − B_r ∈ 𝒟_d(U).
6. (Total mass of Z.) Let η ∈ 𝒟^d(U) have tsupport η disjoint from sphere(x₀, r). Then Z(η) = ∂A_r(η) − B_r(η) = 0 by (iii). The sphere is compact (isCompact_sphere) and lies in the open set G, because r < r₀. Apply lcmp_massOn_le_of_vanish_off_compact with C := sphere(x₀, r), V := G, X := Z and the set U: it gives M(Z) = M_U(Z) ≤ M_G(Z) < ∞.
7. (Mass of B_r.) By (ii), B_r(η) = ∫ ξ'(η) d(μ'⌞B_r(x₀)) for η ∈ 𝒟^d(U). The bound |ξ'(x)(α)| ≤ |α| holds everywhere, hence μ'⌞B_r(x₀)-a.e. Step 0 with k := d, ν := μ'⌞B_r(x₀), ζ := ξ' and W := U gives M(B_r) ≤ (μ'⌞B_r(x₀))(U) ≤ μ'(B_r(x₀)) ≤ μ'(closedBall(x₀, r₀)) < ∞.
8. (Mass of ∂A_r.) For every η ∈ 𝒟^d(U), ∂A_r(η) = B_r(η) + Z(η), since Z(η) = ∂A_r(η) − B_r(η). Let η be admissible for M_U. Then ofReal(∂A_r(η)) ≤ ofReal(B_r(η)) + ofReal(Z(η)) (ENNReal.ofReal_add_le) ≤ M_U(B_r) + M_U(Z) (le_massOn). Taking the supremum, M(∂A_r) ≤ M(B_r) + M(Z), which is finite by steps 6–7.
9. (R' := A_r is integer multiplicity.) Apply (IMC)(b) to R₀ and E := B_r(x₀), which is open and hence Borel. It gives an IMRep R'' of U with carrier M ∩ B_r(x₀), multiplicity θ and orientation ξ. Let ω ∈ 𝒟^{d+1}(U). Step 1(c) with E := B_r(x₀) and R′ := R'' gives R''.action(ω) = ∫_{B_r(x₀)} ξ(ω) dμ, and this is A_r(ω) by (i). So R'' represents R' := A_r, i.e. R' is integer multiplicity.
10. (Mass of R'.) By (i), A_r(ω) = ∫ ξ(ω) d(μ⌞B_r(x₀)). The bound |ξ(x)(α)| ≤ |α| holds μ-a.e. (step 1), hence μ⌞B_r(x₀)-a.e. (ae_restrict_of_ae). Step 0 with k := d + 1, ν := μ⌞B_r(x₀) and W := U gives M(R') ≤ (μ⌞B_r(x₀))(U) ≤ μ(B_r(x₀)) ≤ μ(closedBall(x₀, r₀)) < ∞.
11. (Support of R'.) Let y ∈ spt R', so y ∈ U and y ∉ Z(R'), and suppose y ∉ closedBall(x₀, r). The set U ∖ closedBall(x₀, r) is open (U open, closed balls closed) and contains y, so there is δ > 0 with B_δ(y) ⊆ U ∖ closedBall(x₀, r). Put W := B_{δ/2}(y). Then W is open and contains y; closure(W) ⊆ closedBall(y, δ/2) (closure_ball_subset_closedBall), so closure(W) is compact, being a closed subset of a compact ball; and closure(W) ⊆ closedBall(y, δ/2) ⊆ B_δ(y) ⊆ U. Let ω ∈ 𝒟^{d+1}(U) with tsupport ω ⊆ W, and let x ∈ B_r(x₀). If x were in tsupport ω, then x ∈ W ⊆ B_δ(y) ⊆ U ∖ closedBall(x₀, r), contradicting x ∈ B_r(x₀) ⊆ closedBall(x₀, r); so x ∉ tsupport ω, ω(x) = 0 and ξ(x)(ω(x)) = 0. By (i), R'(ω) = ∫_{B_r(x₀)} ξ(ω) dμ = 0 (setIntegral_eq_zero_of_forall_eq_zero). Thus W is one of the open sets whose union is Z(R'), so y ∈ W ⊆ Z(R'), a contradiction. Therefore spt R' ⊆ closedBall(x₀, r).
12. (Agreement with ∂R.) Let η ∈ 𝒟^d(U) with tsupport η ⊆ B_r(x₀). Points of B_r(x₀) have distance < r from x₀, so tsupport η is disjoint from sphere(x₀, r). Hence ∂R'(η) = ∂A_r(η) = B_r(η) by (iii), and B_r(η) = ∫_{B_r(x₀)} ξ'(η) dμ' by (ii). This equals ∫ ξ'(η) dμ', because the integrand vanishes off B_r(x₀): there x ∉ tsupport η, so η(x) = 0 and ξ'(x)(0) = 0 (setIntegral_eq_integral_of_forall_compl_eq_zero). By step 2 it equals ∂R(η).
13. (Conclusion.) r > 0 and closedBall(x₀, r) ⊆ closedBall(x₀, r₀) ⊆ U, as r < r₀. R' = A_r is integer multiplicity (step 9), spt R' ⊆ closedBall(x₀, r) (step 11), M(R') < ∞ (step 10), M(∂R') < ∞ (step 8), and ∂R'(η) = ∂R(η) for every η ∈ 𝒟^d(U) with tsupport η ⊆ B_r(x₀) (step 12). ∎

Lean note (verified realization of the numbered proof above; not part of the proof). The following tactic proof of `Submission.dtc_bc_tc_cl_bim_slice_localization` compiles against the frozen contract (Lean v4.35.0-rc3, Mathlib 25730c7c, SimonGMT 2b366308). It is placed after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's `open` commands, with the reused sibling declarations `Submission.lcmp_imRep_measure_restrict` and `Submission.lcmp_massOn_le_of_vanish_off_compact` in scope. With those two declarations as the only non-standard constants, `#print axioms` reports only propext, Classical.choice and Quot.sound besides them, and `exact Submission.dtc_bc_tc_cl_bim_slice_localization` closes the frozen type in the comparator scope. Do not open the ContDiff scope, whose notation makes ω a token.
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
  -- the support of A r lies in closedBall x₀ r
  have hspt : (A r).support ⊆ closedBall x₀ r := by
    intro y hy
    by_contra hyc
    apply hy.2
    have hopen : IsOpen (U \ closedBall x₀ r) := hU.sdiff isClosed_closedBall
    obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hopen y ⟨hy.1, hyc⟩
    refine mem_sUnion.mpr ⟨ball y (δ / 2), ⟨isOpen_ball, ?_, ?_, ?_⟩, mem_ball_self (by positivity)⟩
    · exact (isCompact_closedBall y (δ / 2)).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    · exact closure_ball_subset_closedBall.trans
        ((closedBall_subset_ball (by linarith)).trans (hδsub.trans sdiff_subset))
    · intro ω hω
      rw [hA r ω]
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      have hxt : x ∉ tsupport (ω : DifferentialForm (Euclid P) (d + 1)) := by
        intro hxt
        have h1 : x ∈ U \ closedBall x₀ r :=
          hδsub (ball_subset_ball (by linarith) (hω hxt))
        exact h1.2 (ball_subset_closedBall (mem_ball.mpr hx))
      rw [image_eq_zero_of_notMem_tsupport hxt, map_zero]
  refine ⟨r, hr.1, (closedBall_subset_closedBall hr.2.le).trans hcb₀, A r, ⟨Rr, hRrA⟩, hspt,
    hAU, hAbU, ?_⟩
  intro η hη
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
2. Slice by f = |· − x₀| with (SL), L = 1; the integrated bound (SL)(v) (Simon 4.10) on (0, r₀) gives r ∈ (0, r₀) with M_{B_{r₀}(x₀)}(∂A_r − B_r) < ∞.
3. ∂A_r − B_r vanishes off the compact sphere {f = r} ⊆ B_{r₀}(x₀), so its total mass is finite (lcmp_massOn_le_of_vanish_off_compact); M(B_r) ≤ μ'(B_r(x₀)) < ∞, hence M(∂A_r) < ∞.
4. (IMC)(b) with E = B_r(x₀) and lcmp_imRep_measure_restrict show that R' := A_r is IM (carrier M ∩ B_r(x₀)), and M(R') ≤ μ(B_r(x₀)) < ∞.
5. R' vanishes on forms supported in a small ball around any y ∈ U ∖ B̄_r(x₀), so spt R' ⊆ B̄_r(x₀).
6. For η supported in B_r(x₀): ∂R'(η) = B_r(η) = ∫ξ'(η)dμ' = ∂R(η).

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `rg -n "bim_|slice_localization|boundary_im_of_compact|extend_to_univ|boundary rectifiab" /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project --glob '*.lean' (no match)`
- `rg -n "theorem setLIntegral_congr_fun |theorem setIntegral_eq_zero_of_forall_eq_zero|theorem setIntegral_eq_integral_of_forall_compl_eq_zero|theorem enorm_integral_le_lintegral_enorm|theorem lintegral_indicator_one_le|theorem volume_Ioo|theorem IsCompact.of_isClosed_subset|theorem withDensity_apply |theorem tendsto_pow_atTop_nhds_zero_of_lt_one" /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib --glob '*.lean'`
- `rg -n "closure_ball_subset_closedBall|exists_bound_of_continuous|LipschitzWith.dist_left|protected theorem dist_left|isCompact_sphere|theorem ae_restrict_of_ae" /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib --glob '*.lean'`
- `grep -n 'def GeometricCurrentOn.restrictDomain|def GeometricCurrentOn.support|def GeometricCurrentOn.zeroRegion|isOpen_zeroRegion|def WeaklyConvergesOn|def GeometricCurrentOn.boundary|boundary_boundary|def GeometricCurrentOn.massOn|massOn_mono|le_massOn' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/{Currents,CurrentLocalEquality,Mass}.lean`
- `sed -n 1335,1405p and 1960,2005p book/chapter-06.txt (Simon Ch. 6, slices 4.6–4.11; 6.2 Weak Polyhedral Approximation, 6.3 Boundary Rectifiability, 6.4)`
- `python3 -I over dag.json: parent closure-a1 children and statuses; lean_name scans for dtc_bc_tc_cl_*, cbr_bim_*, dmcbr_bim_*, dtc_bc_tc_cl_bim (none); statuses/candidate commits of cmc_fc_extend_to_univ, lcmp_imRep_measure_restrict, lcmp_massOn_le_of_vanish_off_compact, cmr_abs_apply_le_massOn, rsd_mw_tfa_norm_props, cmc_slice_mass_bounds, cbrcs_cutoff_extension, dtc_extend_by_zero, dtc_restrictDomain_isIntegerMultiplicity, cmc_fc_eu_cutoff_mass_le`
- `python3 -I top-level split of the selected type at ' → ' and of foundations/deformation at ' ∧ '; string equality of (MR), (IMC), (VO), (DTr), (REP), (IMC)(b), (IMC)(d), (SL) against deformation, foundations, cmc_slice_mass_bounds and cbr_bim_slice_localization (all equal)`
- `sed of nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-10c568d35f/decomposition-v{1,2,3}.json and decomposition-audit-v3.json (parallel cbr split: slice_localization, extension_masses, deformation_closure; audit acceptable)`
- `grep -n '_existing_lean_name_problem|_overlay_accepted_children|max_depth' /runtime/flows/gmt-claude-73516a26825a/_recursive_lean/runtime.py (reuse of an accepted declaration requires the identical frozen type; depth 5 < max_depth 6)`
- `git show <candidate>:GMT/Ch07/Submission.lean for bc8fc26f, ae810e9b, a3cc98d1, 7a706164, f492ba4a, a1c12d76 (frozen type lines identical to dag.json); git log --all -S dtc_bc_tc_cl_bim (none)`
- `lake env lean /tmp/bim-dtc-scratch/Challenges.lean (exit 0); lake env lean /tmp/bim-dtc-scratch/AllAx.lean (no errors; #print axioms as stated); lake env lean /tmp/bim-dtc-scratch/cand_*.lean (five accepted proofs, only propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/ProperSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-c5b345f704/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-c5b345f704/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-e6c3d0d31e/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-e6c3d0d31e/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-10c568d35f/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-10c568d35f/decomposition-audit-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-extend-to-univ-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1-imrep-1bd5f15878/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1-mass-l-9981f1246a/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-eva-463e096c91/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1-test-form-approx-a1-norm-props-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-73516a26825a/_recursive_lean/runtime.py`
- `/tmp/bim-dtc-scratch/Challenges.lean`
- `/tmp/bim-dtc-scratch/AllAx.lean`

The snapshot (local-project, project b4d606db, Mathlib 25730c7c) has a Ch07 Contract.lean byte-identical to the workspace Contract.lean and Submission.lean. It contains no slice-localization, extension, deformation or boundary-rectifiability theorem (rg: no match), so these come from DAG declarations. Every Mathlib lemma used by the two new children's proofs exists in the snapshot and resolves after import GMT.Ch07.Submission: setLIntegral_congr_fun, Real.volume_Ioo, setIntegral_eq_zero_of_forall_eq_zero, setIntegral_eq_integral_of_forall_compl_eq_zero, enorm_integral_le_lintegral_enorm, lintegral_indicator_one_le, withDensity_apply, ae_restrict_of_ae, closure_ball_subset_closedBall, IsCompact.of_isClosed_subset, isCompact_sphere, LipschitzWith.dist_left, HasCompactSupport.exists_bound_of_continuous and tendsto_pow_atTop_nhds_zero_of_lt_one. The SimonGMT API needed (restrictDomain_apply, support/zeroRegion/isOpen_zeroRegion, boundary_apply, boundary_boundary, WeaklyConvergesOn.boundary, massOn_mono, le_massOn) is in Chapter06 Currents/CurrentLocalEquality/Mass. Five accepted declarations with byte-identical frozen types supply the extension (cmc_fc_extend_to_univ) and the helpers. Their candidate proofs recompile with only propext, Classical.choice and Quot.sound. Both new child types elaborate in the comparator scope. The assembly of the exact selected type from the children and the siblings slicing and foundations compiles.
