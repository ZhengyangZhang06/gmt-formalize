# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.offvertex_rep-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.offvertex_rep-a1.orientation_glue-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 4 and 5 and fact (F3) of the supplied parent proof (parent B3a–B3b).
Departures from the parent text, stated explicitly.
(i) (F3) is derived from the accepted declaration submanifold_density_one (H^m(M ∩ B_s(w))/(ω_m s^m) → 1 as s ↓ 0). The parent used the mean value inequality and bilipschitz_measure. The conclusion is the same and the proof is shorter.
(ii) In the sign test the parent shows ξ_{y'} = −ξ_y on a whole neighbourhood. Here both representations of C are compared on one bump form: one integral is > 0 and the other < 0, using only continuity of the two pairings at w. The idea is the same (orientation_sign plus a positive bump-form test).
Notation.
- H^m := μHE[m], B_s(w) := ball w s, and B_y := B_{ρ(y)}(y).
- ⟨α, η⟩ := η(α), and |α| := covectorEuclideanNorm α.
- ξ_y := ξs y.

1. (Tangent spaces of the pieces.) M is an embedded C¹ m-submanifold, so the hypothesis of submanifold_local holds with O := ℝ^P at every point (M ∩ ℝ^P = M). Part (b) of submanifold_local with O := B_y gives tangentSpace(M ∩ B_y, w) = tangentSpace(M, w) for every y ∈ M and w ∈ M ∩ B_y.
2. (Positivity, F3.) Let w ∈ M and s > 0. Then H^m(M ∩ B_s(w)) ≠ 0. Otherwise H^m(M ∩ B_{s'}(w)) ≤ H^m(M ∩ B_s(w)) = 0 for 0 < s' < s. So the ratio H^m(M ∩ B_{s'}(w))/(ω_m s'^m) is 0 on (0, s) and tends to 0 as s' ↓ 0. By submanifold_density_one it tends to 1. Limits in [0, ∞] are unique, a contradiction.
3. (Agreement on overlaps.) Let y, y' ∈ M and w ∈ M ∩ B_y ∩ B_{y'}. We show ξ_{y'}(w) = ξ_y(w).
 (a) By the orientation hypotheses there are subspaces Q and Q' such that:
  - Q has carrier tangentSpace(M ∩ B_y, w), and ξ_y(w) is a unit orientation of Q;
  - Q' has carrier tangentSpace(M ∩ B_{y'}, w), and ξ_{y'}(w) is a unit orientation of Q'.
  By step 1 both carriers equal tangentSpace(M, w), so Q = Q' (a submodule is determined by its carrier). By orientation_sign, ξ_{y'}(w) = ξ_y(w) or ξ_{y'}(w) = −ξ_y(w). Assume the latter; we derive a contradiction.
 (b) Let L be given by unit_orientation_dual, and put β := L(ξ_y(w)). Part (c) of that lemma gives ξ_y(w)(β) = 1, hence ξ_{y'}(w)(β) = −1.
 (c) Put f(x) := ξ_y(x)(β) and g(x) := ξ_{y'}(x)(β).
  - Orientations are continuous on their sets, and evaluation at β is continuous. So f is continuous on M ∩ B_y and g on M ∩ B_{y'}.
  - Both sets are neighbourhoods of w relative to M, and f(w) = 1, g(w) = −1.
  - B_y ∩ B_{y'} is an open set containing w.
  Hence there is r > 0 with B_r(w) ⊆ B_y ∩ B_{y'} such that f(x) > 1/2 and g(x) < −1/2 for every x ∈ M ∩ B_r(w).
 (d) Let φ : ℝ^P → [0, 1] be the smooth bump ContDiffBump centred at w with inner radius r/4 and outer radius r/2.
  - φ = 1 on closedBall(w, r/4), and tsupport φ = closedBall(w, r/2) ⊆ B_r(w) is compact.
  - For a covector γ put ω_γ(x) := φ(x)γ. It is smooth with compact support, so ω_γ ∈ 𝒟^m(ℝ^P), and tsupport ω_γ ⊆ B_r(w).
  - ω_{−β} = −ω_β.
 (e) Claim. Let z ∈ M with B_r(w) ⊆ B_z, and let γ be a covector with ξ_z(x)(γ) ≥ 1/2 for all x ∈ M ∩ B_r(w). Then C(ω_γ) > 0.
  Proof. tsupport ω_γ ⊆ B_z, so by hypothesis C(ω_γ) = ∫_{M ∩ B_z} F dH^m, where F(x) := ξ_z(x)(φ(x)γ) = φ(x)·ξ_z(x)(γ).
  - F is integrable on M ∩ B_z. It is continuous on the Borel set M ∩ B_z, hence a.e. strongly measurable for H^m restricted to it. Also |F(x)| ≤ |ξ_z(x)(γ)| ≤ |γ| by unit_orientation_dual (a), since ξ_z(x) is a unit orientation of a subspace. And H^m(M ∩ B_z) < ∞.
  - F ≥ 0 on M ∩ B_z. On B_r(w), φ ≥ 0 and ξ_z(x)(γ) ≥ 1/2. Off B_r(w), φ(x) = 0 because tsupport φ ⊆ B_r(w).
  - F ≥ 1/2 on M ∩ B_{r/4}(w), where φ = 1.
  - Put E := M ∩ B_{r/4}(w) ⊆ M ∩ B_z. E is Borel, H^m(E) > 0 by step 2, and H^m(E) ≤ H^m(M ∩ B_z) < ∞.
  - Hence C(ω_γ) = ∫_{M ∩ B_z} F ≥ ∫_E F ≥ (1/2)·H^m(E) > 0. The first inequality is monotonicity in the domain for a nonnegative integrable function; the second is the lower bound on E.
 (f) Apply (e) twice.
  - With z := y and γ := β, using f > 1/2 on M ∩ B_r(w): C(ω_β) > 0.
  - With z := y' and γ := −β, using ξ_{y'}(x)(−β) = −g(x) > 1/2: C(ω_{−β}) > 0.
  But C(ω_{−β}) = C(−ω_β) = −C(ω_β) < 0 by linearity of C, a contradiction. Hence ξ_{y'}(w) = ξ_y(w).
4. (Global orientation.) Define ξ(x) := ξ_x(x) for every x ∈ ℝ^P.
 (a) Let y ∈ M and x ∈ M ∩ B_y. Then x ∈ B_x since ρ(x) > 0. Step 3 for the pair (y, x) at the point x gives ξ(x) = ξ_x(x) = ξ_y(x). So ξ = ξ_y on M ∩ B_y, the second conclusion.
 (b) ξ is continuous on M. Let y ∈ M.
  - ξ_y is continuous within M ∩ B_y at y, and M ∩ B_y is a neighbourhood of y relative to M. So ξ_y is continuous within M at y.
  - ξ agrees with ξ_y on that neighbourhood, by (a). So ξ is continuous within M at y.
 (c) Let x ∈ M. Then ξ(x) = ξ_x(x) is a unit orientation of a subspace Q with carrier tangentSpace(M ∩ B_x, x) = tangentSpace(M, x), by step 1.
 Hence IsOrientation m M ξ.
5. (Representation.) Let y ∈ M and ω ∈ 𝒟^m(ℝ^P) with tsupport ω ⊆ B_y.
 - By hypothesis, C(ω) = ∫_{M ∩ B_y} ⟨ω, ξ_y⟩ dH^m.
 - This equals ∫_{M ∩ B_y} ⟨ω, ξ⟩ dH^m, since ξ = ξ_y on the Borel set M ∩ B_y (step 4(a)).
 - For x ∈ M ∖ B_y we have x ∉ tsupport ω, so ω(x) = 0 and ⟨ω(x), ξ(x)⟩ = 0. As M is Borel and M ∩ B_y ⊆ M, this gives ∫_{M ∩ B_y} ⟨ω, ξ⟩ dH^m = ∫_M ⟨ω, ξ⟩ dH^m. ∎

Lean reference proof (verified). The declaration below was compiled with Lean v4.35.0-rc3 and Mathlib 25730c7c, after `import GMT.Ch07.Submission`, in namespace GMT.Ch07 with the contract `open`s. It was compiled twice: in a standalone file, and spliced into a copy of GMT/Ch07/Submission.lean just before main_theorem. Each listed dependency was present under its exact frozen type, as an axiom standing in for the accepted or sibling declaration. `#print axioms` reports propext, Classical.choice and Quot.sound, plus exactly the declarations listed in depends_on (for reused children: their Submission names). It follows the numbered proof above.

```lean
theorem Submission.codim1_ovr_orientation_glue : ∀ (P m : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) m) (M : Set (Euclid P)) (ρ : Euclid P → ℝ) (ξs : Euclid P → Euclid P → MultiVector P m), IsEmbeddedSubmanifold 1 m M → MeasurableSet M → (∀ y ∈ M, 0 < ρ y ∧ IsOrientation m (M ∩ ball y (ρ y)) (ξs y) ∧ μHE[m] (M ∩ ball y (ρ y)) ≠ ∞ ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) m, tsupport (ω : DifferentialForm (Euclid P) m) ⊆ ball y (ρ y) → C ω = ∫ x in M ∩ ball y (ρ y), ξs y x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m]) → ∃ ξ : Euclid P → MultiVector P m, IsOrientation m M ξ ∧ (∀ y ∈ M, ∀ x ∈ M ∩ ball y (ρ y), ξ x = ξs y x) ∧ ∀ y ∈ M, ∀ ω : TestFormOn (univ : Set (Euclid P)) m, tsupport (ω : DifferentialForm (Euclid P) m) ⊆ ball y (ρ y) → C ω = ∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m] := by
  intro P m C M ρ ξs hM hMm hloc
  -- step 1: tangent spaces of the pieces are those of M
  have hloc2 := (Submission.codim1_ovr_embedded_submanifold_local P 1 m M le_rfl
    (fun y _ => ⟨univ, isOpen_univ, mem_univ y, by rwa [inter_univ]⟩)).2
  have htan : ∀ y ∈ M, ∀ w ∈ M ∩ ball y (ρ y),
      tangentSpace (M ∩ ball y (ρ y)) w = tangentSpace M w :=
    fun y _ w hw => (hloc2 (ball y (ρ y)) isOpen_ball).2 w hw
  -- step 2 (F3): positivity of H^m(M ∩ B_s(w))
  have hpos : ∀ w ∈ M, ∀ s : ℝ, 0 < s → μHE[m] (M ∩ ball w s) ≠ 0 := by
    intro w hw s hs h0
    have hlim := Submission.dimred_rpd_submanifold_density_one P m M w hM hw
    have hev : (fun _ : ℝ => (0 : ℝ≥0∞)) =ᶠ[𝓝[>] (0 : ℝ)]
        fun s' : ℝ => μHE[m] (M ∩ ball w s') / (unitBallVolume m * ENNReal.ofReal (s' ^ m)) := by
      filter_upwards [Ioo_mem_nhdsGT hs] with s' hs'
      have h' : μHE[m] (M ∩ ball w s') = 0 :=
        measure_mono_null (inter_subset_inter_right _ (ball_subset_ball hs'.2.le)) h0
      rw [h', ENNReal.zero_div]
    have h01 := tendsto_nhds_unique (tendsto_const_nhds.congr' hev) hlim
    exact zero_ne_one h01
  -- step 3: agreement on overlaps (analytic core: bump-form test)
  have hagree : ∀ y ∈ M, ∀ y' ∈ M, ∀ w ∈ M ∩ ball y (ρ y), w ∈ ball y' (ρ y') →
      ξs y' w = ξs y w := by
    intro y hy y' hy' w hw hw'
    obtain ⟨Q, hQ, hQξ⟩ := (hloc y hy).2.1.2 w hw
    obtain ⟨Q', hQ', hQξ'⟩ := (hloc y' hy').2.1.2 w ⟨hw.1, hw'⟩
    have hQQ : Q' = Q := by
      apply SetLike.coe_injective
      rw [hQ, hQ', htan y hy w hw, htan y' hy' w ⟨hw.1, hw'⟩]
    subst hQQ
    rcases Submission.rsdic_unitOrientation_eq_or_eq_neg P m (ξs y w) (ξs y' w) Q' hQξ hQξ' with h | h
    · exact h
    · exfalso
      obtain ⟨L, hL⟩ := Submission.dor_ims_unitOrientation_dual P m
      have hβ1 : ξs y w (L (ξs y w)) = 1 := (hL (ξs y w) Q' hQξ).2.2
      have hβ2 : ξs y' w (L (ξs y w)) = -1 := by
        rw [h, neg_apply, hβ1]
      set β := L (ξs y w) with hβdef
      have hwM : w ∈ M := hw.1
      -- continuity of the two pairings at w within M
      have hny : M ∩ ball y (ρ y) ∈ 𝓝[M] w :=
        inter_mem_nhdsWithin M (isOpen_ball.mem_nhds hw.2)
      have hny' : M ∩ ball y' (ρ y') ∈ 𝓝[M] w :=
        inter_mem_nhdsWithin M (isOpen_ball.mem_nhds hw')
      have hcy : ContinuousWithinAt (fun x => ξs y x β) M w :=
        (((hloc y hy).2.1.1 w hw).mono_of_mem_nhdsWithin hny).clm_apply continuousWithinAt_const
      have hcy' : ContinuousWithinAt (fun x => ξs y' x β) M w :=
        (((hloc y' hy').2.1.1 w ⟨hwM, hw'⟩).mono_of_mem_nhdsWithin hny').clm_apply
          continuousWithinAt_const
      have hev1 : ∀ᶠ x in 𝓝[M] w, (1 / 2 : ℝ) < ξs y x β :=
        hcy.eventually (lt_mem_nhds (by show (1 / 2 : ℝ) < ξs y w β; rw [hβ1]; norm_num))
      have hev2 : ∀ᶠ x in 𝓝[M] w, ξs y' x β < -(1 / 2 : ℝ) :=
        hcy'.eventually (gt_mem_nhds (by show ξs y' w β < -(1 / 2 : ℝ); rw [hβ2]; norm_num))
      obtain ⟨r₁, hr₁, hr₁sub⟩ := Metric.mem_nhdsWithin_iff.1 (hev1.and hev2)
      obtain ⟨r₂, hr₂, hr₂sub⟩ := Metric.isOpen_iff.1 (isOpen_ball.inter (isOpen_ball (x := y') (ε := ρ y')))
        w ⟨hw.2, hw'⟩
      set r := min r₁ r₂ with hrdef
      have hr : 0 < r := lt_min hr₁ hr₂
      have hrB : ball w r ⊆ ball y (ρ y) ∩ ball y' (ρ y') :=
        (ball_subset_ball (min_le_right _ _)).trans hr₂sub
      have hrM : ∀ x ∈ M ∩ ball w r, (1 / 2 : ℝ) < ξs y x β ∧ ξs y' x β < -(1 / 2 : ℝ) :=
        fun x hx => hr₁sub ⟨ball_subset_ball (min_le_left _ _) hx.2, hx.1⟩
      -- the bump function
      let φ : ContDiffBump w := ⟨r / 4, r / 2, by positivity, by linarith⟩
      have hφsupp : tsupport φ ⊆ ball w r := by
        rw [φ.tsupport_eq]; exact closedBall_subset_ball (by simp [φ]; linarith)
      have hform : ∀ γ : Covector (Euclid P) m,
          (fun x => φ x • γ) ∈ TestFormOn (univ : Set (Euclid P)) m := by
        intro γ
        refine ⟨⟨?_, ?_⟩, subset_univ _⟩
        · exact (φ.contDiff (n := ⊤)).smul contDiff_const
        · exact φ.hasCompactSupport.smul_right
      have htsupp : ∀ γ : Covector (Euclid P) m,
          tsupport (fun x => φ x • γ) ⊆ ball w r :=
        fun γ => (tsupport_smul_subset_left _ _).trans hφsupp
      -- positivity of C on a bump times a covector that pairs ≥ 1/2 near w
      have hposC : ∀ z ∈ M, ball w r ⊆ ball z (ρ z) → ∀ γ : Covector (Euclid P) m,
          (∀ x ∈ M ∩ ball w r, (1 / 2 : ℝ) ≤ ξs z x γ) →
          0 < C ⟨fun x => φ x • γ, hform γ⟩ := by
        intro z hz hrz γ hγ
        rw [(hloc z hz).2.2.2 ⟨fun x => φ x • γ, hform γ⟩ ((htsupp γ).trans hrz)]
        simp only [map_smul, smul_eq_mul]
        have hmeasB : MeasurableSet (M ∩ ball z (ρ z)) := hMm.inter measurableSet_ball
        have hmeas4 : MeasurableSet (M ∩ ball w (r / 4)) := hMm.inter measurableSet_ball
        have hsub4 : M ∩ ball w (r / 4) ⊆ M ∩ ball z (ρ z) :=
          inter_subset_inter_right _ ((ball_subset_ball (by linarith)).trans hrz)
        have hfinB := (hloc z hz).2.2.1
        have hfin4 : μHE[m] (M ∩ ball w (r / 4)) ≠ ∞ :=
          ne_top_of_le_ne_top hfinB (measure_mono hsub4)
        have hpos4 : 0 < μHE[m].real (M ∩ ball w (r / 4)) :=
          ENNReal.toReal_pos (hpos w hwM (r / 4) (by positivity)) hfin4
        -- integrability on M ∩ B_z
        have hint : IntegrableOn (fun x => φ x * ξs z x γ) (M ∩ ball z (ρ z)) μHE[m] := by
          refine IntegrableOn.of_bound (lt_top_iff_ne_top.2 hfinB) ?_ (covectorEuclideanNorm γ) ?_
          · exact (((φ.continuous.continuousOn).mul
              (((hloc z hz).2.1.1).clm_apply continuousOn_const))).aestronglyMeasurable hmeasB
          · refine (ae_restrict_iff' hmeasB).2 (Eventually.of_forall fun x hx => ?_)
            obtain ⟨Q, -, hQ⟩ := (hloc z hz).2.1.2 x hx
            have hb := (hL (ξs z x) Q hQ).1 γ
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg φ.nonneg]
            calc φ x * |ξs z x γ| ≤ 1 * |ξs z x γ| :=
                  mul_le_mul_of_nonneg_right φ.le_one (abs_nonneg _)
              _ ≤ covectorEuclideanNorm γ := by rw [one_mul]; exact hb
        have hnonneg : ∀ x ∈ M ∩ ball z (ρ z), 0 ≤ φ x * ξs z x γ := by
          intro x hx
          by_cases hxr : x ∈ ball w r
          · exact mul_nonneg φ.nonneg (le_trans (by norm_num) (hγ x ⟨hx.1, hxr⟩))
          · rw [image_eq_zero_of_notMem_tsupport (fun h => hxr (hφsupp h)), zero_mul]
        have hge : ∀ x ∈ M ∩ ball w (r / 4), (1 / 2 : ℝ) ≤ φ x * ξs z x γ := by
          intro x hx
          have hx1 : φ x = 1 := φ.one_of_mem_closedBall (by
            show x ∈ closedBall w (r / 4); exact ball_subset_closedBall hx.2)
          rw [hx1, one_mul]
          exact hγ x ⟨hx.1, ball_subset_ball (by linarith) hx.2⟩
        calc (0 : ℝ) < 1 / 2 * μHE[m].real (M ∩ ball w (r / 4)) := by positivity
          _ ≤ ∫ x in M ∩ ball w (r / 4), φ x * ξs z x γ ∂μHE[m] :=
              setIntegral_ge_of_const_le_real hmeas4 hfin4 hge (hint.mono_set hsub4)
          _ ≤ ∫ x in M ∩ ball z (ρ z), φ x * ξs z x γ ∂μHE[m] :=
              setIntegral_mono_set hint
                ((ae_restrict_iff' hmeasB).2 (Eventually.of_forall hnonneg))
                (Eventually.of_forall hsub4)
      have h1 := hposC y hy (hrB.trans inter_subset_left) β
        (fun x hx => (hrM x hx).1.le)
      have h2 := hposC y' hy' (hrB.trans inter_subset_right) (-β)
        (fun x hx => by rw [map_neg]; linarith [(hrM x hx).2])
      have hneg : (⟨fun x => φ x • (-β), hform (-β)⟩ : TestFormOn (univ : Set (Euclid P)) m) =
          -⟨fun x => φ x • β, hform β⟩ := by
        apply Subtype.ext
        funext x
        simp [smul_neg]
      have hC : C ⟨fun x => φ x • (-β), hform (-β)⟩ = -C ⟨fun x => φ x • β, hform β⟩ := by
        rw [hneg]; exact map_neg (C.toCurrent : TestFormOn (univ : Set (Euclid P)) m →ₗ[ℝ] ℝ) _
      rw [hC] at h2
      linarith
  -- step 4: the global orientation
  refine ⟨fun x => ξs x x, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro y hy
    have hcont : ContinuousWithinAt (ξs y) (M ∩ ball y (ρ y)) y :=
      (hloc y hy).2.1.1 y ⟨hy, mem_ball_self (hloc y hy).1⟩
    have hnhds : M ∩ ball y (ρ y) ∈ 𝓝[M] y :=
      inter_mem_nhdsWithin M (isOpen_ball.mem_nhds (mem_ball_self (hloc y hy).1))
    have hc2 : ContinuousWithinAt (ξs y) M y := hcont.mono_of_mem_nhdsWithin hnhds
    refine hc2.congr_of_eventuallyEq ?_ rfl
    filter_upwards [hnhds] with x hx
    exact hagree y hy x hx.1 x hx (mem_ball_self (hloc x hx.1).1)
  · intro x hx
    obtain ⟨Q, hQ, hQξ⟩ := (hloc x hx).2.1.2 x ⟨hx, mem_ball_self (hloc x hx).1⟩
    exact ⟨Q, by rw [hQ, htan x hx x ⟨hx, mem_ball_self (hloc x hx).1⟩], hQξ⟩
  · intro y hy x hx
    exact hagree y hy x hx.1 x hx (mem_ball_self (hloc x hx.1).1)
  · intro y hy ω hω
    rw [(hloc y hy).2.2.2 ω hω]
    have hmeas : MeasurableSet (M ∩ ball y (ρ y)) := hMm.inter measurableSet_ball
    have h1 : ∫ x in M ∩ ball y (ρ y), ξs y x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m] =
        ∫ x in M ∩ ball y (ρ y), ξs x x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m] :=
      setIntegral_congr_fun hmeas (fun x hx => by
        simp only [hagree y hy x hx.1 x hx (mem_ball_self (hloc x hx.1).1)])
    rw [h1]
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hMm inter_subset_left
    intro x hx
    have hxω : x ∉ tsupport (ω : DifferentialForm (Euclid P) m) := fun h => hx.2 ⟨hx.1, hω h⟩
    rw [image_eq_zero_of_notMem_tsupport hxω, map_zero]
```

## Key steps

1. submanifold_local: the pieces M ∩ B_y have the tangent spaces of M, so two local orientations at a common point orient the same subspace.
2. submanifold_density_one gives H^m(M ∩ B_s(w)) > 0 for w ∈ M and s > 0.
3. orientation_sign gives ξ_{y'} = ±ξ_y at a common point. The − case fails: the bump form φ·L(ξ_y(w)) would receive a positive value of C from the y-representation and a negative one from the y'-representation.
4. ξ(x) := ξ_x(x) agrees with every ξ_y on M ∩ B_y. Hence it is a continuous orientation of M and represents C on each B_y.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; sha256sum <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `cat GMT/Ch07/Contract.lean (IMRep, IsIntegerMultiplicity, IsConeCurrent, blowUp, dilation, IsEmbeddedSubmanifold, tangentSpace, IsOrientation, IsUnitOrientationOf, regularSet, HasMassDensity)`
- `grep -n 'VanishesOn|def zeroRegion|def support|isOpen_zeroRegion|structure GeometricCurrentOn|abbrev TestFormOn|IsTestForm|IsSmoothForm|covectorEuclideanNorm|testFormEuclideanSupNorm' simongmt/Poincare/SimonGMT/Chapter06/{CurrentLocalEquality,Currents,Forms,Mass,FormSupNorm}.lean`
- `rg -n 'euclideanHausdorffMeasure_smul₀|nullSingletonClass_hausdorff|exists_isSubordinate|one_of_mem_closedBall|support_eq|tsupport_eq|tendsto_integral_of_dominated_convergence|setIntegral_ge_of_const_le_real|setIntegral_mono_set|IntegrableOn.of_bound|ENNReal.tsum_geometric|exists_nat_pow_near|Tendsto.bddAbove_range|ContinuousAlternatingMap.apply' <snapshot>/mathlib/Mathlib`
- `rg -c 'codim1_ovr_' <snapshot> (no match); grep each of the 7 new lean_names in dag.json (no match); git grep -l 'codim1_ovr_' over all 1662 distinct ref objects (no match)`
- `python3 over dag.json: accepted nodes whose lean_statement mentions IsEmbeddedSubmanifold, tangentSpace or IsOrientation; nodes with IsConeCurrent and support; IMRep/IsIntegerMultiplicity with Tendsto; status, frozen type, candidate commit and parent handoff of the 5 reused names; children of simons_regular_cone-a1`
- `git show <commit> -- GMT/Ch07/Submission.lean for 44ef61f79e21 (dtc_vanish_off_support: smooth partition of unity), 52115c22ec2d (cone_current_apply_dilation_pullback), d626082a69a0 (chart_tangentSpace_eq_range_fderiv), a5ceace526bc (dpf_pb_imrep_pullback_integral_tendsto: IMRep dominated convergence)`
- `runtime.py (_decompose, _existing_lean_name_problem, _solve_children, _install_parent_supplied_child_handoff) and speculation.py contract (a parent's prerequisites are its children plus its depends_on)`
- `lean -DautoImplicit=false /tmp/ovr-split-check/{Types,Assembly,SkelC3,C1C2,C4,C5,C6,C7,Full,SubmissionCopy}.lean with LEAN_PATH = .lake/build/lib/lean plus every package's .lake/build/lib/lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/NullSingletonClass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Archimedean/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-b7ab3fcecc/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-7577af74dd/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-cone-measure-homogeneous-a1-27e5a07a68/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-chart-tangent-space-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-unit-or-24edf309fb/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-integer-combination-a1-orientation-sign-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1-density-one-a1/parent-supplied-natural-proof.md`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/speculation.py`
- `/tmp/ovr-split-check/Full.lean`
- `/tmp/ovr-split-check/SubmissionCopy.lean`

Pins match. The manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib. The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).
Library.
- SimonGMT Chapter06 supplies GeometricCurrentOn, TestFormOn, VanishesOn, the open zeroRegion, support = U ∖ zeroRegion, and covectorEuclideanNorm.
- SimonGMT has no continuity or homogeneity lemma for covectorEuclideanNorm, and no local-to-global gluing lemma for currents. The children prove these inline.
- The snapshot Mathlib has every library lemma the children use:
  - Measure.euclideanHausdorffMeasure_smul₀ (Geometry/Euclidean/Volume/Measure.lean:152);
  - nullSingletonClass_hausdorff (MeasureTheory/Measure/Hausdorff.lean:615);
  - SmoothPartitionOfUnity.exists_isSubordinate (Geometry/Manifold/PartitionOfUnity.lean:555);
  - ContDiffBump.one_of_mem_closedBall, support_eq and tsupport_eq (Analysis/Calculus/BumpFunction/Basic.lean:137–157);
  - tendsto_integral_of_dominated_convergence (MeasureTheory/Integral/DominatedConvergence.lean:57);
  - setIntegral_mono_set and setIntegral_ge_of_const_le_real (MeasureTheory/Integral/Bochner/Set.lean:737, 798);
  - IntegrableOn.of_bound (MeasureTheory/Integral/IntegrableOn.lean:174);
  - ENNReal.tsum_geometric (Analysis/SpecificLimits/Basic.lean:402);
  - exists_nat_pow_near (Algebra/Order/Archimedean/Basic.lean:195).
DAG.
- Five accepted declarations are reused with byte-identical frozen types: cone_current_apply_dilation_pullback (52115c22ec2d), chart_tangentSpace_eq_range_fderiv (d626082a69a0), dor_ims_unitOrientation_dual (9c8432cb0101), rsdic_unitOrientation_eq_or_eq_neg (fe95347baaed) and dimred_rpd_submanifold_density_one (e8842d90b78f).
- Unaccepted nodes owned by other parents cannot be shared: idtp_tpf_cone_support_smul and idtp_ccd_cone_support_smul (decomposing) have the content of cone_support_smul. So that child gets the fresh name codim1_ovr_cone_support_smul.
- The 7 new codim1_ovr_ names are free in dag.json, the snapshot, SimonGMT and all git refs.
- This node's own prerequisites stay available to its glue (speculation.contract = children + depends_on): codim1_density_one_regular_local_rep, dtc_vanish_off_support and dor_ims_unitOrientation_dual.
Lean.
- Types.lean elaborates all 12 child types.
- Assembly.lean proves the selected frozen type from the frozen child types and this node's prerequisites, all given as axioms.
- Each new child has a complete Lean proof that uses exactly its listed dependencies. These proofs are attached to the child proofs.
- Full.lean, and SubmissionCopy.lean (the same block spliced into a copy of Submission.lean before main_theorem), compile without errors.
- #print axioms of the selected theorem lists propext, Classical.choice and Quot.sound, plus the 7 frozen prerequisites: the 5 reused declarations, codim1_density_one_regular_local_rep and dtc_vanish_off_support.
