# Parent-supplied natural-language proof

- Parent DAG node: `root.rectifiability-a1.bf_trichotomy-a1`
- Child DAG node: `root.rectifiability-a1.bf_trichotomy-a1.fibre_cone_comparison-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent-supplied proof of rectifiability_bf_trichotomy. It consists of the inclusions (i) and (ii) between cones and unions of fibres and the resulting bounds ϑ_j ≤ Φ ≤ N^{k/2}Σ_jϑ_j. Here ψ_{j,u}(B(0,t))/tᵏ is written as sup_{0<r<δ} μ(B(a,r) ∩ K_j(t))/(rt)ᵏ. The case N = 0 (where the parent proof notes Φ ≡ 0) is included.

Notation. c(x) := ENNReal.ofReal x. For y ∈ ℝ^N, y_j := ⟨e_j,y⟩ is the j-th coordinate, and |y_j| ≤ |y|. Put F(s) := sup_{r∈(0,δ)} μ(X_u(a,r,s))/c((rs)ᵏ) and F_j(t) := sup_{r∈(0,δ)} μ(B(a,r) ∩ K_j(t))/c((rt)ᵏ), so that Φ = limsup_{s→0⁺} F(s) and ϑ_j = limsup_{t→0⁺} F_j(t).

1. Fibre identity. For c ∈ ℝᵏ and y ∈ ℝ^N, L_{u⊕_jc}(y) = L_u(y) + y_j·c. Indeed, the i-th coordinate is ⟨u_i + c_ie_j, y⟩ = ⟨u_i,y⟩ + c_i⟨e_j,y⟩ = ⟨u_i,y⟩ + c_iy_j (EuclideanSpace.inner_single_left).

2. Inclusion (ii): B(a,r) ∩ K_j(t) ⊆ X_u(a,r,t) for r > 0 and t > 0.
 - Let x ∈ B(a,r) ∩ K_j(t) and y := x − a ≠ 0, and let c satisfy |c| < t and L_{u⊕_jc}(y) = 0.
 - By step 1, L_u(y) = −y_j·c, so |L_u(y)| = |y_j|·|c| ≤ |y|·|c| < t|y|. The last inequality is strict because |y| > 0 and |c| < t.
 - Also |x − a| < r. Hence x ∈ X_u(a,r,t).
 For t ≤ 0 the set {c : |c| < t} is empty, so K_j(t) = ∅.

3. ϑ_j ≤ Φ. Let t > 0 and r ∈ (0,δ). Step 2 and monotonicity of μ give μ(B(a,r) ∩ K_j(t))/c((rt)ᵏ) ≤ μ(X_u(a,r,t))/c((rt)ᵏ). Taking the sup over r gives F_j(t) ≤ F(t). For t ≤ 0, F_j(t) = 0 ≤ F(t), since μ(∅) = 0. Hence F_j ≤ F pointwise, and ϑ_j = limsup F_j ≤ limsup F = Φ (Filter.limsup_le_limsup).

4. Case N = 0. Then ℝ^N is a single point, so x − a = 0 for every x. Since L_u(0) = 0, the condition |L_u(x − a)| < s|x − a| reads 0 < 0, which is false. So X_u(a,r,s) = ∅, F ≡ 0 and Φ = 0 ≤ (√N)ᵏΣ_jϑ_j. Assume N ≥ 1 from now on and set σ := √N > 0.

5. Inclusion (i): X_u(a,r,s) ⊆ ⋃_{j} (B(a,r) ∩ K_j(σs)) for s > 0 and r > 0.
 - Let x ∈ X_u(a,r,s) and y := x − a. Then |L_u(y)| < s|y| forces |y| > 0, i.e. x ≠ a.
 - Since |y|² = Σ_j y_j² ≤ N·max_j y_j², there is j with |y_j| ≥ |y|/σ > 0.
 - Put c := −(1/y_j)·L_u(y) ∈ ℝᵏ. Then |c| = |L_u(y)|/|y_j| < s|y|·σ/|y| = σs.
 - By step 1, L_{u⊕_jc}(y) = L_u(y) + y_j·c = 0. Hence x ∈ K_j(σs), and also x ∈ B(a,r).

6. Pointwise bound. Let s > 0 and r ∈ (0,δ).
 - By step 5 and finite subadditivity (measure_iUnion_fintype_le), μ(X_u(a,r,s)) ≤ Σ_j μ(B(a,r) ∩ K_j(σs)).
 - Since (rσs)ᵏ = σᵏ(rs)ᵏ with all factors positive, c((rs)ᵏ)⁻¹ = c(σᵏ)·c((rσs)ᵏ)⁻¹.
 - Therefore μ(X_u(a,r,s))/c((rs)ᵏ) ≤ c(σᵏ)·Σ_j μ(B(a,r) ∩ K_j(σs))/c((rσs)ᵏ) ≤ c(σᵏ)·Σ_j F_j(σs). The last step holds because r ∈ (0,δ) is admissible in F_j(σs).
 Taking the sup over r ∈ (0,δ): F(s) ≤ c(σᵏ)·Σ_j F_j(σs) for all s > 0.

7. Constant factor. Let H(s) := Σ_j F_j(σs). By step 6, F ≤ c(σᵏ)·H on (0,∞), which belongs to 𝓝[>]0. So Φ ≤ limsup (c(σᵏ)·H) = c(σᵏ)·limsup H, by ENNReal.limsup_const_mul_of_ne_top since c(σᵏ) < ∞.

8. limsup of a finite sum. For functions h₁, …, h_N : ℝ → [0,∞] and any filter, limsup Σ_j h_j ≤ Σ_j limsup h_j.
 - By induction on N it suffices to show limsup(h + h′) ≤ limsup h + limsup h′.
 - If the right side is ∞ this is trivial. Otherwise let α > limsup h and α′ > limsup h′ be finite. Eventually h < α and h′ < α′ (Filter.eventually_lt_of_limsup_lt), so eventually h + h′ < α + α′, and limsup(h + h′) ≤ α + α′.
 - Letting α ↓ limsup h and α′ ↓ limsup h′ gives the claim.
 Mathlib's ENNReal.limsup_add_le assumes a CountableInterFilter, which 𝓝[>]0 is not, so this direct argument is used. Hence limsup H ≤ Σ_j limsup_{s→0⁺} F_j(σs).

9. Change of variable. The map s ↦ σs sends 𝓝[>]0 into 𝓝[>]0, since σ > 0 (Tendsto; i.e. map (σ·) 𝓝[>]0 ≤ 𝓝[>]0). Therefore limsup_{s→0⁺} F_j(σs) = limsup F_j (map (σ·) 𝓝[>]0) ≤ limsup F_j 𝓝[>]0 = ϑ_j (Filter.limsup_comp, Filter.limsup_le_limsup_of_le).

10. Steps 7–9 give Φ ≤ c(σᵏ)·Σ_jϑ_j = c((√N)ᵏ)·Σ_jϑ_j. Together with step 3 and the case N = 0 (step 4), this proves the statement. ∎

Lean reference proof (appendix; written by the independent Lean reviewer of this decomposition and re-compiled by the author). It is compile-checked as a single declaration against the exact frozen statement inside `namespace GMT.Ch06` of a scratch copy of the frozen project (commit d8d46c9587747dee0751a1f780fcafdba16a3886, Lean v4.35.0-rc3, pinned Mathlib 25730c7c), with no sibling dependencies; #print axioms = [propext, Classical.choice, Quot.sound]. It introduces no auxiliary declarations.
```lean
theorem Submission.rectifiability_bf_fibre_cone_comparison : (∀ (N m : ℕ) (μ : Measure (Eucl N)) (δ : ℝ) (a : Eucl N) (u : Fin (m + 1) → Eucl N), (∀ j : Fin N, limsup (fun t : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ (ball a r ∩ {x | x ≠ a ∧ ∃ c ∈ ball (0 : Eucl (m + 1)) t, (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i + c i • EuclideanSpace.single j (1 : ℝ)) (x - a)) : Eucl (m + 1)) = 0}) / ENNReal.ofReal ((r * t) ^ (m + 1))) (𝓝[>] 0) ≤ limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x a < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖} / ENNReal.ofReal ((r * s) ^ (m + 1))) (𝓝[>] 0)) ∧ limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x a < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖} / ENNReal.ofReal ((r * s) ^ (m + 1))) (𝓝[>] 0) ≤ ENNReal.ofReal (Real.sqrt (N : ℝ) ^ (m + 1)) * ∑ j : Fin N, limsup (fun t : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ (ball a r ∩ {x | x ≠ a ∧ ∃ c ∈ ball (0 : Eucl (m + 1)) t, (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i + c i • EuclideanSpace.single j (1 : ℝ)) (x - a)) : Eucl (m + 1)) = 0}) / ENNReal.ofReal ((r * t) ^ (m + 1))) (𝓝[>] 0)) := by
  intro N m μ δ a u
  let L : Eucl N → Eucl (m + 1) := fun y => (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i) y) : Eucl (m + 1))
  let K : Fin N → ℝ → Set (Eucl N) := fun j t => {x | x ≠ a ∧ ∃ c ∈ ball (0 : Eucl (m + 1)) t,
    (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i + c i • EuclideanSpace.single j (1 : ℝ)) (x - a)) : Eucl (m + 1)) = 0}
  let X : ℝ → ℝ → Set (Eucl N) := fun r s => {x | dist x a < r ∧ ‖L (x - a)‖ < s * ‖x - a‖}
  let F : ℝ → ℝ≥0∞ := fun s => ⨆ r ∈ Ioo (0 : ℝ) δ, μ (X r s) / ENNReal.ofReal ((r * s) ^ (m + 1))
  let Fj : Fin N → ℝ → ℝ≥0∞ := fun j t => ⨆ r ∈ Ioo (0 : ℝ) δ, μ (ball a r ∩ K j t) / ENNReal.ofReal ((r * t) ^ (m + 1))
  show (∀ j, limsup (Fj j) (𝓝[>] 0) ≤ limsup F (𝓝[>] 0)) ∧
    limsup F (𝓝[>] 0) ≤ ENNReal.ofReal (Real.sqrt (N : ℝ) ^ (m + 1)) * ∑ j : Fin N, limsup (Fj j) (𝓝[>] 0)
  -- fibre identity
  have hfib : ∀ (j : Fin N) (c : Eucl (m + 1)) (y : Eucl N),
      (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i + c i • EuclideanSpace.single j (1 : ℝ)) y) : Eucl (m + 1)) =
        L y + (y j) • c := by
    intro j c y
    ext i
    simp [L, inner_add_left, real_inner_smul_left, EuclideanSpace.inner_single_left, mul_comm]
  -- inclusion (ii)
  have hincl2 : ∀ (j : Fin N) (r t : ℝ), 0 < t → ball a r ∩ K j t ⊆ X r t := by
    rintro j r t ht x ⟨hxr, hxa, c, hc, hx0⟩
    refine ⟨hxr, ?_⟩
    rw [hfib] at hx0
    have hL : L (x - a) = -((x - a) j • c) := eq_neg_of_add_eq_zero_left hx0
    rw [hL, norm_neg, norm_smul]
    have hy : 0 < ‖x - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hxa)
    have hc' : ‖c‖ < t := by simpa using hc
    have hyj : ‖(x - a) j‖ ≤ ‖x - a‖ := PiLp.norm_apply_le _ _
    calc ‖(x - a) j‖ * ‖c‖ ≤ ‖x - a‖ * ‖c‖ := by gcongr
      _ < ‖x - a‖ * t := mul_lt_mul_of_pos_left hc' hy
      _ = t * ‖x - a‖ := mul_comm _ _
  refine ⟨fun j => ?_, ?_⟩
  · refine limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
    filter_upwards [self_mem_nhdsWithin] with t ht
    refine iSup₂_mono fun r hr => ?_
    exact ENNReal.div_le_div_right (measure_mono (hincl2 j r t ht)) _
  · rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      have hF0 : F = fun _ => 0 := by
        funext s
        have hX : ∀ r, X r s = ∅ := by
          intro r
          ext x
          have hxa : x - a = 0 := Subsingleton.elim _ _
          simp [X, hxa]
        simp [F, hX]
      rw [hF0, limsup_const]
      exact zero_le
    · set σ : ℝ := Real.sqrt (N : ℝ) with hσdef
      have hσ : 0 < σ := Real.sqrt_pos.2 (by exact_mod_cast hN)
      have hσsq : σ ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
      -- inclusion (i)
      have hincl1 : ∀ r s, 0 < s → X r s ⊆ ⋃ j, ball a r ∩ K j (σ * s) := by
        rintro r s hs x ⟨hxr, hx⟩
        set y := x - a with hydef
        have hy : 0 < ‖y‖ := by
          rcases (norm_nonneg y).lt_or_eq with h | h
          · exact h
          · exfalso
            rw [← h, mul_zero] at hx
            exact (norm_nonneg _).not_gt hx
        obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun j => ‖y j‖)
          (Finset.univ_nonempty_iff.2 ⟨⟨0, hN⟩⟩)
        have hsq : ‖y‖ ^ 2 ≤ (σ * ‖y j‖) ^ 2 := by
          rw [PiLp.norm_sq_eq_of_L2, mul_pow, hσsq]
          calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin N, ‖y j‖ ^ 2 :=
                Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hj i (Finset.mem_univ i)) 2
            _ = (N : ℝ) * ‖y j‖ ^ 2 := by simp
        have hle : ‖y‖ ≤ σ * ‖y j‖ :=
          (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
        have hyj : 0 < ‖y j‖ := by
          by_contra hcon
          have : ‖y j‖ = 0 := le_antisymm (not_lt.1 hcon) (norm_nonneg _)
          rw [this, mul_zero] at hle
          linarith
        have hyj0 : y j ≠ 0 := norm_pos_iff.1 hyj
        refine mem_iUnion.2 ⟨j, mem_ball.2 hxr, ?_, (-(y j)⁻¹) • L y, ?_, ?_⟩
        · intro h
          rw [hydef, h, sub_self, norm_zero] at hy
          exact lt_irrefl _ hy
        · rw [mem_ball_zero_iff, norm_smul, norm_neg, norm_inv]
          rw [inv_mul_lt_iff₀ hyj]
          calc ‖L y‖ < s * ‖y‖ := hx
            _ ≤ s * (σ * ‖y j‖) := by gcongr
            _ = ‖y j‖ * (σ * s) := by ring
        · rw [hfib, smul_smul, mul_neg, mul_inv_cancel₀ hyj0, neg_smul, one_smul, add_neg_cancel]
      -- pointwise bound
      have hpt : ∀ s, 0 < s → F s ≤ ENNReal.ofReal (σ ^ (m + 1)) * ∑ j, Fj j (σ * s) := by
        intro s hs
        refine iSup₂_le fun r hr => ?_
        have hc0 : ENNReal.ofReal (σ ^ (m + 1)) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
        have hA : ENNReal.ofReal ((r * (σ * s)) ^ (m + 1)) =
            ENNReal.ofReal (σ ^ (m + 1)) * ENNReal.ofReal ((r * s) ^ (m + 1)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow]
          congr 2
          ring
        calc μ (X r s) / ENNReal.ofReal ((r * s) ^ (m + 1))
            ≤ (∑ j, μ (ball a r ∩ K j (σ * s))) / ENNReal.ofReal ((r * s) ^ (m + 1)) := by
              refine ENNReal.div_le_div_right ?_ _
              exact (measure_mono (hincl1 r s hs)).trans (measure_iUnion_fintype_le μ _)
          _ = ∑ j, ENNReal.ofReal (σ ^ (m + 1)) *
                (μ (ball a r ∩ K j (σ * s)) / ENNReal.ofReal ((r * (σ * s)) ^ (m + 1))) := by
              rw [ENNReal.sum_div]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [hA, ← mul_div_assoc, ENNReal.mul_div_mul_left _ _ hc0 ENNReal.ofReal_ne_top]
          _ ≤ ∑ j, ENNReal.ofReal (σ ^ (m + 1)) * Fj j (σ * s) := by
              refine Finset.sum_le_sum fun j _ => ?_
              gcongr
              exact le_iSup₂ (f := fun r (_ : r ∈ Ioo (0 : ℝ) δ) =>
                μ (ball a r ∩ K j (σ * s)) / ENNReal.ofReal ((r * (σ * s)) ^ (m + 1))) r hr
          _ = ENNReal.ofReal (σ ^ (m + 1)) * ∑ j, Fj j (σ * s) := by rw [Finset.mul_sum]
      -- limsup of a sum
      have hadd : ∀ (v w : ℝ → ℝ≥0∞), limsup (fun s => v s + w s) (𝓝[>] (0 : ℝ)) ≤
          limsup v (𝓝[>] 0) + limsup w (𝓝[>] 0) := by
        intro v w
        refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt => ?_
        have hv : limsup v (𝓝[>] (0 : ℝ)) < ⊤ := lt_of_le_of_lt le_self_add hlt
        have hw : limsup w (𝓝[>] (0 : ℝ)) < ⊤ := lt_of_le_of_lt le_add_self hlt
        have hε2 : (ε : ℝ≥0∞) / 2 ≠ 0 := by
          simp [ENNReal.div_eq_zero_iff, hε.ne']
        refine limsup_le_of_le (by isBoundedDefault) ?_
        filter_upwards [eventually_lt_of_limsup_lt (ENNReal.lt_add_right hv.ne hε2),
          eventually_lt_of_limsup_lt (ENNReal.lt_add_right hw.ne hε2)] with x h1 h2
        calc v x + w x ≤ (limsup v (𝓝[>] 0) + (ε : ℝ≥0∞) / 2) + (limsup w (𝓝[>] 0) + (ε : ℝ≥0∞) / 2) :=
              add_le_add h1.le h2.le
          _ = limsup v (𝓝[>] 0) + limsup w (𝓝[>] 0) + ε := by
              rw [add_add_add_comm, ENNReal.add_halves]
      have hsum : ∀ (S : Finset (Fin N)) (h : Fin N → ℝ → ℝ≥0∞),
          limsup (fun s => ∑ j ∈ S, h j s) (𝓝[>] (0 : ℝ)) ≤ ∑ j ∈ S, limsup (h j) (𝓝[>] 0) := by
        intro S h
        induction S using Finset.induction_on with
        | empty => simp
        | insert j S hj ih =>
          simp only [Finset.sum_insert hj]
          exact (hadd (h j) (fun s => ∑ i ∈ S, h i s)).trans (add_le_add le_rfl ih)
      -- change of variables
      have hT : Tendsto (fun s : ℝ => σ * s) (𝓝[>] 0) (𝓝[>] 0) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, ?_⟩
        · have : Tendsto (fun s : ℝ => σ * s) (𝓝 0) (𝓝 (σ * 0)) :=
            ((continuous_const.mul continuous_id).tendsto 0)
          rw [mul_zero] at this
          exact this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with s hs
          exact mul_pos hσ hs
      have hcv : ∀ j, limsup (fun s => Fj j (σ * s)) (𝓝[>] (0 : ℝ)) ≤ limsup (Fj j) (𝓝[>] 0) := by
        intro j
        calc limsup (fun s => Fj j (σ * s)) (𝓝[>] (0 : ℝ))
            = limsup (Fj j) (map (fun s : ℝ => σ * s) (𝓝[>] 0)) := Filter.limsup_comp (Fj j) _ _
          _ ≤ limsup (Fj j) (𝓝[>] 0) := limsup_le_limsup_of_le hT (by isBoundedDefault) (by isBoundedDefault)
      calc limsup F (𝓝[>] 0) ≤ limsup (fun s => ENNReal.ofReal (σ ^ (m + 1)) * ∑ j, Fj j (σ * s)) (𝓝[>] 0) := by
            refine limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
            filter_upwards [self_mem_nhdsWithin] with s hs
            exact hpt s hs
        _ = ENNReal.ofReal (σ ^ (m + 1)) * limsup (fun s => ∑ j, Fj j (σ * s)) (𝓝[>] 0) :=
            ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (σ ^ (m + 1)) * ∑ j, limsup (fun s => Fj j (σ * s)) (𝓝[>] 0) := by
            gcongr
            exact hsum Finset.univ (fun j s => Fj j (σ * s))
        _ ≤ ENNReal.ofReal (σ ^ (m + 1)) * ∑ j, limsup (Fj j) (𝓝[>] 0) := by
            gcongr with j
            exact hcv j
```

## Key steps

1. Fibre identity L_{u⊕_jc}(y) = L_u(y) + y_jc.
2. (ii) B(a,r) ∩ K_j(t) ⊆ X_u(a,r,t), so F_j ≤ F pointwise and ϑ_j ≤ Φ.
3. N = 0: X_u = ∅ and Φ = 0.
4. (i) X_u(a,r,s) ⊆ ⋃_j B(a,r) ∩ K_j(√N s), using j with |y_j| ≥ |y|/√N and c = −L_u(y)/y_j. Hence F(s) ≤ (√N)ᵏ Σ_j F_j(√N s).
5. Constant factor, limsup of a finite sum (direct ε-argument) and the substitution t = √N s give Φ ≤ (√N)ᵏ Σ_j ϑ_j.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `git archive d8d46c9 into /tmp/bft-decomp-1791847446; cmp GMT/Ch06/Submission.lean (workspace) and project/GMT/Ch06/Contract.lean (snapshot) against the scratch copy (identical); lake build GMT.Ch06.Submission (success, 3152 jobs)`
- `rg -n 'theorem ae_ae_comm|theorem measurable_measure_prodMk_left |theorem _root_.Monotone.measure_iUnion|theorem _root_.Directed.measure_iUnion|theorem measure_biUnion_eq_iSup|theorem prod_apply_symm|theorem prod_apply |lemma IsSigmaCompact.image|theorem limsup_add_le|theorem limsup_const_mul_of_ne_top|theorem inner_single_left' local-references/197bdd4b88278494/mathlib/Mathlib`
- `rg -n 'measure_preimage_add_right|measure_univ_of_isAddLeftInvariant|measure_univ_of_isMulLeftInvariant' local-references/197bdd4b88278494/mathlib/Mathlib`
- `rg -n -i 'mickle|besicovitch.federer|purely.unrectifiable' local-references/197bdd4b88278494/mathlib/Mathlib local-references/197bdd4b88278494/project (no match); rg -n 'IsSigmaCompact.measurableSet' local-references/197bdd4b88278494/mathlib/Mathlib (no match)`
- `rg -n 'def dimensionalDensityQuotient|def realUnitBallVolume' lake-packages-25730c7c/simongmt/Poincare; sed -n 1,70p Chapter01/Densities.lean`
- `python3 verifier/gmt-compare.py contract_scope + child_modules (contract mode) for all 8 child statements; lake env lean Scratch/Chal_*.lean (0 errors)`
- `lake env lean Scratch/Names.lean and Scratch/Inst.lean (#check of the cited lemma names; instance checks for IsAddHaarMeasure, IsAddRightInvariant, SFinite of volume on Fin (m+1) → Eucl N, volume univ = ⊤ on Eucl (m+1), BorelSpace of the product types)`
- `lake env lean Scratch/Assembly.lean (parent from child stubs; #print axioms), Scratch/Iface1.lean (cone_ratio_measurable proved from the limsup_sup_measurable stub; ϑ_j instance), Scratch/Iface2.lean (OuterMeasure.mk + rectifiability_mickle_rado interface; later found vacuous because of a binder capture in the test example, and superseded by the complete slice_density_null proof)`
- `python3 lean_name collision scan of dag.json and nodes/*/decomposition-v*.json (658 names); byte comparison of reused lean_statement/title/statement against dag.json and the accepted handoffs`
- `lake env lean Verify/AllProofsFull.lean (independent reviewer's complete proofs of all six new children + accepted mickle_rado subtree + parent assembly; 0 errors; #print axioms [propext, Classical.choice, Quot.sound] for every declaration) and Verify/Standalone/<key>.lean for each new child with only its declared siblings stubbed (0 errors)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Group/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Filter/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-bf-trichotomy-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-mickle-rado-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-mickle-rado-a1-limsup-eq-iinf-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-mass-measure-rectifiable-a1/decomposition-v1.json`
- `/tmp/bft-decomp-1791847446/Scratch/Assembly.lean`
- `/tmp/bft-decomp-1791847446/Scratch/Iface1.lean`
- `/tmp/bft-decomp-1791847446/Verify/AllProofsFull.lean`
- `/tmp/bft-decomp-1791847446/Verify/Standalone/slice_density_null.lean`
- `/tmp/bft-decomp-1791847446/Verify/Standalone/limsup_sup_measurable.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 contract, byte-identical to the workspace Submission.lean and to the scratch copy. Neither the snapshot Mathlib nor the project contains a Besicovitch–Federer, Mickle–Radó or purely-unrectifiable result (rg: no match), and Mathlib has no IsSigmaCompact.measurableSet. So all six new child obligations are genuine; the two accepted declarations rectifiability_mickle_rado and rectifiability_mickle_rado_limsup_eq_iInf are reused with byte-identical types. Every library input cited by the child proofs exists in the pinned environment: measurable_measure_prodMk_left, Measure.prod_apply and prod_apply_symm, Measure.ae_ae_comm (Prod.lean), Monotone.measure_iUnion, Directed.measure_iUnion and measure_biUnion_eq_iSup (Continuity.lean), measure_preimage_add_right and measure_univ_of_isAddLeftInvariant (additive forms of Group/Measure.lean), ENNReal.limsup_const_mul_of_ne_top (Order/Filter/ENNReal.lean), IsSigmaCompact.image, EuclideanSpace.inner_single_left (PiL2.lean:318), and dimensionalDensityQuotient and realUnitBallVolume (SimonGMT Chapter01/Densities.lean:39, Hausdorff.lean:34). ENNReal.limsup_add_le (ENNReal.lean:231) requires CountableInterFilter, which 𝓝[>]0 is not, so fibre_cone_comparison proves limsup subadditivity directly. In the scratch build, all eight child types elaborate in the comparator's exact child scope. The parent compiles from the five stubbed children it uses. Complete single-declaration Lean proofs of all six new children compile against their exact frozen types, using only their declared siblings, and with the accepted mickle_rado subtree the whole tree including Submission.rectifiability_bf_trichotomy compiles with axioms [propext, Classical.choice, Quot.sound].
