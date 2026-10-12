# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.energy_lsc-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.energy_lsc-a1.duality_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is step 3 of the parent proof (duality bound), with the L² bookkeeping filled in. It uses the sibling children dorag_ha_lsc_grad_norm_sq, dorag_ha_lsc_ibp_lipschitz and dorag_ha_lsc_ibp_c1_ball.

Notation.
- μ is Lebesgue measure restricted to B. It is a finite measure, since B is bounded (measure_ball_lt_top).
- d(x) := Σ_i DΦ_i(x)(e_i) and G(x) := Σ_i Φ_i(x)².
- T := ∫_B Σ_i Dh(x)(e_i)Φ_i(x) dx and a_j := ∫_B Σ_i Du_j(x)(e_i)Φ_i(x) dx.
- f_j := u_j − c_j − W, and L_j is a Lipschitz constant of u_j.

1. (d and G.)
   - d is continuous, since each Φ_i is C¹. It vanishes outside the compact set ⋃_i tsupport Φ_i (fderiv_of_notMem_tsupport). So d has compact support and |d| ≤ C_d for some C_d (Continuous.bounded_above_of_compact_support).
   - Likewise G is continuous, G ≥ 0, G has compact support, and G ≤ C_G.
   - So d and √G are bounded measurable functions on the finite measure space (B, μ). Hence d, √G ∈ L²(μ) (MemLp.of_bound).
2. (Cauchy–Schwarz on B.) If f, g ∈ L²(μ), then |∫_B f g| ≤ √(∫_B f²)·√(∫_B g²).
   - First, |∫ fg| ≤ ∫ |f||g| (abs_integral_le_integral_abs, and |fg| = |f||g|).
   - Next, ∫ |f||g| ≤ (∫ |f|²)^{1/2}·(∫ |g|²)^{1/2}. This is Hölder with p = q = 2 (integral_mul_le_Lp_mul_Lq_of_nonneg with Real.HolderConjugate.two_two), applied to |f| and |g|, which lie in L²(μ) by MemLp.norm.
   - Finally, |f|² = f² and t^{1/2} = √t (Real.rpow_two, Real.sqrt_eq_rpow).
3. (Integrability.)
   (a) W ∈ L²(μ) ⊆ L¹(μ) because μ is finite (MemLp.integrable). Since d is bounded, W·d ∈ L¹(μ) (Integrable.mul_bdd).
   (b) u_j is continuous, so u_j·d and c_j·d are continuous with compact support. Hence they are integrable on ℝⁿ, and so on B.
   (c) For x ∈ B, |u_j(x) − c_j| ≤ |u_j(x) − u_j(0)| + |u_j(0)| + |c_j| ≤ L_j·R + |u_j(0)| + |c_j|. So u_j − c_j is bounded and measurable on B, hence in L²(μ). Therefore f_j ∈ L²(μ) (MemLp.sub).
4. (∫_B d = 0.) Apply dorag_ha_lsc_ibp_lipschitz to the constant function u ≡ 1, which is Lipschitz with constant 0 (LipschitzWith.const). Its derivative is 0 (fderiv_const_apply), so the left side is ∫_B 0 = 0, and the identity reads 0 = −∫_B 1·d. Hence ∫_B d = 0.
5. (T in terms of W.) By dorag_ha_lsc_ibp_c1_ball, T = −∫_B h·d. Since h = W μ-a.e., ∫_B h·d = ∫_B W·d (integral_congr_ae). So T = −∫_B W·d.
6. (a_j in terms of u_j.) By dorag_ha_lsc_ibp_lipschitz with u := u_j, a_j = −∫_B u_j·d.
7. (The difference.) Step 3 supplies the integrability needed for linearity, and step 4 removes the c_j term:
   ∫_B f_j·d = ∫_B u_j·d − c_j∫_B d − ∫_B W·d = ∫_B u_j·d − ∫_B W·d.
   Combined with steps 5 and 6, a_j − T = −∫_B f_j·d.
8. (a_j → T.) f_j ∈ L²(μ) by step 3 and d ∈ L²(μ) by step 1. So steps 7 and 2 give
   |a_j − T| ≤ √(∫_B f_j²)·√(∫_B d²).
   By hypothesis ∫_B f_j² → 0. Since √ is continuous with √0 = 0, the right side tends to 0, and a_j → T by squeezing (tendsto_iff_norm_sub_tendsto_zero, squeeze_zero).
9. (Uniform bound on a_j.) Fix j.
   - For each x, the second part of dorag_ha_lsc_grad_norm_sq with L := Du_j(x) and a_i := Φ_i(x) gives |Σ_i Du_j(x)(e_i)Φ_i(x)| ≤ ‖Du_j(x)‖·√G(x).
   - The right side is measurable (measurable_fderiv) and bounded by L_j·√C_G, since ‖Du_j(x)‖ ≤ L_j (norm_fderiv_le_of_lipschitz). So it is integrable on B (Integrable.of_bound), and |a_j| ≤ ∫_B ‖Du_j‖·√G (norm_integral_le_of_norm_le).
   - ‖Du_j‖ ∈ L²(μ) (measurable and bounded by L_j), and √G ∈ L²(μ). Step 2, together with (√G)² = G (G ≥ 0), gives ∫_B ‖Du_j‖·√G ≤ √(∫_B ‖Du_j‖²)·√(∫_B G).
   - Since ∫_B ‖Du_j‖² ≤ E and √ is monotone (Real.sqrt_le_sqrt), this is ≤ √E·√(∫_B G).
   Hence a_j ≤ |a_j| ≤ √E·√(∫_B G) for every j.
10. (Passage to the limit.) a_j → T (step 8) and a_j ≤ √E·√(∫_B G) for all j (step 9). So T ≤ √E·√(∫_B G) (le_of_tendsto'). Since G = Σ_i Φ_i², this is the claim. ∎

Appendix (Lean proof, kernel-checked). This proof was compiled against the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c). It was placed inside `namespace GMT.Ch07` -> `namespace Submission` of a copy of GMT/Ch07/Submission.lean at b4d606d, after the `noncomputable section ... end` block and before `main_theorem`. The contract's `open`s are in scope there. `#print axioms` gives only propext, Classical.choice and Quot.sound. Sibling children are referenced by their bare names.

theorem dorag_ha_lsc_duality_bound : ∀ (n : ℕ) (R E : ℝ) (u : ℕ → Euclid n → ℝ) (c : ℕ → ℝ) (W h : Euclid n → ℝ) (Φ : Fin n → Euclid n → ℝ), (∀ j, ∃ L : NNReal, LipschitzWith L (u j)) → (∀ j, ∫ x in ball (0 : Euclid n) R, ‖fderiv ℝ (u j) x‖ ^ 2 ≤ E) → MemLp W 2 (volume.restrict (ball (0 : Euclid n) R)) → Tendsto (fun j => ∫ x in ball (0 : Euclid n) R, (u j x - c j - W x) ^ 2) atTop (𝓝 0) → ContDiffOn ℝ 1 h (ball (0 : Euclid n) R) → (∀ᵐ x ∂(volume.restrict (ball (0 : Euclid n) R)), h x = W x) → (∀ i, ContDiff ℝ 1 (Φ i)) → (∀ i, HasCompactSupport (Φ i)) → (∀ i, tsupport (Φ i) ⊆ ball (0 : Euclid n) R) → ∫ x in ball (0 : Euclid n) R, ∑ i : Fin n, fderiv ℝ h x (EuclideanSpace.single i (1 : ℝ)) * Φ i x ≤ Real.sqrt E * Real.sqrt (∫ x in ball (0 : Euclid n) R, ∑ i : Fin n, Φ i x ^ 2) := by
  intro n R E u c W h Φ hu hE hW hconv hh hae hΦ hΦc hΦs
  set B := ball (0 : Euclid n) R with hBdef
  have : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  set d : Euclid n → ℝ := fun x => ∑ i : Fin n, fderiv ℝ (Φ i) x (EuclideanSpace.single i (1 : ℝ)) with hddef
  set G : Euclid n → ℝ := fun x => ∑ i : Fin n, Φ i x ^ 2 with hGdef
  -- regularity of d and G
  have hdC : Continuous d := continuous_finsetSum _ fun i _ =>
    ((hΦ i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdc : HasCompactSupport d := by
    refine HasCompactSupport.intro (isCompact_iUnion fun i => hΦc i) fun x hx => ?_
    refine Finset.sum_eq_zero fun i _ => ?_
    have : x ∉ tsupport (Φ i) := fun h' => hx (mem_iUnion.2 ⟨i, h'⟩)
    rw [fderiv_of_notMem_tsupport ℝ this]; rfl
  obtain ⟨Cd, hCd⟩ := hdC.bounded_above_of_compact_support hdc
  have hGC : Continuous G := continuous_finsetSum _ fun i _ => (hΦ i).continuous.pow 2
  have hGc : HasCompactSupport G := by
    refine HasCompactSupport.intro (isCompact_iUnion fun i => hΦc i) fun x hx => ?_
    refine Finset.sum_eq_zero fun i _ => ?_
    have : x ∉ tsupport (Φ i) := fun h' => hx (mem_iUnion.2 ⟨i, h'⟩)
    rw [image_eq_zero_of_notMem_tsupport this]; ring
  obtain ⟨CG, hCG⟩ := hGC.bounded_above_of_compact_support hGc
  have hG0 : ∀ x, 0 ≤ G x := fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  -- Cauchy–Schwarz on μ
  have CS : ∀ f g : Euclid n → ℝ, MemLp f 2 (volume.restrict B) → MemLp g 2 (volume.restrict B) →
      |∫ x in B, f x * g x| ≤ Real.sqrt (∫ x in B, f x ^ 2) * Real.sqrt (∫ x in B, g x ^ 2) := by
    intro f g hf hg
    have hf' : MemLp (fun x => |f x|) (ENNReal.ofReal 2) (volume.restrict B) := by
      simpa [Real.norm_eq_abs] using hf.norm
    have hg' : MemLp (fun x => |g x|) (ENNReal.ofReal 2) (volume.restrict B) := by
      simpa [Real.norm_eq_abs] using hg.norm
    have H := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (ae_of_all _ fun x => abs_nonneg (f x)) (ae_of_all _ fun x => abs_nonneg (g x)) hf' hg'
    calc |∫ x in B, f x * g x| ≤ ∫ x in B, |f x * g x| := abs_integral_le_integral_abs
      _ = ∫ x in B, |f x| * |g x| := by simp_rw [abs_mul]
      _ ≤ _ := H
      _ = _ := by simp_rw [Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow]
  have hdL2 : MemLp d 2 (volume.restrict B) := MemLp.of_bound hdC.aestronglyMeasurable Cd (ae_of_all _ hCd)
  -- integrability facts
  have hW1 : Integrable W (volume.restrict B) := hW.integrable one_le_two
  have hWd : Integrable (fun x => W x * d x) (volume.restrict B) :=
    hW1.mul_bdd hdC.aestronglyMeasurable (ae_of_all _ hCd)
  have hud : ∀ j, Integrable (fun x => u j x * d x) (volume.restrict B) := by
    intro j
    obtain ⟨L, hL⟩ := hu j
    exact ((hL.continuous.mul hdC).integrable_of_hasCompactSupport hdc.mul_left).integrableOn
  have hcd : ∀ j, Integrable (fun x => c j * d x) (volume.restrict B) := fun j =>
    ((continuous_const.mul hdC).integrable_of_hasCompactSupport hdc.mul_left).integrableOn
  -- ∫_B d = 0
  have hdiv0 : ∫ x in B, d x = 0 := by
    have := dorag_ha_lsc_ibp_lipschitz n R (fun _ => (1 : ℝ)) Φ ⟨0, LipschitzWith.const 1⟩ hΦ hΦc hΦs
    simp only [fderiv_const_apply, FunLike.coe_zero, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
      integral_zero, one_mul] at this
    linarith
  -- the limit
  set T := ∫ x in B, ∑ i : Fin n, fderiv ℝ h x (EuclideanSpace.single i (1 : ℝ)) * Φ i x with hTdef
  have hT : T = -∫ x in B, W x * d x := by
    rw [hTdef, dorag_ha_lsc_ibp_c1_ball n R h Φ hh hΦ hΦc hΦs]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  set a : ℕ → ℝ := fun j => ∫ x in B, ∑ i : Fin n, fderiv ℝ (u j) x (EuclideanSpace.single i (1 : ℝ)) * Φ i x with hadef
  have ha : ∀ j, a j = -∫ x in B, u j x * d x := fun j =>
    dorag_ha_lsc_ibp_lipschitz n R (u j) Φ (hu j) hΦ hΦc hΦs
  have hfL2 : ∀ j, MemLp (fun x => u j x - c j - W x) 2 (volume.restrict B) := by
    intro j
    obtain ⟨L, hL⟩ := hu j
    have hb : MemLp (fun x => u j x - c j) 2 (volume.restrict B) := by
      refine MemLp.of_bound ((hL.continuous.sub continuous_const).aestronglyMeasurable)
        (|u j 0| + L * R + |c j|) ?_
      refine (ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun x hx => ?_)
      have hx' : ‖x‖ < R := mem_ball_zero_iff.1 hx
      have h1 : |u j x - u j 0| ≤ L * ‖x‖ := by
        simpa [Real.dist_eq, dist_zero_right] using hL.dist_le_mul x 0
      have h2 : (L : ℝ) * ‖x‖ ≤ L * R := mul_le_mul_of_nonneg_left hx'.le L.coe_nonneg
      rw [Real.norm_eq_abs]
      calc |u j x - c j| ≤ |u j x - u j 0| + |u j 0| + |c j| := by
              have := abs_sub (u j x) (c j)
              have := abs_sub_abs_le_abs_sub (u j x) (u j 0)
              have := abs_add_le (u j x - u j 0) (u j 0)
              simp only [sub_add_cancel] at this
              linarith
        _ ≤ |u j 0| + L * R + |c j| := by linarith
    exact hb.sub hW
  have hdiff : ∀ j, a j - T = -∫ x in B, (u j x - c j - W x) * d x := by
    intro j
    rw [ha j, hT]
    have e1 : ∫ x in B, (u j x - c j - W x) * d x
        = (∫ x in B, u j x * d x) - c j * (∫ x in B, d x) - ∫ x in B, W x * d x := by
      have hI1 : Integrable (fun x => u j x * d x - c j * d x) (volume.restrict B) := (hud j).sub (hcd j)
      simp_rw [sub_mul]
      rw [integral_sub hI1 hWd, integral_sub (hud j) (hcd j), integral_const_mul]
    rw [e1, hdiv0]; ring
  have hbound : ∀ j, |a j - T| ≤ Real.sqrt (∫ x in B, (u j x - c j - W x) ^ 2) * Real.sqrt (∫ x in B, d x ^ 2) := by
    intro j
    rw [hdiff j, abs_neg]
    exact CS _ _ (hfL2 j) hdL2
  have hlim : Tendsto a atTop (𝓝 T) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun j => norm_nonneg _) (fun j => (Real.norm_eq_abs _).trans_le (hbound j)) ?_
    have := (hconv.sqrt).mul_const (Real.sqrt (∫ x in B, d x ^ 2))
    simpa using this
  -- uniform bound on a j
  have hGsqrt : MemLp (fun x => Real.sqrt (G x)) 2 (volume.restrict B) :=
    MemLp.of_bound (hGC.sqrt.aestronglyMeasurable) (Real.sqrt CG) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt ((le_abs_self _).trans ((Real.norm_eq_abs _).symm.trans_le (hCG x))))
  have habound : ∀ j, a j ≤ Real.sqrt E * Real.sqrt (∫ x in B, G x) := by
    intro j
    obtain ⟨L, hL⟩ := hu j
    have hDuL2 : MemLp (fun x => ‖fderiv ℝ (u j) x‖) 2 (volume.restrict B) :=
      MemLp.of_bound ((measurable_fderiv ℝ (u j)).norm.aestronglyMeasurable) L
        (ae_of_all _ fun x => by rw [norm_norm]; exact norm_fderiv_le_of_lipschitz ℝ hL)
    have hprodI : Integrable (fun x => ‖fderiv ℝ (u j) x‖ * Real.sqrt (G x)) (volume.restrict B) :=
      Integrable.of_bound ((measurable_fderiv ℝ (u j)).norm.aestronglyMeasurable.mul
        hGC.sqrt.aestronglyMeasurable) (L * Real.sqrt CG) (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))]
          refine mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hL) ?_ (Real.sqrt_nonneg _) L.coe_nonneg
          exact Real.sqrt_le_sqrt ((le_abs_self _).trans ((Real.norm_eq_abs _).symm.trans_le (hCG x))))
    have h1 : |a j| ≤ ∫ x in B, ‖fderiv ℝ (u j) x‖ * Real.sqrt (G x) := by
      rw [← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le hprodI (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs]
      exact (dorag_ha_lsc_grad_norm_sq n (fderiv ℝ (u j) x)).2 (fun i => Φ i x)
    have h2 : ∫ x in B, ‖fderiv ℝ (u j) x‖ * Real.sqrt (G x)
        ≤ Real.sqrt (∫ x in B, ‖fderiv ℝ (u j) x‖ ^ 2) * Real.sqrt (∫ x in B, G x) := by
      have := CS _ _ hDuL2 hGsqrt
      have hG2 : ∀ x, Real.sqrt (G x) ^ 2 = G x := fun x => Real.sq_sqrt (hG0 x)
      simp_rw [hG2] at this
      exact (le_abs_self _).trans this
    have h3 : Real.sqrt (∫ x in B, ‖fderiv ℝ (u j) x‖ ^ 2) ≤ Real.sqrt E := Real.sqrt_le_sqrt (hE j)
    calc a j ≤ |a j| := le_abs_self _
      _ ≤ _ := h1
      _ ≤ _ := h2
      _ ≤ Real.sqrt E * Real.sqrt (∫ x in B, G x) :=
          mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _)
  exact le_of_tendsto' hlim habound

## Key steps

1. d = divΦ and G = |Φ|² are continuous, compactly supported and bounded; Cauchy–Schwarz on B via Hölder with p = q = 2.
2. ∫_B divΦ = 0 (Lipschitz IBP with u ≡ 1); T = −∫_B W·divΦ (C¹ IBP and h = W a.e.); a_j = −∫_B u_j·divΦ (Lipschitz IBP).
3. a_j − T = −∫_B (u_j − c_j − W)·divΦ, so |a_j − T| ≤ ‖u_j − c_j − W‖_{L²(B)}·‖divΦ‖_{L²(B)} → 0.
4. Pointwise |∇u_j·Φ| ≤ ‖Du_j‖·|Φ| plus Cauchy–Schwarz gives a_j ≤ √E·‖Φ‖_{L²(B)}; pass to the limit.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json  (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; cmp GMT/Ch07/Contract.lean <snapshot>/project/GMT/Ch07/Contract.lean  (both IDENTICAL; git HEAD b4d606d)`
- `sed -n 150,200p Analysis/Calculus/Rademacher.lean; rg -n 'theorem|lemma' Analysis/Calculus/Rademacher.lean  (LipschitzWith.integral_lineDeriv_mul_eq :169, LipschitzWith.ae_differentiableAt :385)`
- `rg -n 'theorem (ContDiff.lipschitzWith_of_hasCompactSupport|exists_pos_lt_subset_ball|exists_lt_subset_ball|support_fderiv_subset|norm_fderiv_le_of_lipschitz|measurable_fderiv|measurable_fderiv_apply_const|integral_mul_le_Lp_mul_Lq_of_nonneg|ContDiffOn.fderiv_of_isOpen|ContDiffOn.continuousOn_fderiv_of_isOpen)' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem (one_of_mem_closedBall|support_eq|tsupport_eq|nonneg|nonneg.|le_one|contDiff|hasCompactSupport)' Analysis/Calculus/BumpFunction/Basic.lean; rg -n hasContDiffBump_of_innerProductSpace Analysis/`
- `rg -n 'setLIntegral_iUnion_of_directed|restrict_iUnion_apply_eq_iSup|lintegral_iSup|lintegral_iUnion' MeasureTheory`
- `rg -n 'toDual_symm_apply|EuclideanSpace.(norm_eq|norm_sq_eq|real_norm_sq_eq|inner_single_left|single_apply)' Analysis/InnerProductSpace; rg -n sum_mul_le_sqrt_mul_sqrt Analysis/Real/Sqrt.lean; rg -n two_two Basic/Real/ConjExponents.lean`
- `rg -n 'MemLp.of_bound|Integrable.of_bound|Integrable.mul_bdd|Integrable.bdd_mul|abs_integral_le_integral_abs|norm_integral_le_of_norm_le|fderiv_of_notMem_tsupport|notMem_mulTSupport_iff_eventuallyEq|Continuous.bounded_above_of_compact_support|IntegrableOn.of_forall_sdiff_eq_zero|integral_finsetSum|isFiniteMeasure_restrict|measure_ball_lt_top|isCompact_iUnion|Filter.EventuallyEq.fderiv_eq|DifferentiableAt.lineDeriv_eq_fderiv' <snapshot>/mathlib/Mathlib`
- `rg -l 'integral_lineDeriv_mul_eq|lineDeriv' <snapshot>/project  (no match); rg -l 'integral_lineDeriv_mul_eq|ContDiffBump|setLIntegral_iUnion_of_directed|toDual_symm_apply' .lake/packages/simongmt  (only mollifier/Whitney-bump/L1-dual uses, no IBP lemma); rg -n -i 'theorem .*(ibp|integration_by_parts|divergence)' .lake/packages/simongmt  (only varifold tangential-divergence lemmas)`
- `python3 -I scan of every lean_name in dag.json, nodes/*/*.json and issue-workers.json (566 names) for the 6 proposed dorag_ha_lsc_* names (no collision); sibling node statements printed from dag.json (all siblings still decomposing, none reusable)`
- `python3 -I import of verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch07.main_theorem') to replay the comparator child scope`
- `lean (toolchains/lean-4.35.0-rc3-linux/bin/lean; LEAN_PATH = workspace .lake/build + .lake/packages builds): /tmp/energylsc-decomp/Children.lean (stubs + parent assembly), ChildB.lean, ChildAF.lean, ChildBC.lean, ChildAFE.lean, ChildD.lean, Full2.lean (#print axioms), Challenge.lean (exact comparator challenge scope), insitu/ (modified Submission compiled with `lean --root=src -o build/GMT/Ch07/Submission.olean` + NodeSolution `exact Submission.X` checks)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-6c5873a6f5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/InnerProduct.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/ProperSpace/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Real/Sqrt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/Real/ConjExponents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/tmp/energylsc-decomp/Full2.lean`
- `/tmp/energylsc-decomp/Challenge.lean`
- `/tmp/energylsc-decomp/insitu/src/GMT/Ch07/Submission.lean`
- `/tmp/energylsc-decomp/insitu/NodeSolution.lean`

The snapshot pins project b4d606d and Mathlib 25730c7c. GMT/Ch07/Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

The pinned Mathlib supplies every tool the children need:
- Lipschitz integration by parts and Rademacher: LipschitzWith.integral_lineDeriv_mul_eq, LipschitzWith.ae_differentiableAt, DifferentiableAt.lineDeriv_eq_fderiv;
- C¹_c ⇒ Lipschitz: ContDiff.lipschitzWith_of_hasCompactSupport (its argument is `n ≠ 0`);
- bump functions on Euclid n: ContDiffBump with one_of_mem_closedBall, tsupport_eq, nonneg', le_one, hasCompactSupport and contDiff;
- exists_pos_lt_subset_ball;
- the Riesz isometry: InnerProductSpace.toDual_symm_apply, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.inner_single_left;
- finite Cauchy–Schwarz: Real.sum_mul_le_sqrt_mul_sqrt;
- Hölder: integral_mul_le_Lp_mul_Lq_of_nonneg with Real.HolderConjugate.two_two;
- monotone exhaustion: setLIntegral_iUnion_of_directed;
- MemLp.of_bound, Integrable.of_bound, Integrable.mul_bdd, Integrable.bdd_mul, fderiv_of_notMem_tsupport, notMem_tsupport_iff_eventuallyEq and integral_finsetSum (integral_finset_sum is deprecated).

Nothing is reusable from the project or SimonGMT. The project has no lineDeriv/IBP lemma. SimonGMT uses ContDiffBump only for mollifiers and Whitney bumps, and its divergence results are varifold tangential-divergence lemmas. No comparator-accepted declaration has an identical type, and the six dorag_ha_lsc_* names are unreserved.

Lean results:
- every child type elaborates in the comparator's replayed scope;
- all six children are fully proved;
- the exact frozen parent type follows from them;
- in-situ NodeSolution checks (`exact Submission.X`) against a compiled copy of GMT.Ch07.Submission pass, with axioms [propext, Classical.choice, Quot.sound] only.
