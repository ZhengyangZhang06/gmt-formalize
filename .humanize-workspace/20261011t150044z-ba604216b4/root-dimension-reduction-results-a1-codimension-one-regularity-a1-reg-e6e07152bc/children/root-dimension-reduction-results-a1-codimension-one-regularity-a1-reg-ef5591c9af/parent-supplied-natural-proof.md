# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.graph_chart-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.graph_chart-a1.orientation_along_graph-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 6, (6a)–(6e), of the parent proof of codim1_rdo_graph_chart, with the graph data (u C¹ on D, u ⊥ range ι, graph in N, u(0) = 0, Du(0) = 0) and the normalization ξN(x) = ιe_0∧…∧ιe_n of parent step 1 taken as hypotheses. Siblings used: gram_unit_orientation (Submission.codim1_rdo_gc_gram_unitOrientation) for (6c); the accepted orientation_sign (Submission.rsdic_unitOrientation_eq_or_eq_neg) for (6d); the accepted unit_orientation_dual (Submission.dor_ims_unitOrientation_dual) for the map L of (6e); the accepted chart_range_subset_tangent (Submission.dsmc_chart_range_subset_tangentSpace) for the curves of (6b); and the accepted covector_eval_continuous (Submission.dgoj_exists_continuous_covector_eval) for the continuity of (b_i) ↦ (α ↦ α(b_0, …, b_n)) used in (6e).

Notation. m := n + 1; G(v) := x + ιv + u(v); A(v) := ι + Du(v), a continuous linear map ℝ^m → ℝ^P; a(v) := (A(v)e_0, …, A(v)e_n), so a_i(v) = ιe_i + Du(v)e_i; Γ(v) := det(⟨a_i(v), a_j(v)⟩)_{i,j}; J(v) := √Γ(v).

Proof.
1. (Calculus.) D is open and u is C¹ on D. Hence for v ∈ D: u is differentiable at v with derivative Du(v); G has derivative A(v) at v (sum of the constant x, the continuous linear map ι and u), so DG(v)e_i = a_i(v); v ↦ Du(v) is continuous on D (ContDiffOn.continuousOn_fderiv_of_isOpen); and G is C¹ on D.
2. (Du(v) ⊥ range ι; parent (6a).) Fix v ∈ D and w ∈ ℝ^m. The real function v' ↦ ⟨ιw, u(v')⟩ vanishes on the open set D ∋ v, so its derivative at v, c ↦ ⟨ιw, Du(v)c⟩, is the derivative of the zero function, i.e. 0 (HasFDerivAt.congr_of_eventuallyEq and uniqueness of derivatives). Thus ⟨ιw, Du(v)c⟩ = 0 for all w, c.
3. (Injectivity; parent (6a).) For v ∈ D and c ∈ ℝ^m, step 2 gives ‖A(v)c‖² = ‖ιc‖² + 2⟨ιc, Du(v)c⟩ + ‖Du(v)c‖² = ‖c‖² + ‖Du(v)c‖² ≥ ‖c‖². So A(v)c = 0 implies c = 0: A(v) is injective. Hence a(v), the image of the standard basis under the injective linear map A(v), is linearly independent (LinearIndependent.map').
4. (Pointwise unit orientation; parent (6c).) Let ev : (Fin m → ℝ^P) → MultiVector P m be the continuous map with ev(c)(α) = α(c) from covector_eval_continuous. For v ∈ D, gram_unit_orientation applied to the linearly independent family a(v) gives Γ(v) > 0, so J(v) > 0. Define η(v) := J(v)⁻¹·ev(a(v)). Then η(v)(α)·J(v) = J(v)⁻¹α(a(v))·J(v) = α(a(v)) for every α, so by gram_unit_orientation again, η(v) is a unit orientation of S_v := span{a_0(v), …, a_n(v)}.
5. (Tangent space; parent (6b).) Let v ∈ D. IsOrientation at G(v) ∈ N gives a subspace Q_v with (Q_v as a set) = tangentSpace N (G(v)) and ξN(G(v)) a unit orientation of Q_v. chart_range_subset_tangent (with r = 1, the open set D, the C¹ map G and G(D) ⊆ N) gives range DG(v) ⊆ tangentSpace N (G(v)) = Q_v; in particular a_i(v) = DG(v)e_i ∈ Q_v for every i, so S_v ≤ Q_v. Now dim S_v = m because a(v) is linearly independent, and dim Q_v = m because Q_v is spanned by the orthonormal (hence linearly independent) m-family τ from IsUnitOrientationOf. Hence S_v = Q_v (Submodule.eq_of_le_of_finrank_eq), and η(v) is a unit orientation of Q_v.
6. (Sign; parent (6d).) By orientation_sign applied to the unit orientations η(v) and ξN(G(v)) of Q_v: ξN(G(v)) = η(v) or ξN(G(v)) = −η(v), for every v ∈ D.
7. (A continuous sign function; parent (6e).) Let L : MultiVector P m → Covector(ℝ^P, m) be the continuous linear map of unit_orientation_dual; since η(v) is a unit orientation (step 4), η(v)(L(η(v))) = 1 for v ∈ D. Put s(v) := ξN(G(v))(L(η(v))). By step 6, s(v) = 1 or s(v) = −1 for every v ∈ D. s is continuous on D:
 - v ↦ ξN(G(v)) is continuous on D, because ξN is continuous on N (IsOrientation) and G is continuous on D with G(D) ⊆ N;
 - v ↦ a(v) is continuous on D (a_i(v) = ιe_i + Du(v)e_i with Du continuous on D), hence v ↦ ev(a(v)) is continuous on D; Γ is continuous on D (determinant of a matrix with continuous entries ⟨a_i(v), a_j(v)⟩), so J = √Γ is continuous and positive on D and v ↦ J(v)⁻¹ is continuous on D; hence η is continuous on D;
 - L is continuous, and evaluation (ξ, β) ↦ ξ(β) is jointly continuous, so s is continuous on D (ContinuousOn.clm_apply).
8. (Value at the centre.) 0 ∈ D since δ > 0. G(0) = x + ι0 + u(0) = x. Since Du(0) = 0, a_i(0) = ιe_i, and ⟨ιe_i, ιe_j⟩ = ⟨e_i, e_j⟩ = δ_ij (ι is an isometry), so the Gram matrix at 0 is the identity, Γ(0) = 1 and J(0) = 1. Hence η(0)(α) = α(ιe_0, …, ιe_n) = ξN(x)(α) for every α, i.e. η(0) = ξN(x) = ξN(G(0)), and s(0) = η(0)(L(η(0))) = 1.
9. (Connectedness.) D is convex, hence preconnected. Suppose s(v₁) = −1 for some v₁ ∈ D. By the intermediate value theorem on the preconnected set D (IsPreconnected.intermediate_value with the points v₁ and 0), the value 0 ∈ [−1, 1] = [s(v₁), s(0)] is attained: s(w) = 0 for some w ∈ D. This contradicts s(w) ∈ {1, −1}. Hence s(v) = 1 for every v ∈ D.
10. (Conclusion.) Let v ∈ D. If ξN(G(v)) = −η(v), then s(v) = −η(v)(L(η(v))) = −1, contradicting step 9. So by step 6, ξN(G(v)) = η(v). Therefore, for every (n+1)-covector α, ξN(x + ιv + u(v))(α)·J(v) = η(v)(α)·J(v) = α(a(v)) = α(ιe_0 + Du(v)e_0, …, ιe_n + Du(v)e_n). ∎

Formalization note (verified). The following Lean proof was compiled against the frozen import closure of GMT/Ch07/Submission.lean (Lean 4.35.0-rc3, Mathlib 25730c7c), with the five listed prerequisites present, as a single appended declaration inside namespace GMT.Ch07 before main_theorem; #print axioms gives propext, Classical.choice, Quot.sound; it passes the runtime leaf-delta check (check_source_delta). It may be used verbatim:

theorem Submission.codim1_rdo_gc_orientation_along_graph : ∀ (P n : ℕ) (N : Set (Euclid P)) (ξN : Euclid P → MultiVector P (n + 1)) (x : Euclid P) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid P) (u : Euclid (n + 1) → Euclid P) (δ : ℝ), IsOrientation (n + 1) N ξN → (∀ α : Covector (Euclid P) (n + 1), ξN x α = α (fun i => ι (EuclideanSpace.single i 1))) → 0 < δ → u 0 = 0 → fderiv ℝ u 0 = 0 → ContDiffOn ℝ 1 u (ball 0 δ) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ, ∀ w : Euclid (n + 1), inner ℝ (ι w) (u v) = 0) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ, x + ι v + u v ∈ N) → ∀ v ∈ ball (0 : Euclid (n + 1)) δ, ∀ α : Covector (Euclid P) (n + 1), ξN (x + ι v + u v) α * Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (n + 1) => inner ℝ (ι (EuclideanSpace.single i 1) + fderiv ℝ u v (EuclideanSpace.single i 1)) (ι (EuclideanSpace.single j 1) + fderiv ℝ u v (EuclideanSpace.single j 1)))) = α (fun i => ι (EuclideanSpace.single i 1) + fderiv ℝ u v (EuclideanSpace.single i 1)) := by
  intro P n N ξN x ι u δ hξ hιξ hδ hu0 hDu0 hu horth hmem
  set D := ball (0 : Euclid (n + 1)) δ with hD
  have hDopen : IsOpen D := isOpen_ball
  let e : Fin (n + 1) → Euclid (n + 1) := fun i => EuclideanSpace.single i 1
  let G : Euclid (n + 1) → Euclid P := fun v => x + ι v + u v
  let A : Euclid (n + 1) → (Euclid (n + 1) →L[ℝ] Euclid P) :=
    fun v => ι.toContinuousLinearMap + fderiv ℝ u v
  let a : Euclid (n + 1) → Fin (n + 1) → Euclid P := fun v i => ι (e i) + fderiv ℝ u v (e i)
  let gram : Euclid (n + 1) → ℝ := fun v => Matrix.det (Matrix.of fun i j => inner ℝ (a v i) (a v j))
  let J : Euclid (n + 1) → ℝ := fun v => Real.sqrt (gram v)
  have hudiff : ∀ v ∈ D, HasFDerivAt u (fderiv ℝ u v) v := fun v hv =>
    ((hu.contDiffAt (hDopen.mem_nhds hv)).differentiableAt (by norm_num)).hasFDerivAt
  have hGderiv : ∀ v ∈ D, HasFDerivAt G (A v) v := fun v hv => by
    have h1 : HasFDerivAt (fun v : Euclid (n + 1) => x + ι v) ι.toContinuousLinearMap v :=
      (ι.toContinuousLinearMap.hasFDerivAt).const_add x
    exact h1.add (hudiff v hv)
  have hAe : ∀ v ∈ D, ∀ i, fderiv ℝ G v (e i) = a v i := fun v hv i => by
    rw [(hGderiv v hv).fderiv]; rfl
  have hDuc : ContinuousOn (fderiv ℝ u) D := hu.continuousOn_fderiv_of_isOpen hDopen le_rfl
  have hGc : ContDiffOn ℝ 1 G D :=
    (contDiffOn_const.add ι.toContinuousLinearMap.contDiff.contDiffOn).add hu
  -- derivative of u is orthogonal to range ι
  have hDorth : ∀ v ∈ D, ∀ w a', inner ℝ (ι w) (fderiv ℝ u v a') = 0 := by
    intro v hv w a'
    have hloc : (fun v' => inner ℝ (ι w) (u v')) =ᶠ[𝓝 v] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (hDopen.mem_nhds hv) (fun v' hv' => horth v' hv' w)
    have hd : HasFDerivAt (fun v' => inner ℝ (ι w) (u v'))
        ((innerSL ℝ (ι w)).comp (fderiv ℝ u v)) v :=
      (innerSL ℝ (ι w)).hasFDerivAt.comp v (hudiff v hv)
    have hd0 : HasFDerivAt (fun v' => inner ℝ (ι w) (u v')) (0 : Euclid (n + 1) →L[ℝ] ℝ) v :=
      (hasFDerivAt_const (0 : ℝ) v).congr_of_eventuallyEq hloc
    have h2 := congrArg (fun L => L a') (hd.unique hd0)
    simpa using h2
  -- injectivity and linear independence
  have hnorm : ∀ v ∈ D, ∀ c : Euclid (n + 1), ‖c‖ ^ 2 ≤ ‖A v c‖ ^ 2 := by
    intro v hv c
    have h1 : A v c = ι c + fderiv ℝ u v c := rfl
    rw [h1, norm_add_sq_real, hDorth v hv c c, LinearIsometry.norm_map]
    nlinarith [sq_nonneg ‖fderiv ℝ u v c‖]
  have hinj : ∀ v ∈ D, Injective (A v) := by
    intro v hv c₁ c₂ h12
    have h1 := hnorm v hv (c₁ - c₂)
    rw [map_sub, h12, sub_self, norm_zero] at h1
    have h2 : ‖c₁ - c₂‖ = 0 := by nlinarith [norm_nonneg (c₁ - c₂)]
    exact sub_eq_zero.mp (norm_eq_zero.mp h2)
  have hlin : ∀ v ∈ D, LinearIndependent ℝ (a v) := by
    intro v hv
    have hb := (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.linearIndependent
    have hker : LinearMap.ker (A v : Euclid (n + 1) →ₗ[ℝ] Euclid P) = ⊥ :=
      LinearMap.ker_eq_bot.mpr (hinj v hv)
    have := hb.map' (A v : Euclid (n + 1) →ₗ[ℝ] Euclid P) hker
    convert this using 1
    funext i
    simp [a, A, e]
  -- pointwise orientation
  obtain ⟨ev, hevc, hev⟩ := Submission.dgoj_exists_continuous_covector_eval P (n + 1)
  let η : Euclid (n + 1) → MultiVector P (n + 1) := fun v => (J v)⁻¹ • ev (a v)
  have hgpos : ∀ v ∈ D, 0 < gram v := fun v hv =>
    (Submission.codim1_rdo_gc_gram_unitOrientation P (n + 1) (a v) (hlin v hv)).1
  have hJpos : ∀ v ∈ D, 0 < J v := fun v hv => Real.sqrt_pos.2 (hgpos v hv)
  have hηJ : ∀ v ∈ D, ∀ α, η v α * J v = α (a v) := by
    intro v hv α
    simp only [η, smul_apply, hev, smul_eq_mul]
    field_simp [(hJpos v hv).ne']
  have hηunit : ∀ v ∈ D, IsUnitOrientationOf (η v) (Submodule.span ℝ (Set.range (a v))) :=
    fun v hv => (Submission.codim1_rdo_gc_gram_unitOrientation P (n + 1) (a v) (hlin v hv)).2 _
      (hηJ v hv)
  -- tangent space identification
  have hrange := Submission.dsmc_chart_range_subset_tangentSpace P 1 (n + 1) N D G le_rfl hDopen
    (by simpa using hGc) (by rintro _ ⟨v, hv, rfl⟩; exact hmem v hv)
  have hsign : ∀ v ∈ D, ξN (G v) = η v ∨ ξN (G v) = -η v := by
    intro v hv
    obtain ⟨Q, hQ, hQξ⟩ := hξ.2 (G v) (hmem v hv)
    have hle : Submodule.span ℝ (Set.range (a v)) ≤ Q := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have h1 : a v i ∈ tangentSpace N (G v) := hrange v hv ⟨e i, hAe v hv i⟩
      rw [← hQ] at h1
      exact h1
    have hfin1 : Module.finrank ℝ (Submodule.span ℝ (Set.range (a v))) = n + 1 := by
      rw [finrank_span_eq_card (hlin v hv)]; simp
    have hfin2 : Module.finrank ℝ Q = n + 1 := by
      obtain ⟨τ, hτ, hτspan, -⟩ := hQξ
      rw [← hτspan, finrank_span_eq_card hτ.linearIndependent]; simp
    have hEq := Submodule.eq_of_le_of_finrank_eq hle (hfin1.trans hfin2.symm)
    have hηQ : IsUnitOrientationOf (η v) Q := hEq ▸ hηunit v hv
    exact Submission.rsdic_unitOrientation_eq_or_eq_neg P (n + 1) (η v) (ξN (G v)) Q hηQ hQξ
  -- the sign function
  obtain ⟨L, hL⟩ := Submission.dor_ims_unitOrientation_dual P (n + 1)
  have hηL : ∀ v ∈ D, η v (L (η v)) = 1 := fun v hv => (hL _ _ (hηunit v hv)).2.2
  let s : Euclid (n + 1) → ℝ := fun v => ξN (G v) (L (η v))
  have hs : ∀ v ∈ D, s v = 1 ∨ s v = -1 := by
    intro v hv
    rcases hsign v hv with h | h
    · left; simp only [s, h]; exact hηL v hv
    · right; simp only [s, h, neg_apply]; rw [hηL v hv]
  -- continuity
  have hGcont : ContinuousOn G D := hGc.continuousOn
  have hξG : ContinuousOn (fun v => ξN (G v)) D := hξ.1.comp hGcont (fun v hv => hmem v hv)
  have hac : ContinuousOn a D := continuousOn_pi.2 fun i =>
    continuousOn_const.add (hDuc.clm_apply continuousOn_const)
  have hgramc : ContinuousOn gram D := by
    have hM : ContinuousOn (fun v => (Matrix.of fun i j => inner ℝ (a v i) (a v j) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) D :=
      continuousOn_pi.2 fun i => continuousOn_pi.2 fun j =>
        ((continuousOn_pi.1 hac) i).inner ((continuousOn_pi.1 hac) j)
    exact (continuous_id.matrix_det).comp_continuousOn hM
  have hJc : ContinuousOn J D := Real.continuous_sqrt.comp_continuousOn hgramc
  have hηc : ContinuousOn η D :=
    (hJc.inv₀ (fun v hv => (hJpos v hv).ne')).smul (hevc.comp_continuousOn hac)
  have hsc : ContinuousOn s D := hξG.clm_apply (L.continuous.comp_continuousOn hηc)
  -- value at the centre
  have h0D : (0 : Euclid (n + 1)) ∈ D := mem_ball_self hδ
  have hG0 : G 0 = x := by simp [G, hu0]
  have ha0 : a 0 = fun i => ι (e i) := by funext i; simp [a, hDu0]
  have hgram0 : gram 0 = 1 := by
    have hM : (Matrix.of fun i j => inner ℝ (a 0 i) (a 0 j) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) = 1 := by
      ext i j
      rw [ha0, Matrix.of_apply, LinearIsometry.inner_map_map, Matrix.one_apply]
      simp [e, EuclideanSpace.inner_single_left]
    simp only [gram, hM, Matrix.det_one]
  have hJ0 : J 0 = 1 := by simp [J, hgram0]
  have hη0 : η 0 = ξN x := by
    ext α
    simp only [η, hJ0, inv_one, one_smul, hev, ha0, hιξ]
    rfl
  have hs0 : s 0 = 1 := by
    show ξN (G 0) (L (η 0)) = 1
    rw [hG0, ← hη0]; exact hηL 0 h0D
  have hsconst : ∀ v ∈ D, s v = 1 := by
    intro v hv
    rcases hs v hv with h | h
    · exact h
    · exfalso
      have hpre : IsPreconnected D := (convex_ball (0 : Euclid (n + 1)) δ).isPreconnected
      have hivt := hpre.intermediate_value hv h0D hsc
      rw [h, hs0] at hivt
      obtain ⟨w, hw, hw0⟩ := hivt (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num)
      rcases hs w hw with h' | h' <;> rw [hw0] at h' <;> norm_num at h'
  -- conclusion
  intro v hv α
  have hpos : ξN (G v) = η v := by
    rcases hsign v hv with h | h
    · exact h
    · exfalso
      have h1 := hsconst v hv
      simp only [s, h, neg_apply] at h1
      rw [hηL v hv] at h1
      norm_num at h1
  show ξN (G v) α * J v = α (a v)
  rw [hpos]
  exact hηJ v hv α

## Key steps

1. Du(v) ⊥ range ι (the derivative of v' ↦ ⟨ιw, u(v')⟩ ≡ 0), so ‖A(v)c‖ ≥ ‖c‖ and a(v) is linearly independent.
2. η(v) := J(v)⁻¹ ev(a(v)) is a unit orientation of span a(v) (gram_unit_orientation); span a(v) = T_{G v}N by range DG(v) ⊆ T_{G v}N (chart_range_subset_tangent) and equal dimensions.
3. orientation_sign gives ξN(G v) = ±η(v).
4. s(v) = ξN(G v)(L η(v)) ∈ {±1} is continuous on D (continuity of ξN on N, ev, J), and s(0) = 1 because G(0) = x, a(0) = ιe, J(0) = 1.
5. The intermediate value theorem on the convex ball forces s ≡ 1, so ξN(G v) = η(v), which is the claimed identity.

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
