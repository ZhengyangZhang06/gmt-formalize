# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1`
- Child DAG node: `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1.chart_representation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps (6a)–(6d) of the parent proof for one chart, with G := G_K, treating the two integrands at once. About the pair (A, f), (6c)–(6d) only use two facts: (A(x)_#ξ(x))(α(f(x))) is evaluated through ξ(x) = s·JΦ⁻¹·simpleNVector(∂Φ(w)), and A(Φ(w))∂_bΦ(w) = ∂_b(f∘Φ)(w). In the parent this is applied with (f, A) = (g_j, Dg_j) (C¹ chain rule) and with (f, A) = (g, L) (sibling chart_chain_rule). The weight ψ = 1_D·(θ∘Φ)·σ does not depend on (f, A, α).

Conventions. H := μHE[k] on ℝ^P; L := volume on ℝ^k; J := JΦ = √det(⟨DΦ(w)e_a, DΦ(w)e_b⟩)_{a,b}; D := Ω ∩ Φ⁻¹(G); ∂Φ(w) := (DΦ(w)e_b)_b; ofReal := ENNReal.ofReal.

1. (Sets.) D ⊆ Ω, and D ⊆ Ω ∩ Φ⁻¹(M) because G ⊆ M.
2. (Jacobian bound, (6a).) Let w ∈ Ω. Φ is differentiable at w (C¹). The sibling fderiv_lower_bound gives c|s| ≤ |DΦ(w)s| for all s. The sibling gram_det_lower_bound with T := DΦ(w) then gives c^k ≤ J(w). In particular J(w) ≥ c^k > 0 on Ω.
3. (Orientation, (6c).) The sibling chart_orientation applies (U open, the triple, Ω open, Φ C¹ and antilipschitz on Ω). It gives σ : ℝ^k → ℝ, a.e.-strongly measurable for L⌞(Ω ∩ Φ⁻¹(M)), with σ(w) = ±1 and J(w)·ξ(Φ(w)) = σ(w)·simpleNVector(∂Φ(w)) for L⌞(Ω ∩ Φ⁻¹(M))-a.e. w. By step 1 both facts hold for L⌞D (restriction to a subset: ae_restrict_of_ae_restrict_of_subset, and AEStronglyMeasurable.mono_measure with Measure.restrict_mono).
4. (θ on the chart, (6b).) θ is H-integrable on G, so ofReal∘θ is a.e.-measurable for H⌞G. The sibling chart_change_of_variables applies (Ω open, Φ Lipschitz and c-antilipschitz on Ω, G ⊆ Φ(Ω), G null-measurable). It gives:
 - D is L-null-measurable;
 - w ↦ ofReal(θ(Φ(w))) is a.e.-measurable for L⌞D;
 - ∫⁻_G ofReal(θ) dH = ∫⁻_D ofReal(θ(Φ(w)))·ofReal(J(w)) dw.
 For w ∈ D, Φ(w) ∈ G ⊆ M, so θ(Φ(w)) > 0 and θ(Φ(w)) = toReal(ofReal(θ(Φ(w)))). As L⌞D-a.e. w lies in D (ae_restrict_mem₀), θ∘Φ is a.e.-measurable for L⌞D.
5. (The weight.) Put F₁(w) := θ(Φ(w))·σ(w) and ψ := 1_D·F₁ (ψ = F₁ on D and 0 elsewhere). F₁ is a.e.-strongly measurable for L⌞D by steps 3–4. D is null-measurable for L⌞Ω, and (L⌞Ω)⌞D = L⌞(D ∩ Ω) = L⌞D (Measure.restrict_restrict₀ and D ⊆ Ω). So ψ is a.e.-strongly measurable for L⌞Ω (aestronglyMeasurable_indicator_iff₀).
6. (ψ ∈ L¹(Ω), (6d).) ∫⁻_Ω |ψ| dL = ∫⁻_D |F₁| dL (lintegral_indicator₀ and step 5). For L⌞D-a.e. w we have |σ(w)| = 1 and θ(Φ(w)) > 0, so by step 2
 ofReal|F₁(w)| = ofReal(θ(Φ(w))) = (ofReal c^k)⁻¹·ofReal(θ(Φ(w)))·ofReal(c^k) ≤ (ofReal c^k)⁻¹·ofReal(θ(Φ(w)))·ofReal(J(w)),
 using ofReal c^k ∈ (0, ∞). Integrating (lintegral_mono_ae, lintegral_const_mul'):
 ∫⁻_D |F₁| ≤ (ofReal c^k)⁻¹ ∫⁻_D ofReal(θ∘Φ)·ofReal(J) = (ofReal c^k)⁻¹ ∫⁻_G ofReal(θ) dH ≤ (ofReal c^k)⁻¹ ∫⁻_G |θ| dH < ∞,
 where the equality is step 4. With step 5, ψ is L-integrable on Ω. This is the first conclusion.
7. (The representation.) Let f, A, α satisfy (i) and (ii). Put h(x) := θ(x)·(A(x)_#ξ(x))(α(f(x))) and X(w) := α(f(Φ(w)))(∂_0(f∘Φ)(w), …, ∂_{k−1}(f∘Φ)(w)).
 (7.1) By (ii) and the sibling signed_change_of_variables (same Φ and Ω, with A := G and h := h): ∫_G h dH = ∫_D h(Φ(w))·J(w) dw.
 (7.2) ψ·X = 1_D·(F₁·X). Hence ∫_Ω ψ·X dL = ∫_D F₁·X dL (integral_indicator₀ for L⌞Ω, and (L⌞Ω)⌞D = L⌞D).
 (7.3) For L⌞D-a.e. w, step 3 and (i) hold at w. For such w put x := Φ(w), v := ∂Φ(w) and γ := covectorPullback k (A(x)) (α(f(x))).
  - By definition of the push-forward, (A(x)_#ξ(x))(α(f(x))) = ξ(x)(γ).
  - Evaluating J(w)·ξ(x) = σ(w)·simpleNVector v at γ gives J(w)·ξ(x)(γ) = σ(w)·γ(v), and γ(v) = α(f(x))(A(x)v_0, …, A(x)v_{k−1}) (covectorPullback_apply).
  - By (i), fderiv ℝ (f∘Φ) w = A(x)∘DΦ(w) (HasFDerivAt.fderiv), so ∂_b(f∘Φ)(w) = A(x)(DΦ(w)e_b) = A(x)v_b.
  Hence h(x)·J(w) = θ(x)·ξ(x)(γ)·J(w) = θ(x)·σ(w)·α(f(x))(∂(f∘Φ)(w)) = F₁(w)·X(w).
 (7.4) By (7.3) and setIntegral_congr_ae₀ (D null-measurable), ∫_D h(Φ(w))·J(w) dw = ∫_D F₁·X dL. Combining with (7.1) and (7.2) gives ∫_G h dH = ∫_Ω ψ·X dL, the second conclusion. ∎

Lean remark. The script below was verified with Lean v4.35.0-rc3, Mathlib 25730c7c and SimonGMT 2b36630 as `theorem Submission.deformation_ipl_cc_chart_integral_representation : (<frozen type>) := by` inside `namespace GMT.Ch06` of GMT/Ch06/Submission.lean. It uses the sibling declarations `Submission.deformation_ipl_cc_gram_det_lower_bound`, `Submission.lpf_wtc_cat_fderiv_lower_bound`, `Submission.lpf_raf_chart_change_of_variables`, `Submission.deformation_ipl_cc_signed_change_of_variables`, `Submission.deformation_ipl_cc_chart_orientation_sign`, which were present as declarations of exactly their frozen types. With those sibling statements taken as hypotheses, #print axioms gives only propext, Classical.choice and Quot.sound. Its dependencies are `Submission.deformation_ipl_cc_gram_det_lower_bound`, `Submission.lpf_wtc_cat_fderiv_lower_bound`, `Submission.lpf_raf_chart_change_of_variables`, `Submission.deformation_ipl_cc_signed_change_of_variables` and `Submission.deformation_ipl_cc_chart_orientation_sign`; no extra import is needed.
Tactic script:
  intro P Q k U M θ ξ Φ Ω G hU hT hΩ hΦC1 hΦLip hΦanti hGM hGΦ hGm hθG
  obtain ⟨c, hc, hcanti⟩ := hΦanti
  set J : Eucl k → ℝ := fun w => Real.sqrt (Matrix.of fun i j => inner ℝ
    (fderiv ℝ Φ w (EuclideanSpace.single i 1)) (fderiv ℝ Φ w (EuclideanSpace.single j 1))).det
    with hJdef
  set D : Set (Eucl k) := Ω ∩ Φ ⁻¹' G with hDdef
  have hDΩ : D ⊆ Ω := inter_subset_left
  have hDM : D ⊆ Ω ∩ Φ ⁻¹' M := fun w hw => ⟨hw.1, hGM hw.2⟩
  -- (6a) Jacobian lower bound
  have hJlow : ∀ w ∈ Ω, c ^ k ≤ J w := fun w hw =>
    Submission.deformation_ipl_cc_gram_det_lower_bound P k (fderiv ℝ Φ w) c hc.le
      (Submission.lpf_wtc_cat_fderiv_lower_bound P k Φ Ω c w hΩ hw ((hΦC1.differentiable one_ne_zero) w) hcanti)
  -- (6c) orientation sign
  obtain ⟨σ, hσm, hσ⟩ := Submission.deformation_ipl_cc_chart_orientation_sign P k U M θ ξ Φ Ω hU hT hΩ hΦC1 ⟨c, hc, hcanti⟩
  have hσD : ∀ᵐ w ∂((volume : Measure (Eucl k)).restrict D), (σ w = 1 ∨ σ w = -1) ∧
      J w • ξ (Φ w) = σ w • simpleNVector (fun b => fderiv ℝ Φ w (EuclideanSpace.single b 1)) :=
    ae_restrict_of_ae_restrict_of_subset hDM hσ
  -- (6b) change of variables for θ
  have hθae : AEMeasurable (fun x => ENNReal.ofReal (θ x))
      ((μHE[k] : Measure (Eucl P)).restrict G) := hθG.aemeasurable.ennreal_ofReal
  obtain ⟨hDm, hθΦm, hθCoV⟩ := Submission.lpf_raf_chart_change_of_variables P k Φ Ω G (fun x => ENNReal.ofReal (θ x)) hΩ hΦLip
    ⟨c, hc, hcanti⟩ hGΦ hGm hθae
  have hmemD : ∀ᵐ w ∂((volume : Measure (Eucl k)).restrict D), w ∈ D := ae_restrict_mem₀ hDm
  have hθΦpos : ∀ w ∈ D, 0 < θ (Φ w) := fun w hw => hT.pos _ (hGM hw.2)
  have hθΦae : AEMeasurable (fun w => θ (Φ w)) ((volume : Measure (Eucl k)).restrict D) := by
    refine hθΦm.ennreal_toReal.congr ?_
    filter_upwards [hmemD] with w hw
    exact ENNReal.toReal_ofReal (hθΦpos w hw).le
  have hσDm : AEStronglyMeasurable σ ((volume : Measure (Eucl k)).restrict D) :=
    hσm.mono_measure (Measure.restrict_mono hDM le_rfl)
  have hDmΩ : NullMeasurableSet D ((volume : Measure (Eucl k)).restrict Ω) :=
    hDm.mono_ac Measure.restrict_le_self.absolutelyContinuous
  have hrestrDΩ : ((volume : Measure (Eucl k)).restrict Ω).restrict D =
      (volume : Measure (Eucl k)).restrict D := by
    rw [Measure.restrict_restrict₀ hDmΩ, inter_eq_left.mpr hDΩ]
  -- the weight
  set F₁ : Eucl k → ℝ := fun w => θ (Φ w) * σ w with hF₁
  set ψ : Eucl k → ℝ := D.indicator F₁ with hψdef
  have hF₁m : AEStronglyMeasurable F₁ ((volume : Measure (Eucl k)).restrict D) :=
    hθΦae.aestronglyMeasurable.mul hσDm
  have hψm : AEStronglyMeasurable ψ ((volume : Measure (Eucl k)).restrict Ω) := by
    rw [hψdef, aestronglyMeasurable_indicator_iff₀ hDmΩ, hrestrDΩ]
    exact hF₁m
  have hck : 0 < c ^ k := pow_pos hc k
  have hck0 : ENNReal.ofReal (c ^ k) ≠ 0 := by simpa using hck
  refine ⟨ψ, ?_, ?_⟩
  · -- (6d) integrability of ψ
    refine ⟨hψm, ?_⟩
    rw [HasFiniteIntegral]
    have h1 : ∫⁻ w in Ω, ‖ψ w‖ₑ = ∫⁻ w in D, ‖F₁ w‖ₑ := by
      have : (fun w => ‖ψ w‖ₑ) = D.indicator (fun w => ‖F₁ w‖ₑ) := by
        funext w
        by_cases hw : w ∈ D
        · simp [hψdef, hw]
        · simp [hψdef, hw]
      rw [this, lintegral_indicator₀ hDmΩ, hrestrDΩ]
    rw [h1]
    have h2 : ∫⁻ w in D, ‖F₁ w‖ₑ ≤ ∫⁻ w in D,
        (ENNReal.ofReal (c ^ k))⁻¹ * (ENNReal.ofReal (θ (Φ w)) * ENNReal.ofReal (J w)) := by
      refine lintegral_mono_ae ?_
      filter_upwards [hσD, hmemD] with w hw hwD
      have hθp := hθΦpos w hwD
      have hσ1 : |σ w| = 1 := by rcases hw.1 with h | h <;> simp [h]
      have hle : c ^ k ≤ J w := hJlow w hwD.1
      calc ‖F₁ w‖ₑ = ENNReal.ofReal (θ (Φ w)) := by
            rw [hF₁, Real.enorm_eq_ofReal_abs, abs_mul, hσ1, abs_of_pos hθp, mul_one]
        _ = (ENNReal.ofReal (c ^ k))⁻¹ * (ENNReal.ofReal (θ (Φ w)) * ENNReal.ofReal (c ^ k)) := by
            rw [mul_comm (ENNReal.ofReal (θ (Φ w))), ← mul_assoc,
              ENNReal.inv_mul_cancel hck0 ENNReal.ofReal_ne_top, one_mul]
        _ ≤ (ENNReal.ofReal (c ^ k))⁻¹ * (ENNReal.ofReal (θ (Φ w)) * ENNReal.ofReal (J w)) := by
            gcongr
    refine lt_of_le_of_lt h2 ?_
    rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hck0), ← hθCoV]
    refine ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (by simpa using hck)) ?_
    refine lt_of_le_of_lt ?_ hθG.2
    refine lintegral_mono fun x => ?_
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  · intro f A α hfd hint
    obtain ⟨-, hcov⟩ := Submission.deformation_ipl_cc_signed_change_of_variables P k Φ Ω G (fun x => θ x * nVectorPushforward k (A x) (ξ x) (α (f x)))
      hΩ hΦLip ⟨c, hc, hcanti⟩ hGΦ hGm hint
    rw [hcov]
    have hR : ∫ w in Ω, ψ w * α (f (Φ w))
          (fun b => fderiv ℝ (f ∘ Φ) w (EuclideanSpace.single b 1)) =
        ∫ w in D, F₁ w * α (f (Φ w))
          (fun b => fderiv ℝ (f ∘ Φ) w (EuclideanSpace.single b 1)) := by
      have : (fun w => ψ w * α (f (Φ w))
            (fun b => fderiv ℝ (f ∘ Φ) w (EuclideanSpace.single b 1))) =
          D.indicator (fun w => F₁ w * α (f (Φ w))
            (fun b => fderiv ℝ (f ∘ Φ) w (EuclideanSpace.single b 1))) := by
        funext w
        by_cases hw : w ∈ D
        · simp [hψdef, hw]
        · simp [hψdef, hw]
      rw [this, integral_indicator₀ hDmΩ, hrestrDΩ]
    rw [hR]
    refine setIntegral_congr_ae₀ hDm ?_
    have hgood := (ae_restrict_iff'₀ hDm).mp (hσD.and hfd)
    filter_upwards [hgood] with w hw hwD
    obtain ⟨⟨-, hJξ⟩, hder⟩ := hw hwD
    set v : Fin k → Eucl P := fun b => fderiv ℝ Φ w (EuclideanSpace.single b 1) with hv
    set β : Covector (Eucl P) k := covectorPullback k (A (Φ w)) (α (f (Φ w))) with hβ
    have key : ξ (Φ w) β * J w = σ w * β v := by
      have := congrArg (fun T : NVector (Eucl P) k => T β) hJξ
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, simpleNVector_apply] at this
      linarith [this]
    have hfv : (fun b => fderiv ℝ (f ∘ Φ) w (EuclideanSpace.single b 1)) =
        (A (Φ w)) ∘ v := by
      funext b
      rw [hder.fderiv]
      rfl
    have hβv : β v = α (f (Φ w)) ((A (Φ w)) ∘ v) := by
      rw [hβ, covectorPullback_apply]
    show θ (Φ w) * nVectorPushforward k (A (Φ w)) (ξ (Φ w)) (α (f (Φ w))) * J w =
      F₁ w * α (f (Φ w)) (fun b => fderiv ℝ (f ∘ Φ) w (EuclideanSpace.single b 1))
    have hpush : nVectorPushforward k (A (Φ w)) (ξ (Φ w)) (α (f (Φ w))) = ξ (Φ w) β := rfl
    rw [hpush, mul_assoc, key, hβv, hfv, hF₁]
    ring

## Key steps

1. fderiv_lower_bound and gram_det_lower_bound: JΦ ≥ c^k > 0 on Ω.
2. chart_orientation: a measurable σ = ±1 with JΦ·ξ(Φ) = σ·simpleNVector(∂Φ) a.e. on D = Ω ∩ Φ⁻¹(G).
3. chart_change_of_variables for ofReal∘θ: D is null-measurable, θ∘Φ is measurable on D and ∫⁻_D θ(Φ)·JΦ = ∫⁻_G θ; so ψ := 1_D·θ(Φ)·σ satisfies ∫_Ω|ψ| ≤ c^{−k}∫_G θ < ∞.
4. signed_change_of_variables gives ∫_G h = ∫_D h(Φ)·JΦ, and pointwise h(Φ(w))·JΦ(w) = ψ(w)·α(f(Φ(w)))(∂(f∘Φ)(w)) from the orientation identity, the push-forward definition and fderiv(f∘Φ) = A(Φ(w))∘DΦ(w).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp of workspace GMT/Ch06/Submission.lean, GMT/Ch06/Contract.lean and the snapshot project/GMT/Ch06/Contract.lean (byte-identical)`
- `python3 -I over dag.json: status, candidate_commit and lean_statement of the node's dependencies lpf_simple_nvector_algebra, lpf_countably_rectifiable_c1_cover, lpf_chart_chain_rule, lpf_raf_chart_change_of_variables (accepted), deformation_ipl_minor_weak_continuity and deformation_ipl_tangential_pushforward_aestronglyMeasurable (decomposing)`
- `python3 -I over dag.json: regex search jacob|change_of_var|antilip|gram|det|tannery|dominat|chart|area|orient|simple|pushforward over lean names, then lean_statement of lpf_wtc_cat_fderiv_lower_bound, lpf_wtc_cat_gram_jacobian_continuous, lpf_wtc_caf_signed_of_lintegral, lpf_pi_jacobian_local_bound, lpf_pi_measurability, lpf_pic_density_dominated, lpf_raf_chart_preimage_null, lpf_ccr_ae_pullback, lpf_weighted_tangent_on_c1_chart, lpf_wtc_chart_image_measurable_locally_finite, iwl_sp_sn_signed_simpleNVector_bound_ne_zero, fiw_ims_frame_sign, slicing_im_ll_twl_chart_integral_eq (decomposing, not reusable)`
- `python3 -I over nodes/*/parent-child-handoff.json: map the six reused node ids to their directories and check title/statement/lean_statement/lean_name byte-identity with dag.json (all True)`
- `python3 -I over dag.json: lean-name collision check for deformation_ipl_cc_gram_det_lower_bound, deformation_ipl_cc_signed_change_of_variables, deformation_ipl_cc_chart_orientation_sign, deformation_ipl_cc_chart_integral_representation, deformation_ipl_cc_pushforward_integrand_bound, deformation_ipl_cc_tendsto_setIntegral_of_partition (none); rg -l deformation_ipl_cc over GMT, snapshot project, snapshot Mathlib and SimonGMT (no match); git grep over all local branches (no match)`
- `rg -n 'abbrev (Covector|NVector)|def (simpleNVector|nVectorPushforward|covectorPullback|wedgeCovectors)|theorem wedgeCovectors_apply_det|theorem nVectorPushforward_simple' simongmt/Poincare/SimonGMT/Chapter06; rg -n 'HasWeightedApproximateTangentSpaceAt' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `rg -n over snapshot Mathlib: IsOpen.isSigmaCompact (no match), NullMeasurableSet.disjointed, disjointed_subset|iUnion_disjointed|disjoint_disjointed, integral_iUnion_ae, hasSum_integral_iUnion_ae, tendsto_tsum_of_dominated_convergence, setIntegral_congr_set, setIntegral_indicator, aestronglyMeasurable_indicator_iff₀, aestronglyMeasurable_iUnion_iff, Matrix.IsHermitian det_eq_prod_eigenvalues|eigenvalues_eq|mulVec_eigenvectorBasis, prod_le_prod₀, adjoint_inner_right, continuous_compContinuousLinearMapCLM, integral_eq_lintegral_pos_part_sub_lintegral_neg_part, Orthonormal.inner_right_fintype, mem_span_range_iff_exists_fun, HasDerivAt.le_of_lipschitz, norm_fderiv_le_of_lipschitz, IsCompact.cthickening, mem_cthickening_of_dist_le, image_eq_zero_of_notMem_tsupport, HasCompactSupport.exists_bound_of_continuous, opNorm_smul_le, NormedSpace.toNormSMulClass`
- `git show 9fc44225b304fca8af9dead3256575ef03818d1e:GMT/Ch06/Submission.lean (accepted declaration format) and the import lines of all accepted candidate Submissions (extra imports already accepted)`
- `python3 -I verifier/lean_contract.py validate_lean_statement and verifier/gmt-compare.py child_modules (mode contract) for the twelve types`
- `lake env lean /tmp/ccv-decomp/ExactScope.lean (twelve types, exit 0); /tmp/ccv-decomp/Assembly.lean (parent from child and dependency types); /tmp/ccv-decomp/Dproof.lean, Cproof.lean, Bproof.lean, Aproof.lean (+Mathlib.Analysis.Matrix.Spectrum), Eproof.lean, Fproof.lean (+Mathlib.Analysis.Normed.Group.Tannery); /tmp/ccv-decomp/Final_*.lean (final Submission.* forms against stubs); /tmp/ccv-decomp/Inst.lean (NormSMulClass ℝ (NVector …) not synthesized)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-chart-convergence-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-chart-convergence-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1/decomposition-audit-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-simple-nvector-algebra-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1-ae-pullback-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-chart-ch-1ba1e0b708/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-837491fcd9/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-1f4173ea67/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Matrix/Spectrum.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/Tannery.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Disjointed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/ccv-decomp/ExactScope.lean`
- `/tmp/ccv-decomp/Assembly.lean`
- `/tmp/ccv-decomp/Dproof.lean`
- `/tmp/ccv-decomp/Cproof.lean`
- `/tmp/ccv-decomp/Final_parent.lean`

Pinned revisions are confirmed, and the frozen contract is byte-identical to the snapshot (Submission = Contract).
Reuse:
- Six accepted declarations are reused by name: lpf_simple_nvector_algebra, lpf_weighted_tangent_on_c1_chart, lpf_ccr_ae_pullback, lpf_raf_chart_change_of_variables, lpf_wtc_cat_fderiv_lower_bound and lpf_wtc_chart_image_measurable_locally_finite.
- Each has status accepted with a candidate commit, and its title, statement and Lean type are copied byte-for-byte from dag.json (identical to its handoff).
- The node's other dependencies (c1_cover, chart_chain_rule, minor_weak_continuity, pushforward_measurable) are used only by the parent assembly.
- No accepted DAG node or library lemma states the signed chart change of variables, the measurable chart orientation sign, the chart integral representation or the partition Tannery lemma. slicing_im_ll_twl_chart_integral_eq is still decomposing, so it cannot be reused.
New names: the six deformation_ipl_cc_ names collide with nothing in dag.json, the project, SimonGMT or the pinned Mathlib.
Library support (all present in the snapshot):
- Matrix.IsHermitian spectral theorem (det_eq_prod_eigenvalues, eigenvalues_eq) and tendsto_tsum_of_dominated_convergence; both modules need an extra import.
- NullMeasurableSet.disjointed, integral_iUnion_ae, hasSum_integral_iUnion_ae, integral_eq_lintegral_pos_part_sub_lintegral_neg_part, ContinuousLinearMap.adjoint_inner_right and ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.
- SimonGMT: wedgeCovectors_apply_det, nVectorPushforward_simple and HasWeightedApproximateTangentSpaceAt.unique.
- IsOpen.isSigmaCompact does not exist; the open-set exhaustion is written out explicitly.
- NormSMulClass ℝ (NVector …) is not synthesized; opNorm_smul_le is used instead.
Lean checks:
- All twelve types validate and elaborate in the exact comparator scope.
- The parent assembly compiles from the frozen child and dependency types.
- Every new child compiles from exactly its declared sibling types.
- All of these give only propext, Classical.choice and Quot.sound.
