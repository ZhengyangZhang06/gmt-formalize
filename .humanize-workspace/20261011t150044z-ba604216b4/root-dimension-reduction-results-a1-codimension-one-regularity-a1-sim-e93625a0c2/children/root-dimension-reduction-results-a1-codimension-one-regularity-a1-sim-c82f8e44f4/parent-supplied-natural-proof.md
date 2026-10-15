# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.first_variation-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.first_variation-a1.smooth_to_c1-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 8 of the supplied proof of the parent; Simon Ch. 2, end of §5 (book/chapter-02.txt lines 1269–1275: stationarity tested with C¹ fields of compact support in U). The supplied proof mollifies X with a fixed compact margin K' ⊆ U and uses dominated convergence. Here the mollified fields come from the accepted lemma smooth_approx, which mollifies id + X in exactly this way. It provides the three facts the dominated convergence needs: a common compact set K' ⊆ U outside which all approximants vanish, a uniform bound on their derivatives, and pointwise convergence of the derivatives. Dependencies: locally_closed (M is Borel); smooth_approx (Submission.dpf_smooth_approx_compact_perturbation): for U open, K ⊆ U compact and φ C¹ with φ(x) = x off K, there are C^∞ maps ψ_k, a compact K' ⊆ U and C ∈ ℝ with ψ_k(x) = x for x ∉ K', ‖Dψ_k(x)‖ ≤ C, ψ_k(x) → φ(x) and Dψ_k(x) → Dφ(x) for every x; tangent_projection ((a) dim S_x = m on M, (c) continuity of div_M Y on M for C¹ Y); trace_bound.

1. (Set-up.) M is Borel (locally_closed). Let μ := H^m⌞M. Fix X as in the conclusion and let K₀ := tsupport X, compact (compact support) and ⊆ U.
2. (Approximation.) φ := id + X is C¹, and φ(x) = x for x ∉ K₀ because X vanishes off its tsupport. smooth_approx applied to (U, K₀, φ) gives C^∞ maps ψ_k (k ∈ ℕ), a compact K' ⊆ U and C ∈ ℝ as stated above.
3. (Smooth fields.) X_k := ψ_k − id is C^∞ and X_k(x) = 0 for x ∉ K'. Hence X_k has compact support (HasCompactSupport.intro with the compact set K'), and tsupport X_k ⊆ K' because K' is closed; so tsupport X_k ⊆ U. By hypothesis ∫_M div_M X_k dH^m = 0 for every k.
4. (Derivatives.) By the difference and sum rules DX_k(x) = Dψ_k(x) − I and Dφ(x) = I + DX(x). Hence ‖DX_k(x)‖ ≤ C + 1 for all k, x, and DX_k(x) → Dφ(x) − I = DX(x) for every x. Moreover DX_k(x) = 0 for x ∉ K', because support(DX_k) ⊆ tsupport X_k ⊆ K' (support_fderiv_subset).
5. (Dominating function.) Let g := m(C + 1)·1_{K'}. Since K' is compact and K' ⊆ U, μ(K') = H^m(M ∩ K') < ∞, so g is μ-integrable. For x ∈ M: if x ∈ K', then trace_bound and tangent_projection (a) give |div_M X_k(x)| ≤ dim(S_x)·‖DX_k(x)‖ = m‖DX_k(x)‖ ≤ m(C + 1) = g(x); if x ∉ K', then DX_k(x) = 0 and div_M X_k(x) = trace(P_x ∘ 0) = 0 = g(x). Hence |div_M X_k| ≤ g μ-a.e., for every k.
6. (Measurability.) Each X_k is C¹, so div_M X_k is continuous on the Borel set M (tangent_projection (c)), hence a.e.-strongly measurable for μ.
7. (Pointwise convergence.) Fix x. L ↦ trace(P_x ∘ L) is a linear function on the finite-dimensional space L(ℝ^P), hence continuous, and DX_k(x) → DX(x) by step 4. So div_M X_k(x) → div_M X(x).
8. (Dominated convergence.) By steps 5–7 and the dominated convergence theorem (tendsto_integral_of_dominated_convergence), ∫_M div_M X_k dH^m → ∫_M div_M X dH^m. The left side is 0 for every k (step 3), so ∫_M div_M X dH^m = 0 by uniqueness of limits. ∎

Lean reference proof (verified). The declaration below was compiled with Lean v4.35.0-rc3 and Mathlib 25730c7c after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's `open`s, with every dependency declared under its exact `Submission.` name and byte-identical frozen type (file /tmp/fv-split-e936/check/Final.lean, exit 0). It is a single declaration with no helper lemmas, and `#print axioms` lists only propext, Classical.choice, Quot.sound and the dependencies named above.

```lean
theorem Submission.codim1_hcp_fv_smooth_to_C1_stationary : ∀ (P m : ℕ) (U M : Set (Euclid P)), IsOpen U → IsEmbeddedSubmanifold 1 m M → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[m] (M ∩ K) ≠ ∞) → (∀ Z : Euclid P → Euclid P, ContDiff ℝ (⊤ : ℕ∞) Z → HasCompactSupport Z → tsupport Z ⊆ U → ∫ x in M, LinearMap.trace ℝ (Euclid P) ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ (fderiv ℝ Z x).toLinearMap) ∂μHE[m] = 0) → ∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U → ∫ x in M, LinearMap.trace ℝ (Euclid P) ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ (fderiv ℝ X x).toLinearMap) ∂μHE[m] = 0 := by
  intro P m U M hU hM hfin hsmooth X hX hXc hXU
  have hMmeas : MeasurableSet M := (Submission.dimred_rpd_embedded_locally_closed P 1 m M hM).1
  obtain ⟨hfr, -, hdivc⟩ := Submission.codim1_hcp_fv_tangent_projection_continuousOn P m M hM
  have hXd : Differentiable ℝ X := hX.differentiable one_ne_zero
  -- smooth approximations ψ_k of φ = id + X, equal to id off a compact K' ⊆ U
  obtain ⟨ψ, K', C, hK', hK'U, hψs, hψid, hψC, -, hψD⟩ :=
    Submission.dpf_smooth_approx_compact_perturbation P U (tsupport X) (fun x => x + X x) hU hXc
      hXU (contDiff_id.add hX) (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
  set Xk : ℕ → Euclid P → Euclid P := fun k x => ψ k x - x with hXk_def
  have hXks : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (Xk k) := fun k => (hψs k).sub contDiff_id
  have hXk0 : ∀ k x, x ∉ K' → Xk k x = 0 := fun k x hx => by simp [Xk, hψid k x hx]
  have hXkc : ∀ k, HasCompactSupport (Xk k) := fun k => HasCompactSupport.intro hK' (hXk0 k)
  have hXkts : ∀ k, tsupport (Xk k) ⊆ K' := fun k =>
    closure_minimal (fun x hx => by_contra fun h => hx (hXk0 k x h)) hK'.isClosed
  have hstat : ∀ k, ∫ x in M, LinearMap.trace ℝ (Euclid P)
      ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ
        (fderiv ℝ (Xk k) x).toLinearMap) ∂μHE[m] = 0 :=
    fun k => hsmooth (Xk k) (hXks k) (hXkc k) ((hXkts k).trans hK'U)
  -- derivatives: DX_k = Dψ_k − I → DX pointwise, ‖DX_k‖ ≤ C + 1, DX_k = 0 off K'
  have hψd : ∀ k, Differentiable ℝ (ψ k) := fun k => (hψs k).differentiable (by simp)
  have hDXk : ∀ k x, fderiv ℝ (Xk k) x = fderiv ℝ (ψ k) x - ContinuousLinearMap.id ℝ (Euclid P) :=
    fun k x => ((hψd k x).hasFDerivAt.sub (hasFDerivAt_id x)).fderiv
  have hDφ : ∀ x, fderiv ℝ (fun x => x + X x) x =
      ContinuousLinearMap.id ℝ (Euclid P) + fderiv ℝ X x :=
    fun x => ((hasFDerivAt_id x).add (hXd x).hasFDerivAt).fderiv
  have hconv : ∀ x, Tendsto (fun k => fderiv ℝ (Xk k) x) atTop (𝓝 (fderiv ℝ X x)) := by
    intro x
    have h := (hψD x).sub_const (ContinuousLinearMap.id ℝ (Euclid P))
    rw [hDφ x, add_sub_cancel_left] at h
    simpa only [hDXk] using h
  have hDXkb : ∀ k x, ‖fderiv ℝ (Xk k) x‖ ≤ C + 1 := by
    intro k x
    rw [hDXk]
    exact (norm_sub_le _ _).trans (add_le_add (hψC k x) ContinuousLinearMap.norm_id_le)
  have hDXk0 : ∀ k x, x ∉ K' → fderiv ℝ (Xk k) x = 0 := by
    intro k x hx
    by_contra hne
    exact hx (hXkts k (support_fderiv_subset ℝ hne))
  -- dominated convergence for μHE[m] ⌞ M with dominant m (C + 1) 1_{K'}
  set g : Euclid P → ℝ := K'.indicator (fun _ => (m : ℝ) * (C + 1)) with hg_def
  have hg : Integrable g (μHE[m].restrict M) := by
    rw [hg_def, integrable_indicator_iff hK'.isClosed.measurableSet]
    refine integrableOn_const ?_
    rw [Measure.restrict_apply hK'.isClosed.measurableSet, inter_comm]
    exact hfin K' hK' hK'U
  have hbound : ∀ k, ∀ᵐ x ∂(μHE[m].restrict M), ‖LinearMap.trace ℝ (Euclid P)
      ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ
        (fderiv ℝ (Xk k) x).toLinearMap)‖ ≤ g x := by
    intro k
    filter_upwards [ae_restrict_mem hMmeas] with x hx
    by_cases hxK : x ∈ K'
    · rw [hg_def, indicator_of_mem hxK, Real.norm_eq_abs]
      have h := Submission.codim1_hcp_fv_trace_comp_abs_le P
        (Submodule.span ℝ (tangentSpace M x)) (fderiv ℝ (Xk k) x)
      rw [hfr x hx] at h
      exact h.trans (mul_le_mul_of_nonneg_left (hDXkb k x) (Nat.cast_nonneg m))
    · rw [hg_def, indicator_of_notMem hxK, hDXk0 k x hxK]
      simp
  have hlim : ∀ᵐ x ∂(μHE[m].restrict M), Tendsto (fun k => LinearMap.trace ℝ (Euclid P)
      ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ
        (fderiv ℝ (Xk k) x).toLinearMap)) atTop
      (𝓝 (LinearMap.trace ℝ (Euclid P)
        ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ
          (fderiv ℝ X x).toLinearMap))) := by
    refine Eventually.of_forall fun x => ?_
    have htr : Continuous (fun T : Euclid P →L[ℝ] Euclid P =>
        LinearMap.trace ℝ (Euclid P) (T : Euclid P →ₗ[ℝ] Euclid P)) :=
      LinearMap.continuous_of_finiteDimensional
        ((LinearMap.trace ℝ (Euclid P)).comp (ContinuousLinearMap.coeLM ℝ))
    have hF : Continuous (fun L : Euclid P →L[ℝ] Euclid P => LinearMap.trace ℝ (Euclid P)
        ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ L.toLinearMap)) := by
      have := htr.comp (Continuous.clm_comp
        (g := fun _ : Euclid P →L[ℝ] Euclid P =>
          (Submodule.span ℝ (tangentSpace M x)).starProjection)
        (f := id) continuous_const continuous_id)
      refine this.congr fun L => ?_
      simp only [Function.comp_apply, id]
      rfl
    exact (hF.tendsto _).comp (hconv x)
  have hmeas : ∀ k, AEStronglyMeasurable (fun x => LinearMap.trace ℝ (Euclid P)
      ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ
        (fderiv ℝ (Xk k) x).toLinearMap)) (μHE[m].restrict M) :=
    fun k => (hdivc (Xk k) ((hXks k).of_le (by exact_mod_cast le_top))).aestronglyMeasurable hMmeas
  have hT := tendsto_integral_of_dominated_convergence g hmeas hg hbound hlim
  simp only [hstat] at hT
  exact tendsto_nhds_unique hT tendsto_const_nhds
```

## Key steps

1. smooth_approx applied to φ = id + X gives C^∞ ψ_k equal to id off a fixed compact K' ⊆ U, with ‖Dψ_k‖ ≤ C and Dψ_k → Dφ pointwise.
2. X_k = ψ_k − id are admissible smooth fields (compact support in K' ⊆ U), so ∫_M div_M X_k = 0.
3. |div_M X_k| ≤ m(C + 1)·1_{K'} (trace_bound), integrable because H^m(M ∩ K') < ∞; div_M X_k → div_M X pointwise.
4. Dominated convergence gives ∫_M div_M X = lim ∫_M div_M X_k = 0.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; sha256sum GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `sed -n 1,457p GMT/Ch07/Submission.lean (IsEmbeddedSubmanifold, tangentSpace, tangentialDivergence, IMRep.IsStationaryAlong)`
- `read nodes/<selected>/parent-child-handoff.json and parent-supplied-plan.md; nodes/root-…-sim-b5d5990773/decomposition-v1.json (hypercone_plane split)`
- `python3 scans of dag.json: nodes whose lean_statement mentions starProjection|tangentSpace|IsEmbeddedSubmanifold|adjoint+det|subtypeL|LinearMap.trace|convolution|TendstoUniformly|ContDiff ℝ (⊤, with status and candidate_commit`
- `read parent-child-handoff.json of dsmc_chart_tangentSpace_eq_range, dimred_rpd_embedded_locally_closed, fvmb_orthonormal_gram_sqrt_det_le_first_order, fvmb_gram_det_le_exp_sum_norm_sq_sub, fvmb_trace_starProjection_comp_eq_sum_inner, dpf_smooth_approx_compact_perturbation`
- `git show <commit>:GMT/Ch07/Submission.lean | grep '^theorem Submission.' for 44afba4d4bb9 6da66b1edf6f 84fc998516ed 56e107017393 6b000c36933a 39688605e0a8 (exact frozen type present)`
- `grep -rn in local-references/123e8435b4a2469b/mathlib/Mathlib: setLIntegral_mono', ofReal_integral_eq_lintegral_ofReal, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, ContinuousOn.aestronglyMeasurable, IntegrableOn.of_bound, support_fderiv_subset, inverse_continuousAt, eq_starProjection_of_mem_of_inner_eq_zero, ContDiffOn.continuousOn_fderiv_of_isOpen, det_toMatrix, repr_apply_apply, adjoint_inner_right, LinearMap.continuous_of_finiteDimensional, tendsto_integral_of_dominated_convergence, norm_image_sub_le_of_norm_fderiv_le, HasCompactSupport.fderiv, bounded_above_of_compact_support, image_eq_zero_of_notMem_tsupport, Orthonormal.comp_linearIsometry, LinearMap.finrank_range_of_inj, coe_range, mul_apply_eq_comp`
- `grep -c codim1_hcp_fv_ dag.json GMT/Ch07/Submission.lean; grep -rl codim1_hcp_fv_ .lake/packages/simongmt; git grep codim1_hcp_fv_ over all 2626 refs (no match)`
- `runtime.py (_decompose max_depth, _existing_lean_name_problem, _solve_children, _install_parent_supplied_child_handoff, _overlay_accepted_children, _leaf_author_task) and store.py ensure`
- `lean -DautoImplicit=false /tmp/fv-split-e936/check/{TypesAll,Assembly,N1,N2N3,N4,N5,N6,Chain,Final}.lean and /tmp/fv-split-e936/reuse/R_*.lean (#print axioms)`
- `book/chapter-02.txt lines 1030–1041 (4.18–4.20) and 1160–1285 (§5: 5.1–5.4, stationarity)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-e93625a0c2/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-b5d5990773/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ch-f0862c44ef/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1-locally-closed-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-first-variation-mass-bound-a1-g-86ce9f2a61/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-first-variation-mass-bound-a1-g-3e803c0b62/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-first-variation-mass-bound-a1-t-e90143df5c/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-smooth-ap-e30aa8106d/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/runtime/flows/gmt-claude-252c8df06c56/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-252c8df06c56/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/fv-split-e936/check/TypesAll.lean`
- `/tmp/fv-split-e936/check/Assembly.lean`
- `/tmp/fv-split-e936/check/Final.lean`
- `/tmp/fv-split-e936/reuse/R_dsmc_chart_tangentSpace_eq_range.lean`

Pins match. The manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib. Snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…). Reusable accepted DAG lemmas found:
- dsmc_chart_tangentSpace_eq_range: T_{ψ v} = range Dψ(v), plus continuity of ψ⁻¹.
- dimred_rpd_embedded_locally_closed: M is Borel.
- fvmb_orthonormal_gram_sqrt_det_le_first_order: √det Gram(Lτ) ≤ 1 + tΣ⟨τ_a,Bτ_a⟩ + ε|t|.
- fvmb_trace_starProjection_comp_eq_sum_inner: trace(P_Q∘B) = Σ⟨τ_a,Bτ_a⟩.
- dpf_smooth_approx_compact_perturbation: C^∞ approximation of id + X with a fixed compact K' ⊆ U and pointwise derivative convergence.
Their types are byte-identical to the DAG, and each compiles at its candidate commit with standard axioms only. The C² tangent-projection proof (dor_lmb_ret_tangent_projection, commit 39688605e0a8) supplied the D(D*D)⁻¹D* technique, adapted to continuity for C¹ charts. No accepted lemma gives continuity of P_x for C¹ M, a trace bound, a subspace-det Jacobian bound, injectivity of id + tZ, or the first-variation and C¹-extension steps. These are the six new codim1_hcp_fv_ nodes; the names have no match anywhere. All cited Mathlib names exist in the snapshot (the current spelling is setIntegral_eq_of_subset_of_forall_sdiff_eq_zero). Lean: all child types elaborate. All six new children and the selected frozen type are kernel-checked from exactly the declared prerequisites, with the area formula as the parent's own prerequisite (Final.lean, exit 0).
