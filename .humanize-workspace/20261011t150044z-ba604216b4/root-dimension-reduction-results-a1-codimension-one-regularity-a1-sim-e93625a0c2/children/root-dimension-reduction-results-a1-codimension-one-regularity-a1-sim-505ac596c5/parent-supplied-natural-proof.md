# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.first_variation-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.first_variation-a1.jacobian_first_order-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3–4 of the supplied proof of the parent (Simon Ch. 2, §5, book/chapter-02.txt lines 1198–1250: in an orthonormal basis τ_1, …, τ_n of T_xM the matrix of dφ_t*dφ_t is b_ij(t) = (τ_i + tD_{τ_i}X)·(τ_j + tD_{τ_j}X) and J_t = √det b(t) = 1 + t div_M X + O(t²)). Only the first-order, one-sided form with constants independent of K is needed. Dependencies: gram_first_order (Submission.fvmb_orthonormal_gram_sqrt_det_le_first_order): for P, n, A ≥ 0, ε > 0 there are η > 0, δ > 0 such that |t| < δ, ‖B‖ ≤ A, ‖L − I − tB‖ ≤ η|t| and τ : Fin n → ℝ^P orthonormal imply √det(⟨Lτ_i, Lτ_j⟩)_{i,j} ≤ 1 + tΣ_a⟨τ_a, Bτ_a⟩ + ε|t|; trace_frame (Submission.fvmb_trace_starProjection_comp_eq_sum_inner): if τ : Fin n → ℝ^P is orthonormal and span(range τ) = Q, then trace(Q.starProjection ∘ B) = Σ_a ⟨τ_a, Bτ_a⟩.

1. (Choice of δ.) Apply gram_first_order to (P, n, A, ε) and obtain η > 0 and δ > 0; they depend only on P, n, A, ε. We show that this δ works.
2. (Set-up.) Fix t with |t| < δ, a subspace K with dim K = n and B with ‖B‖ ≤ A, and put L := I + tB. Then L − I − tB = 0, so ‖L − I − tB‖ = 0 ≤ η|t|.
3. (Frame.) Since dim K = n, the standard orthonormal basis e of K (stdOrthonormalBasis ℝ K) is indexed by Fin n (after substituting n = dim K). Put τ_a := e_a regarded as a vector of ℝ^P. The inclusion K → ℝ^P is a linear isometry (K.subtypeₗᵢ), so τ is orthonormal in ℝ^P (Orthonormal.comp_linearIsometry). Moreover span(range τ) = K: range τ is the image of range e under the inclusion, span commutes with linear images (Submodule.span_image), span(range e) = ⊤ in K because e is a basis, and the image of ⊤ under the inclusion is K (Submodule.map_top, Submodule.range_subtype).
4. (Gram identity.) Let Λ := L ∘ ι_K : K → ℝ^P and G := Λ*Λ : K → K. The determinant of an endomorphism equals the determinant of its matrix in any basis (LinearMap.det_toMatrix applied to the basis e). In the orthonormal basis e the (i, j) entry of that matrix is e.repr(G e_j)_i = ⟨e_i, Λ*Λe_j⟩_K = ⟨Λe_i, Λe_j⟩ = ⟨Lτ_i, Lτ_j⟩ (OrthonormalBasis.repr_apply_apply, ContinuousLinearMap.adjoint_inner_right; the inner product of K is the restriction of that of ℝ^P). Hence det G = det(⟨Lτ_i, Lτ_j⟩)_{i,j=1}^n, i.e. det G is the Gram determinant b(t) of the parent's step 3.
5. (First-order bound.) By steps 2–3 the hypotheses of gram_first_order hold for t, B, L and τ, so √det G = √det(⟨Lτ_i, Lτ_j⟩) ≤ 1 + tΣ_a⟨τ_a, Bτ_a⟩ + ε|t|.
6. (Divergence.) By trace_frame with Q = K, Σ_a⟨τ_a, Bτ_a⟩ = trace(P_K ∘ B). Substituting into step 5 gives √det(((I + tB)∘ι_K)*((I + tB)∘ι_K)) ≤ 1 + t·trace(P_K ∘ B) + ε|t|. ∎

Lean reference proof (verified). The declaration below was compiled with Lean v4.35.0-rc3 and Mathlib 25730c7c after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's `open`s, with every dependency declared under its exact `Submission.` name and byte-identical frozen type (file /tmp/fv-split-e936/check/Final.lean, exit 0). It is a single declaration with no helper lemmas, and `#print axioms` lists only propext, Classical.choice, Quot.sound and the dependencies named above.

```lean
theorem Submission.codim1_hcp_fv_subspace_jacobian_first_order : ∀ (P n : ℕ) (A ε : ℝ), 0 ≤ A → 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ (K : Submodule ℝ (Euclid P)) (B : Euclid P →L[ℝ] Euclid P), Module.finrank ℝ K = n → ‖B‖ ≤ A → Real.sqrt ((((ContinuousLinearMap.id ℝ (Euclid P) + t • B).comp K.subtypeL).adjoint ∘L ((ContinuousLinearMap.id ℝ (Euclid P) + t • B).comp K.subtypeL)).det) ≤ 1 + t * LinearMap.trace ℝ (Euclid P) (K.starProjection.toLinearMap ∘ₗ B.toLinearMap) + ε * |t| := by
  intro P n A ε hA hε
  obtain ⟨η, hη, δ, hδ, hgram⟩ :=
    Submission.fvmb_orthonormal_gram_sqrt_det_le_first_order P n A ε hA hε
  refine ⟨δ, hδ, fun t ht K B hK hB => ?_⟩
  subst hK
  set e := stdOrthonormalBasis ℝ K with he
  have hon : Orthonormal ℝ (fun i => ((e i : K) : Euclid P)) :=
    e.orthonormal.comp_linearIsometry K.subtypeₗᵢ
  have hspan : Submodule.span ℝ (Set.range (fun i => ((e i : K) : Euclid P))) = K := by
    have h : Set.range (fun i => ((e i : K) : Euclid P)) = K.subtype '' Set.range e := by
      rw [← Set.range_comp]; rfl
    have htop : Submodule.span ℝ (Set.range e) = ⊤ := by
      simpa using e.toBasis.span_eq
    rw [h, Submodule.span_image, htop, Submodule.map_top, Submodule.range_subtype]
  -- the determinant on K is the Gram determinant of the frame (L e_i)
  have hgramdet : ∀ L : Euclid P →L[ℝ] Euclid P,
      ((L.comp K.subtypeL).adjoint ∘L (L.comp K.subtypeL)).det =
        Matrix.det (Matrix.of fun i j => inner ℝ (L ((e i : K) : Euclid P))
          (L ((e j : K) : Euclid P))) := by
    intro L
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix e.toBasis]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply, Matrix.of_apply]
    rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right]
    rfl
  rw [hgramdet, Submission.fvmb_trace_starProjection_comp_eq_sum_inner P _ K _ B hon hspan]
  refine hgram t ht B _ hB ?_ _ hon
  have : ContinuousLinearMap.id ℝ (Euclid P) + t • B - ContinuousLinearMap.id ℝ (Euclid P) -
      t • B = 0 := by abel
  rw [this, norm_zero]
  exact mul_nonneg hη.le (abs_nonneg t)
```

## Key steps

1. Take η, δ from gram_first_order for (P, n, A, ε); with L = I + tB the error ‖L − I − tB‖ is 0.
2. In an orthonormal basis e of K the matrix of ((Lι)*(Lι)) is the Gram matrix (⟨Le_i, Le_j⟩), so the determinants agree.
3. gram_first_order bounds √det Gram by 1 + tΣ⟨τ_a, Bτ_a⟩ + ε|t|; trace_frame identifies the sum with trace(P_K ∘ B).

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
