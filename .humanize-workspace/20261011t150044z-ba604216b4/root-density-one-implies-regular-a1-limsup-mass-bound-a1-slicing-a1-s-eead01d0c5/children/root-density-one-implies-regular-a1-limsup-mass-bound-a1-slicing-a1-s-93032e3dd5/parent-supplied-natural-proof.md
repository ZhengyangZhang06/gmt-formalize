# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_weak_limit-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_weak_limit-a1.localize-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 1 (compact neighbourhood of C inside V, Lipschitz bounds, uniform convergence) together with the smooth cut-off χ of Step 3 (“Density”). Here the cut-off multiplies the functions, u_k := χ·(h_k∘ψ), instead of taking McShane extensions. This yields global uniform convergence directly.

1. Trivial case. If C = ∅, take O = ∅, K = 0 and u_k = u = 0. Otherwise fix y₀ ∈ C. Since ‖Dh_0(0)‖ ≤ c, we have c ≥ 0.
2. Neighbourhoods. Choose δ > 0 with S := cthickening(δ, C) ⊆ V (IsCompact.exists_cthickening_subset_open). S is compact, being the closed thickening of a compact set in ℝ^d, and y₀ ∈ S. Put O := thickening(δ/2, C); O is open and contains C.
3. Cut-off. The closed sets (thickening(δ, C))ᶜ and cthickening(δ/2, C) are disjoint, since cthickening(δ/2, C) ⊆ thickening(δ, C). By the smooth Urysohn lemma (exists_contDiff_zero_iff_one_iff_of_isClosed) there is a C¹ function χ : ℝ^d → [0, 1] with χ = 0 exactly on (thickening(δ, C))ᶜ and χ = 1 exactly on cthickening(δ/2, C). Then support χ ⊆ thickening(δ, C), so tsupport χ ⊆ S ⊆ V and χ has compact support. Also χ = 1 on O.
4. Constants.
 (i) Dχ is continuous with compact support, so ‖Dχ‖ ≤ M_χ on ℝ^d.
 (ii) Dψ is continuous on the open set V, so ‖Dψ‖ ≤ M_ψ on the compact S ⊆ V.
 (iii) Each h_k is c-Lipschitz (mean value inequality from ‖Dh_k‖ ≤ c). The set ψ(S) is compact because ψ is continuous on S, so it lies in a closed ball B̄_D(ψ(y₀)). The real sequence |h_k(ψ(y₀))| converges to |h(ψ(y₀))|, so it is bounded by some B₀. For y ∈ S, |h_k(ψ(y))| ≤ |h_k(ψ(y₀))| + c|ψ(y) − ψ(y₀)| ≤ B₀ + cD =: B.
 M_χ, M_ψ and B bound norms at y₀, so they are ≥ 0. Put K := B·M_χ + c·M_ψ ≥ 0.
5. Definitions. u_k(y) := χ(y)·h_k(ψ(y)) and u(y) := χ(y)·h(ψ(y)). Since χ = 1 on O, u_k = h_k∘ψ and u = h∘ψ on O.
6. Each u_k is differentiable everywhere with ‖Du_k‖ ≤ K.
 - If y ∈ tsupport χ, then y ∈ S ⊆ V. Since V is open, ψ is differentiable at y, and h_k is differentiable at ψ(y). By the product and chain rules, Du_k(y) = χ(y)·(Dh_k(ψ(y))∘Dψ(y)) + h_k(ψ(y))·Dχ(y). Hence ‖Du_k(y)‖ ≤ 1·c·M_ψ + B·M_χ = K.
 - If y ∉ tsupport χ, then χ vanishes on the open neighbourhood (tsupport χ)ᶜ of y. So does u_k, and Du_k(y) = 0.
7. By the mean value inequality on the convex space ℝ^d, each u_k is K-Lipschitz (lipschitzWith_of_nnnorm_fderiv_le).
8. Uniform convergence. For every y, |u(y) − u_k(y)| = χ(y)·|h(ψ(y)) − h_k(ψ(y))| ≤ sup_x |h(x) − h_k(x)|. This tends to 0 because h_k → h uniformly on ℝ^P.
9. u is K-Lipschitz: |u(x) − u(z)| = lim_k |u_k(x) − u_k(z)| ≤ K|x − z|.
Steps 2, 5, 7, 8 and 9 give all the asserted properties. ∎

Lean realization: compiled during decomposition with the pinned toolchain in the Submission layout, as the body of `theorem Submission.dor_lmbsf_pwl_chart_cutoff_localize : (frozen lean_statement) := by` inside `namespace GMT.Ch07`. #print axioms reports only propext, Classical.choice and Quot.sound. Extra imports: Mathlib.Geometry.Manifold.PartitionOfUnity.
```lean
  intro P d V C ψ hs h c hV hψ hC hCV hhs hhsb hU
  rcases C.eq_empty_or_nonempty with hCe | ⟨y₀, hy₀⟩
  · refine ⟨∅, 0, fun _ _ => 0, fun _ => 0, isOpen_empty, by simp [hCe],
      fun _ => LipschitzWith.const 0, LipschitzWith.const 0, ?_, by simp, by simp⟩
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    exact Eventually.of_forall fun _ _ => by simpa using hε
  have hc : 0 ≤ c := (norm_nonneg _).trans (hhsb 0 0)
  obtain ⟨δ, hδ, hδV⟩ := hC.exists_cthickening_subset_open hV hCV
  have hδ2 : 0 < δ / 2 := by positivity
  set S := cthickening δ C with hSdef
  have hS : IsCompact S := hC.cthickening
  have hst : Disjoint (thickening δ C)ᶜ (cthickening (δ / 2) C) := by
    rw [disjoint_compl_left_iff_subset]
    exact cthickening_subset_thickening' hδ (by linarith) C
  obtain ⟨χ, hχs, hχr, hχ0, hχ1⟩ := exists_contDiff_zero_iff_one_iff_of_isClosed (n := 1)
    isOpen_thickening.isClosed_compl isClosed_cthickening hst
  have hχ01 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1 := fun y => hχr ⟨y, rfl⟩
  have hsupp : tsupport χ ⊆ S := by
    apply closure_minimal _ isClosed_cthickening
    intro y hy
    by_contra hcon
    exact hy ((hχ0 y).1 (fun h' => hcon (thickening_subset_cthickening δ C h')))
  have hχc : HasCompactSupport χ := hS.of_isClosed_subset (isClosed_tsupport χ) hsupp
  obtain ⟨Mχ, hMχ⟩ := (hχc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (hχs.continuous_fderiv one_ne_zero)
  obtain ⟨Mψ, hMψ⟩ := hS.exists_bound_of_continuousOn
    ((hψ.continuousOn_fderiv_of_isOpen hV le_rfl).mono hδV)
  have hy₀S : y₀ ∈ S := self_subset_cthickening C hy₀
  have hMχ0 : 0 ≤ Mχ := (norm_nonneg _).trans (hMχ y₀)
  have hMψ0 : 0 ≤ Mψ := (norm_nonneg _).trans (hMψ y₀ hy₀S)
  have hhsL : ∀ k, LipschitzWith ⟨c, hc⟩ (hs k) := fun k =>
    lipschitzWith_of_nnnorm_fderiv_le ((hhs k).differentiable one_ne_zero) (fun x =>
      NNReal.coe_le_coe.mp (by rw [coe_nnnorm]; exact hhsb k x))
  have hψS : IsCompact (ψ '' S) := hS.image_of_continuousOn (hψ.continuousOn.mono hδV)
  obtain ⟨D, hD⟩ := hψS.isBounded.subset_closedBall (ψ y₀)
  obtain ⟨B₀, hB₀⟩ := ((hU.tendsto_at (ψ y₀)).abs).bddAbove_range
  set B := B₀ + c * D with hBdef
  have hB : ∀ k, ∀ y ∈ S, |hs k (ψ y)| ≤ B := by
    intro k y hy
    have h1 : |hs k (ψ y) - hs k (ψ y₀)| ≤ c * dist (ψ y) (ψ y₀) := by
      have := (hhsL k).dist_le_mul (ψ y) (ψ y₀)
      rw [Real.dist_eq] at this
      exact this
    have h2 : dist (ψ y) (ψ y₀) ≤ D := hD (mem_image_of_mem ψ hy)
    have h3 : |hs k (ψ y₀)| ≤ B₀ := hB₀ ⟨k, rfl⟩
    have h4 := abs_sub_abs_le_abs_sub (hs k (ψ y)) (hs k (ψ y₀))
    have h5 : c * dist (ψ y) (ψ y₀) ≤ c * D := mul_le_mul_of_nonneg_left h2 hc
    linarith
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 y₀ hy₀S)
  set K : ℝ := B * Mχ + c * Mψ with hKdef
  have hK0 : 0 ≤ K := by positivity
  set us : ℕ → Euclid d → ℝ := fun k y => χ y * hs k (ψ y) with husdef
  have hderiv : ∀ k y, DifferentiableAt ℝ (us k) y ∧ ‖fderiv ℝ (us k) y‖ ≤ K := by
    intro k y
    by_cases hy : y ∈ tsupport χ
    · have hyS : y ∈ S := hsupp hy
      have hyV : y ∈ V := hδV hyS
      have hψd : HasFDerivAt ψ (fderiv ℝ ψ y) y :=
        ((hψ.differentiableOn one_ne_zero y hyV).differentiableAt (hV.mem_nhds hyV)).hasFDerivAt
      have hhd : HasFDerivAt (hs k) (fderiv ℝ (hs k) (ψ y)) (ψ y) :=
        ((hhs k).differentiable one_ne_zero (ψ y)).hasFDerivAt
      have hχd : HasFDerivAt χ (fderiv ℝ χ y) y := (hχs.differentiable one_ne_zero y).hasFDerivAt
      have hprod : HasFDerivAt (us k) (χ y • (fderiv ℝ (hs k) (ψ y)).comp (fderiv ℝ ψ y) +
          (hs k ∘ ψ) y • fderiv ℝ χ y) y := hχd.mul (hhd.comp y hψd)
      refine ⟨hprod.differentiableAt, ?_⟩
      rw [hprod.fderiv]
      calc ‖χ y • (fderiv ℝ (hs k) (ψ y)).comp (fderiv ℝ ψ y) + (hs k ∘ ψ) y • fderiv ℝ χ y‖
          ≤ ‖χ y‖ * (‖fderiv ℝ (hs k) (ψ y)‖ * ‖fderiv ℝ ψ y‖) +
              ‖(hs k ∘ ψ) y‖ * ‖fderiv ℝ χ y‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_smul, norm_smul]
            gcongr
            exact ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ 1 * (c * Mψ) + B * Mχ := by
            gcongr
            · rw [Real.norm_eq_abs, abs_of_nonneg (hχ01 y).1]
              exact (hχ01 y).2
            · exact hhsb k (ψ y)
            · exact hMψ y hyS
            · rw [Real.norm_eq_abs]
              exact hB k y hyS
            · exact hMχ y
        _ = K := by rw [hKdef]; ring
    · have hev : us k =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
        have : (tsupport χ)ᶜ ∈ 𝓝 y := (isClosed_tsupport χ).isOpen_compl.mem_nhds hy
        filter_upwards [this] with z hz
        simp [us, image_eq_zero_of_notMem_tsupport hz]
      have h0 : HasFDerivAt (us k) (0 : Euclid d →L[ℝ] ℝ) y :=
        (hasFDerivAt_const (0 : ℝ) y).congr_of_eventuallyEq hev
      refine ⟨h0.differentiableAt, ?_⟩
      rw [h0.fderiv, norm_zero]
      exact hK0
  have husL : ∀ k, LipschitzWith ⟨K, hK0⟩ (us k) := fun k =>
    lipschitzWith_of_nnnorm_fderiv_le (fun y => (hderiv k y).1) (fun y =>
      NNReal.coe_le_coe.mp (by rw [coe_nnnorm]; exact (hderiv k y).2))
  set u : Euclid d → ℝ := fun y => χ y * h (ψ y) with hudef
  have hUu : TendstoUniformly us u atTop := by
    rw [Metric.tendstoUniformly_iff] at hU ⊢
    intro ε hε
    filter_upwards [hU ε hε] with k hk
    intro y
    have h1 := hk (ψ y)
    rw [Real.dist_eq] at h1 ⊢
    calc |u y - us k y| = |χ y| * |h (ψ y) - hs k (ψ y)| := by
          rw [← abs_mul]
          congr 1
          simp only [hudef, husdef]
          ring
      _ ≤ 1 * |h (ψ y) - hs k (ψ y)| := by
          gcongr
          rw [abs_of_nonneg (hχ01 y).1]
          exact (hχ01 y).2
      _ < ε := by linarith
  have huL : LipschitzWith ⟨K, hK0⟩ u := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    exact le_of_tendsto ((hUu.tendsto_at x).dist (hUu.tendsto_at y))
      (Eventually.of_forall fun k => (husL k).dist_le_mul x y)
  have hχO : ∀ y ∈ thickening (δ / 2) C, χ y = 1 := fun y hy =>
    (hχ1 y).1 (thickening_subset_cthickening _ _ hy)
  refine ⟨thickening (δ / 2) C, ⟨K, hK0⟩, us, u, isOpen_thickening,
    self_subset_thickening hδ2 C, husL, huL, hUu, ?_, ?_⟩
  · intro k y hy
    simp [husdef, hχO y hy]
  · intro y hy
    simp [hudef, hχO y hy]
```

## Key steps

1. Compact S = cthickening δ C ⊆ V and open O = thickening (δ/2) C ⊇ C.
2. Smooth Urysohn cut-off χ with values in [0, 1], χ = 1 on O and tsupport χ ⊆ S.
3. u_k := χ·(h_k∘ψ) and u := χ·(h∘ψ) agree with h_k∘ψ and h∘ψ on O.
4. Uniform bound ‖Du_k‖ ≤ B·M_χ + c·M_ψ from the product and chain rules, boundedness of h_k on ψ(S) and of Dχ, Dψ; Lipschitz by the mean value inequality.
5. u_k → u uniformly because 0 ≤ χ ≤ 1; the limit u is K-Lipschitz.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; cmp snapshot project/GMT/Ch07/Contract.lean against workspace GMT/Ch07/Contract.lean (identical); cmp snapshot mathlib Analysis/Calculus/Rademacher.lean, Analysis/Normed/Lp/SmoothApprox.lean, MeasureTheory/Covering/Besicovitch.lean, Geometry/Manifold/PartitionOfUnity.lean, Analysis/Calculus/FDeriv/Basic.lean, Geometry/Euclidean/Volume/Measure.lean against lake-packages-25730c7c/mathlib (all identical)`
- `python3 -I scan of dag.json: frozen types of dor_lmbsf_piece_weak_limit and dor_lmbsf_density_directions (exact string match); regex 'lineDeriv|Rademacher|weak|McShane|extend_real|density point|Besicovitch|ae_tendsto_measure_inter_div|integral_lineDeriv_mul_eq|dense_hasCompactSupport|areaJacobian|area formula|uniformly Lipschitz|TendstoUniformly' over node statements; lean_name collision check for the seven dor_lmbsf_pwl_* names (1523 nodes, none)`
- `grep -n 'integral_area_formula_of_injective_derivative|weighted_area_formula_of_injective_derivative|map_withDensity_areaJacobian_eq|integrableOn_image_iff_integrableOn_areaJacobian_smul|areaJacobianAt_eq_zero_iff_not_injective|measurable_areaJacobianAt|def areaJacobianAt|areaJacobianAt_nonneg' simongmt/Poincare/SimonGMT/Chapter02`
- `rg/grep -n 'integral_lineDeriv_mul_eq|ae_differentiableAt|HasFDerivWithinAt.lim|ae_tendsto_measure_inter_div|exist_eLpNorm_sub_le|dense_hasCompactSupport_contDiff|exists_contDiff_zero_iff_one_iff_of_isClosed|lipschitzWith_of_nnnorm_fderiv_le|ContDiff.lipschitzWith_of_hasCompactSupport|norm_fderiv_le_of_lipschitz|measurable_fderiv|NormedRing.inverse_continuousAt|ContinuousLinearMap.isUnit_iff_bijective|euclideanHausdorffMeasure_eq_volume|exists_cthickening_subset_open|cthickening_subset_thickening|tendsto_integral_filter_of_dominated_convergence|Integrable.smul_bdd|Integrable.bdd_mul|setIntegral_indicator|setIntegral_eq_integral_of_forall_compl_eq_zero|setIntegral_congr_ae|ae_withDensity_iff|ae_of_ae_map' in the snapshot/package mathlib`
- `python3 -I verifier gmt-compare.contract_scope(Contract.lean, 'GMT.Ch07.main_theorem') and lean_contract.validate_lean_statement on the seven child types`
- `git show proof-workspace/gmt-ch07/20261011t150044z-ba604216b4/theorems/solutions/root-density-and-tangent-cones-a1-blowup-scaling-a1-testform-correspondence-a1-7af5165c95:GMT/Ch07/Submission.lean (child layout: theorem Submission.X inside namespace GMT.Ch07)`
- `toolchains/lean-4.35.0-rc3-linux/bin/lake env lean on /tmp/pwl-decomp/{Types,Assembly,Probe2,ProtoA1,ProtoA,ProtoB,ProtoE,ProtoC,ProtoF,ProtoD,All,Layout,LayoutCmp}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-eead01d0c5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-eead01d0c5/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-e999363692/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Normed/Operator/Banach.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/pwl-decomp/Types.lean`
- `/tmp/pwl-decomp/Assembly.lean`
- `/tmp/pwl-decomp/All.lean`
- `/tmp/pwl-decomp/Layout.lean`
- `/tmp/pwl-decomp/LayoutCmp.lean`

Snapshot: project b4d606d, mathlib 25730c7c. The snapshot Contract.lean and the cited mathlib files are byte-identical to the workspace and package trees.

No existing or accepted DAG declaration has any of the seven child types. The closest node, dor_lmb_fcd_jacobian_weak_continuity, is unaccepted and states a different, Jacobian-minor result. So all seven children get fresh dor_lmbsf_pwl_* names, none used among the 1523 nodes.

Library facts that suffice, all confirmed by compilation:
- SimonGMT Chapter02: integral_area_formula_of_injective_derivative, integrableOn_image_iff_integrableOn_areaJacobian_smul, map_withDensity_areaJacobian_eq, areaJacobianAt_eq_zero_iff_not_injective, measurable_areaJacobianAt.
- Mathlib: LipschitzWith.integral_lineDeriv_mul_eq, LipschitzWith.ae_differentiableAt, MemLp.exist_eLpNorm_sub_le, Besicovitch.ae_tendsto_measure_inter_div, HasFDerivWithinAt.lim (in this version it takes dlim : d → 0), exists_contDiff_zero_iff_one_iff_of_isClosed, lipschitzWith_of_nnnorm_fderiv_le, NormedRing.inverse_continuousAt, ContinuousLinearMap.isUnit_iff_bijective, EuclideanSpace.euclideanHausdorffMeasure_eq_volume.

Lean checks:
- All seven child types validate and elaborate in the comparator scope.
- The parent assembly compiles with only standard axioms.
- All seven children are fully proven in the Submission layout with only standard axioms, and `exact Submission.X` closes each comparator challenge.
