# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.cutoff_estimates-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.cutoff_estimates-a1.annular_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent proof steps 2–5, i.e. Simon Ch. 3, 4.3 (3)–(6) (chapter-03.txt lines 621–652) in the finite-difference form documented by the parent. This child uses the siblings radial_cutoff (Submission.codim1_rdo_dg_ce_radial_cutoff) and signed_layer_cake (Submission.codim1_rdo_dg_ce_signed_layer_cake). The parent applies it to (F, ν, v) and to (ℝ^{m+1} ∖ F, −ν, −v).

Fix ρ, δ > 0 with ρ + δ < ρ₂. Write B̄_r := B̄_r(y), A := B_{ρ+δ}(y) ∖ B̄_ρ(y), L := L^P (volume) and μ(·)_ℝ := ENNReal.toReal.

1. Finiteness. B̄_ρ ⊆ B̄_{ρ+δ} ⊆ B̄_{ρ₂} ⊆ D, so μ(B̄_ρ) ≤ μ(B̄_{ρ+δ}) ≤ μ(B̄_{ρ₂}) < ∞. A ⊆ B_{ρ+δ}(y) is a bounded Borel set, so L(F ∩ A) ≤ L(A) < ∞.

2. Cut-off (parent step 2). radial_cutoff with P, y, ρ, δ gives ζ : ℝ^P → ℝ with these properties:
- ζ is C¹ with compact support, 0 ≤ ζ ≤ 1, and ζ = 1 on B̄_ρ;
- tsupport ζ ⊆ B̄_{ρ+δ};
- ‖Dζ(z)‖ ≤ 3/(2δ) for all z, and Dζ(z) = 0 for z ∉ A;
- for each t ∈ (0, 1], {ζ ≥ t} = B̄_r for some r with ρ ≤ r < ρ + δ.

3. Gauss–Green (parent step 3). Let φ(z) := ζ(z)v. It is C¹ (a C¹ scalar times a constant vector) and has compact support, with tsupport φ ⊆ tsupport ζ ⊆ B̄_{ρ+δ} ⊆ D. Its derivative is the rank-one map Dφ(z)w = (Dζ(z)w)v, whose trace is Dζ(z)v. Also ⟨φ(z), ν(z)⟩ = ζ(z)⟨v, ν(z)⟩. So (GG) gives
(i) ∫ ζ(z)⟨v, ν(z)⟩ dμ(z) = −∫_F Dζ(z)v dL(z).

4. Upper bound. For all z, |Dζ(z)v| ≤ ‖Dζ(z)‖|v| ≤ 3/(2δ), and Dζ(z)v = 0 for z ∉ A. So |Dζ(z)v| ≤ (3/(2δ))1_A(z). This bound is L⌞F-integrable because L(A) < ∞. Hence −∫_F Dζ v dL ≤ |∫_F Dζ v dL| ≤ ∫_F (3/(2δ))1_A dL = (3/(2δ))L(F ∩ A)_ℝ.

5. Lower bound (parent step 4). Apply signed_layer_cake with X = ℝ^P, μ, ζ, g(z) := ⟨v, ν(z)⟩, S := B̄_{ρ+δ}, B := B̄_ρ and c := ½. Its hypotheses hold:
- ζ is measurable (it is continuous), and g is measurable (ν is measurable and the inner product is continuous);
- 0 ≤ ζ ≤ 1, and |g(z)| ≤ |v||ν(z)| ≤ 1 by Cauchy–Schwarz;
- S is closed, hence measurable, and μ(S) < ∞ by step 1;
- ζ(z) = 0 for z ∉ S, since such z lie outside tsupport ζ;
- ζ = 1 on B, and c ≥ 0;
- for t ∈ (0, 1], {ζ ≥ t} = B̄_r with 0 < ρ ≤ r < ρ + δ < ρ₂, so (1′) and the symmetry of the real inner product give ½μ(B̄_r)_ℝ ≤ ∫_{B̄_r} ⟨ν, v⟩ dμ = ∫_{{ζ≥t}} g dμ.
The conclusion is ½ μ(B̄_ρ)_ℝ ≤ ∫ ζ⟨v, ν⟩ dμ.

6. Combination (parent step 5). By (i) and steps 4–5, ½ μ(B̄_ρ)_ℝ ≤ (3/(2δ))L(F ∩ A)_ℝ. Multiplying by 2δ > 0 gives δ μ(B̄_ρ)_ℝ ≤ 3 L(F ∩ A)_ℝ.

7. Passage to [0, ∞]. μ(B̄_ρ) and L(F ∩ A) are finite (step 1), so ofReal(δ)·μ(B̄_ρ) = ofReal(δ μ(B̄_ρ)_ℝ) ≤ ofReal(3 L(F ∩ A)_ℝ) = ofReal(3)·L(F ∩ A). ∎

Appendix (non-normative). A kernel-checked Lean proof of exactly this frozen statement was found during decomposition (workspace file GMT/Scratch/codim1_rdo_dg_cutoff_estimates_decomposition/Full.lean, git-ignored; it uses only the contract imports, compiles without warnings after `import GMT.Ch07.Submission` inside `namespace GMT.Ch07` with the contract opens, and `#print axioms` gives [propext, Classical.choice, Quot.sound]):

```lean
theorem Submission.codim1_rdo_dg_ce_annular_bound : ∀ (P : ℕ) (D F : Set (Euclid P)) (μ : Measure (Euclid P)) (ν : Euclid P → Euclid P) (y v : Euclid P) (ρ₂ : ℝ), MeasurableSet F → closedBall y ρ₂ ⊆ D → μ (closedBall y ρ₂) ≠ ∞ → Measurable ν → (∀ z, ‖ν z‖ ≤ 1) → ‖v‖ ≤ 1 → (∀ φ : Euclid P → Euclid P, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid P) (fderiv ℝ φ z : Euclid P →ₗ[ℝ] Euclid P) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → (∀ r : ℝ, 0 < r → r < ρ₂ → (1 / 2 : ℝ) * (μ (closedBall y r)).toReal ≤ ∫ z in closedBall y r, inner ℝ (ν z) v ∂μ) → ∀ ρ δ : ℝ, 0 < ρ → 0 < δ → ρ + δ < ρ₂ → ENNReal.ofReal δ * μ (closedBall y ρ) ≤ ENNReal.ofReal 3 * volume (F ∩ (ball y (ρ + δ) \ closedBall y ρ)) := by
  intro P D F μ ν y v ρ₂ hF hD hfin hν hν1 hv hGG h1' ρ δ hρ hδ hρδ
  obtain ⟨ζ, hζC, hζc, hζ01, hζ1, hζsupp, hζgrad, hζzero, hζlevel⟩ :=
    Submission.codim1_rdo_dg_ce_radial_cutoff P y ρ δ hρ hδ
  have hSsub : closedBall y (ρ + δ) ⊆ closedBall y ρ₂ := closedBall_subset_closedBall hρδ.le
  have hSfin : μ (closedBall y (ρ + δ)) ≠ ∞ := ne_top_of_le_ne_top hfin (measure_mono hSsub)
  have hg : Measurable (fun z => inner ℝ v (ν z)) := (continuous_const.inner continuous_id).measurable.comp hν
  -- Step 4 (layer cake) via the layer-cake child.
  have hlow : (1 / 2 : ℝ) * (μ (closedBall y ρ)).toReal ≤ ∫ z, ζ z * inner ℝ v (ν z) ∂μ := by
    refine Submission.codim1_rdo_dg_ce_signed_layer_cake (Euclid P) μ ζ (fun z => inner ℝ v (ν z))
      (closedBall y (ρ + δ)) (closedBall y ρ) (1 / 2) hζC.continuous.measurable hg hζ01 ?_
      measurableSet_closedBall hSfin ?_ hζ1 (by norm_num) ?_
    · intro z
      calc |inner ℝ v (ν z)| ≤ ‖v‖ * ‖ν z‖ := abs_real_inner_le_norm _ _
        _ ≤ 1 * 1 := mul_le_mul hv (hν1 z) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    · intro z hz
      exact image_eq_zero_of_notMem_tsupport (fun h => hz (hζsupp h))
    · intro t ht0 ht1
      obtain ⟨r, hr1, hr2, hrset⟩ := hζlevel t ht0 ht1
      rw [hrset]
      have := h1' r (by linarith) (by linarith)
      simpa only [real_inner_comm] using this
  -- Step 3 (Gauss–Green) : the identity for φ = ζ • v.
  have hφC : ContDiff ℝ 1 (fun z => ζ z • v) := hζC.smul contDiff_const
  have hφc : HasCompactSupport (fun z => ζ z • v) := hζc.smul_right
  have hφD : tsupport (fun z => ζ z • v) ⊆ D :=
    (tsupport_smul_subset_left _ _).trans (hζsupp.trans (hSsub.trans hD))
  have hGGζ := hGG _ hφC hφc hφD
  have hint : ∫ z, inner ℝ (ζ z • v) (ν z) ∂μ = ∫ z, ζ z * inner ℝ v (ν z) ∂μ := by
    simp only [real_inner_smul_left]
  have htrace : ∀ z, LinearMap.trace ℝ (Euclid P)
      (fderiv ℝ (fun z => ζ z • v) z : Euclid P →ₗ[ℝ] Euclid P) = fderiv ℝ ζ z v := by
    intro z
    rw [fderiv_smul_const ((hζC.differentiable one_ne_zero) z) v]
    exact LinearMap.trace_smulRight _ _
  simp only [htrace] at hGGζ
  rw [hint] at hGGζ
  set A := ball y (ρ + δ) \ closedBall y ρ with hA
  have hAmeas : MeasurableSet A := measurableSet_ball.diff measurableSet_closedBall
  have hAfin : volume A ≠ ∞ := ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono sdiff_subset)
  have hFAfin : volume (F ∩ A) ≠ ∞ := ne_top_of_le_ne_top hAfin (measure_mono inter_subset_right)
  have hpt : ∀ z, ‖fderiv ℝ ζ z v‖ ≤ A.indicator (fun _ => 3 / (2 * δ)) z := by
    intro z
    by_cases hz : z ∈ A
    · rw [indicator_of_mem hz]
      calc ‖fderiv ℝ ζ z v‖ ≤ ‖fderiv ℝ ζ z‖ * ‖v‖ := (fderiv ℝ ζ z).le_opNorm v
        _ ≤ 3 / (2 * δ) * 1 := mul_le_mul (hζgrad z) hv (norm_nonneg _) (by positivity)
        _ = 3 / (2 * δ) := mul_one _
    · rw [indicator_of_notMem hz, hζzero z hz]
      simp
  have hbound_int : Integrable (A.indicator (fun _ => 3 / (2 * δ))) (volume.restrict F) := by
    refine Integrable.restrict ?_
    exact (integrableOn_const hAfin).integrable_indicator hAmeas
  have hup : -∫ z in F, fderiv ℝ ζ z v ≤ 3 / (2 * δ) * (volume (F ∩ A)).toReal := by
    have h1 : ‖∫ z in F, fderiv ℝ ζ z v‖ ≤ ∫ z in F, A.indicator (fun _ => 3 / (2 * δ)) z :=
      norm_integral_le_of_norm_le hbound_int (Eventually.of_forall hpt)
    have h2 : ∫ z in F, A.indicator (fun _ => 3 / (2 * δ)) z = 3 / (2 * δ) * (volume (F ∩ A)).toReal := by
      rw [integral_indicator_const _ hAmeas, smul_eq_mul, mul_comm]
      congr 1
      simp only [Measure.real, Measure.restrict_apply hAmeas, inter_comm]
    calc -∫ z in F, fderiv ℝ ζ z v ≤ ‖∫ z in F, fderiv ℝ ζ z v‖ := by
          rw [Real.norm_eq_abs]; exact neg_le_abs _
      _ ≤ _ := h1
      _ = _ := h2
  have hreal : δ * (μ (closedBall y ρ)).toReal ≤ 3 * (volume (F ∩ A)).toReal := by
    have key : (1 / 2 : ℝ) * (μ (closedBall y ρ)).toReal ≤ 3 / (2 * δ) * (volume (F ∩ A)).toReal := by
      have : ∫ z, ζ z * inner ℝ v (ν z) ∂μ = -∫ z in F, fderiv ℝ ζ z v := by rw [hGGζ, neg_neg]
      linarith [hup, this, hlow]
    have h3 : 3 / (2 * δ) * (volume (F ∩ A)).toReal * (2 * δ) = 3 * (volume (F ∩ A)).toReal := by
      field_simp
    nlinarith [key, hδ]
  have hBfin : μ (closedBall y ρ) ≠ ∞ :=
    ne_top_of_le_ne_top hfin (measure_mono (closedBall_subset_closedBall (by linarith)))
  calc ENNReal.ofReal δ * μ (closedBall y ρ)
      = ENNReal.ofReal (δ * (μ (closedBall y ρ)).toReal) := by
        rw [ENNReal.ofReal_mul hδ.le, ENNReal.ofReal_toReal hBfin]
    _ ≤ ENNReal.ofReal (3 * (volume (F ∩ A)).toReal) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal 3 * volume (F ∩ A) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hFAfin]
```

## Key steps

1. Take the cut-off ζ from radial_cutoff; φ = ζv is an admissible test field with div φ = Dζ(·)v (trace of a rank-one map).
2. (GG) gives ∫ζ⟨v,ν⟩dμ = −∫_F Dζ v dL ≤ (3/(2δ))·L(F ∩ annulus), since |Dζ v| ≤ (3/(2δ))1_annulus.
3. signed_layer_cake with g = ⟨v,ν⟩, S = B̄_{ρ+δ}, B = B̄_ρ, c = ½, using (1′) on the balls {ζ ≥ t} = B̄_r, r < ρ₂, gives ∫ζ⟨v,ν⟩dμ ≥ ½μ(B̄_ρ).
4. Multiply by 2δ and pass to [0,∞] using μ(B̄_ρ) < ∞ and L(F ∩ annulus) < ∞.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `python3 scans of dag.json: de_giorgi-a1 children (status, lean_name, depth); accepted nodes whose title/statement matches cut-off|bump|smoothstep|layer|Fubini|integration by parts|divergence; statements of dorag_th_radial_cutoff, doragm_sab_cutoff_profile, dorag_ha_mv_radial_potential, dsmc_em_cutoff_tendsto_ball, doragm_sab_cutoff_mass_sandwich, doragm_sab_annulus_increment_sandwich, dorag_ha_lsc_ibp_c1_ball, regcomp_smooth_cutoff_product; collision check of the five codim1_rdo_dg_ce_* names (974 nodes: all free)`
- `grep -rn codim1_rdo_dg_ce /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt (no match)`
- `rg -n 'theorem integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable|theorem integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable|lemma trace_smulRight|theorem trace_eq_matrix_trace |theorem addHaar_ball |theorem volume_ball|theorem contDiffAt_norm|theorem norm_fderiv_le_of_lipschitz|theorem fderiv_smul_const|theorem HasCompactSupport.smul_right|theorem integral_integral_swap|theorem lintegral_eq_lintegral_meas_le|theorem inner_neg_neg|theorem finrank_euclideanSpace_fin|theorem addHaar_sphere|trace_eq_sum_inner' <snapshot>/mathlib/Mathlib`
- `rg -n for contDiff_one_iff_deriv, lipschitzWith_of_nnnorm_deriv_le, IsLocalMax.fderiv_eq_zero, IsLocalMin.fderiv_eq_zero, support_fderiv_subset, Continuous.integrable_of_hasCompactSupport, integral_inner, antitone_of_deriv_nonpos, mem_nhdsGT_iff_exists_Ioo_subset, def basisFun, Integrable.integral_prod_right, setIntegral_eq_integral_of_forall_compl_eq_zero, integral_add_compl, HasDerivWithinAt.union, norm_integral_le_of_norm_le, integral_indicator_const, integrableOn_of_bounded, IsCompact.sSup_mem, HasCompactSupport.intro, LipschitzWith.of_dist_le_mul, mul_le_mul_right' in <snapshot>/mathlib/Mathlib`
- `sed -n 560,700p book/chapter-03.txt; grep -n of the numbered steps (1)-(6), '4.3 Theorem' and 'Proof: By 1.6' in book/chapter-03.txt`
- `git show 46877ce9:GMT/Ch07/Submission.lean; git show 296e19be:GMT/Ch07/Submission.lean (accepted IBP proofs keep the contract imports; LipschitzWith.integral_lineDeriv_mul_eq usage)`
- `lake env lean -DautoImplicit=false /tmp/ce-split-check/Types.lean (five child types elaborate; sorry warnings only)`
- `lake env lean -DautoImplicit=false /tmp/ce-split-check/Assembly.lean (frozen parent type proved from child stubs; type byte-identical to handoff lean_statement; #print axioms = propext, sorryAx, Classical.choice, Quot.sound)`
- `lake env lean -DautoImplicit=false GMT/Scratch/codim1_rdo_dg_cutoff_estimates_decomposition/Full.lean and /tmp/ce-split-check/FromPayload.lean (all five children proved and the parent proved from them; no warnings; #print axioms = [propext, Classical.choice, Quot.sound] for all six)`
- `sed -n 1380,1440p and grep -n _existing_lean_name_problem /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py; cat swarm-project.json`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-3ce4c763f6/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-3ce4c763f6/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-3ce4c763f6/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Layercake.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L2Space.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/LocalExtr/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/codim1_rdo_dg_cutoff_estimates_decomposition/Full.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/codim1_rdo_dg_cutoff_estimates_decomposition/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/codim1_rdo_dg_cutoff_estimates_decomposition/child_statements.json`
- `/tmp/ce-split-check/Types.lean`
- `/tmp/ce-split-check/Assembly.lean`
- `/tmp/ce-split-check/FromPayload.lean`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`

Pins. The snapshot manifest records project b4d606db and Mathlib 25730c7c. The workspace HEAD is b4d606db, and Contract.lean and Submission.lean are byte-identical. Library. No local declaration has the exact types needed for the annulus cut-off, the signed layer cake, ∫ div φ = 0 or the quantitative normal-average bound. The closest accepted nodes differ: dorag_th_radial_cutoff, doragm_sab_cutoff_profile, dorag_ha_mv_radial_potential, dorag_ha_lsc_ibp_c1_ball. So all five children are new, with fresh codim1_rdo_dg_ce_* names that are free among 974 DAG nodes and in SimonGMT. Snapshot Mathlib supplies every tool used: LinearMap.trace_smulRight, LinearMap.trace_eq_sum_inner, fderiv_smul_const, contDiffAt_norm, norm_fderiv_le_of_lipschitz, lipschitzWith_of_nnnorm_deriv_le, IsLocalMax/IsLocalMin.fderiv_eq_zero, integral_integral_swap, Integrable.integral_prod_right, Measure.addHaar_ball, finrank_euclideanSpace_fin, Measure.integrableOn_of_bounded, and LipschitzWith.integral_lineDeriv_mul_eq (Rademacher, imported). integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (LineDeriv/IntegrationByParts.lean) and integral_inner (L2Space.lean) exist in the snapshot but are not imported by the contract; accepted submissions 46877ce9 and 296e19be keep the contract imports. Book. Simon Ch. 3, 4.3 steps (1) and (3)–(6) at chapter-03.txt lines 604–652 match the parent's cited source. Lean. The five child types elaborate. The parent's frozen type is proved from the children, with a byte-identical type. Complete proofs of all five children and of the parent build with axioms [propext, Classical.choice, Quot.sound]; they are saved in GMT/Scratch/codim1_rdo_dg_cutoff_estimates_decomposition and repeated as appendices. Runtime. The node is at depth 5 < max_depth 6, so the children (depth 6) are leaves, and the name-collision rule is satisfied.
