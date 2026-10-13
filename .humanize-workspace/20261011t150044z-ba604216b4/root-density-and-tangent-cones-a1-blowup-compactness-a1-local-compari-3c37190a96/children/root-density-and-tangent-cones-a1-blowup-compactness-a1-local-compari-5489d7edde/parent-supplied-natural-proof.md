# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.c1_tangent-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.c1_tangent-a1.rescaled_tendsto-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 4–6 of the parent proof: domination via the lower Lipschitz bound, the pointwise limit, and dominated convergence along the countably generated filter s ↓ 0. It also includes the identification of the limit integral that precedes step 7. The parent applies this child with:
- B = B̄ = closedBall(c, r), which is compact and is a neighbourhood of z because z ∈ ball(c, r);
- the given g;
- the weight h(a) := J(Dg(a)) = √det(Dg(a)* ∘ Dg(a)), continuous on B̄ because Dg is continuous on the open U ⊇ B̄;
- the constant m of step 2 (the child lower_lipschitz) and the bound m|v| ≤ |Dg(z)v| (the child fderiv_lower_bound);
- f the test function.
The Jacobian is abstracted into a weight h that is continuous on B. Then the upper bound J ≤ J_max of step 2 follows from compactness of B (step 6 below). This child is the compact-neighbourhood analogue of the comparator-accepted DAG lemma codim1_rdo_c1pt_rescaled_integral_tendsto, which assumes g and h continuous on all of ℝ^n and B open. Neither holds in the parent: g is C¹ only on U, and the parent integrates over the closed ball. So the argument is given in full.

Notation. L := Dg(z) = fderiv ℝ g z. For s > 0: G_s(b) := s⁻¹(g(z + sb) − g(z)), F_s(b) := h(z + sb)·f(G_s(b)), B_s := {b ∈ ℝ^n : z + sb ∈ B}. All integrals are Bochner integrals for Lebesgue measure on ℝ^n.

1. (Support radius.) tsupport f is compact, hence bounded, so tsupport f ⊆ closedBall(0, R) for some R > 0. Thus f(y) = 0 whenever |y| > R.

2. (Inner ball.) B is a neighbourhood of z, so ball(z, ε) ⊆ B for some ε > 0. With ρ := ε/2 > 0, closedBall(z, ρ) ⊆ ball(z, ε) ⊆ B.

3. (Small scales.) Put s₀ := mρ/R > 0 and K := closedBall(0, R/m). Let 0 < s ≤ s₀ and b ∈ K. Then |(z + sb) − z| = s|b| ≤ (mρ/R)(R/m) = ρ, so z + sb ∈ closedBall(z, ρ) ⊆ B. Hence K ⊆ B_s.

4. (Vanishing off K.) Let s > 0, b ∈ B_s and b ∉ K, so |b| > R/m, i.e. R < m|b|. The hypothesis with a = z + sb ∈ B gives m·s|b| = m|(z + sb) − z| ≤ |g(z + sb) − g(z)|. Hence |G_s(b)| = s⁻¹|g(z + sb) − g(z)| ≥ m|b| > R. So f(G_s(b)) = 0 by step 1, and F_s(b) = 0.

5. (Localisation to K.) B is compact, hence closed. B_s is the preimage of B under the continuous map b ↦ z + sb, so B_s is closed and measurable. Let 0 < s < s₀. Then K ⊆ B_s by step 3, and F_s = 0 on B_s \ K by step 4. Hence ∫_{B_s} F_s = ∫_K F_s. (For a measurable set and a subset of it, the two set integrals agree when the integrand vanishes on the difference; no integrability is needed. Mathlib: setIntegral_eq_of_subset_of_forall_sdiff_eq_zero.)

6. (Uniform bound.) h is continuous on the compact set B, so |h| ≤ Λ on B for some Λ. f is continuous with compact support, so |f| ≤ C on ℝ^P for some C. Let 0 < s < s₀ and b ∈ K. Then z + sb ∈ B by step 3, so |F_s(b)| ≤ ΛC. The constant ΛC is integrable on K, which has finite Lebesgue measure.

7. (Measurability.) Let 0 < s < s₀. The continuous map b ↦ z + sb sends K into B (step 3). Since h and g are continuous on B and f is continuous, F_s is continuous on K. As K is closed, F_s is a.e.-strongly measurable for Lebesgue measure restricted to K.

8. (Pointwise limit.) Fix b ∈ ℝ^n.
- As s → 0, z + sb → z. Moreover h is continuous at z, since it is continuous on B and B is a neighbourhood of z. So h(z + sb) → h(z).
- g is differentiable at z with derivative L, so g(z + w) − g(z) − Lw = o(|w|) as w → 0. With w = sb this gives G_s(b) − Lb = s⁻¹(g(z + sb) − g(z) − L(sb)) → 0 as s ↓ 0, i.e. G_s(b) → Lb. (Mathlib: HasFDerivAt.lim with c(s) = s⁻¹, where |c(s)| → ∞ along 𝓝[>] 0.)
- f is continuous, so f(G_s(b)) → f(Lb).
Hence F_s(b) → h(z)·f(Lb) as s ↓ 0, for every b.

9. (Dominated convergence.) The filter 𝓝[>] 0 is countably generated. On K, steps 6–8 give eventual a.e.-strong measurability, an eventual uniform integrable bound, and pointwise convergence. The dominated convergence theorem (tendsto_integral_filter_of_dominated_convergence) therefore gives ∫_K F_s → ∫_K h(z)·f(Lb) db as s ↓ 0.

10. (Identification of the limit.) Let b ∉ K. Then |b| > R/m, and the hypothesis on L gives |Lb| ≥ m|b| > R, so f(Lb) = 0. Hence ∫_K h(z) f(Lb) db = ∫_{ℝ^n} h(z) f(Lb) db = h(z)·∫_{ℝ^n} f(Lb) db (setIntegral_eq_integral_of_forall_compl_eq_zero, integral_const_mul).

11. (Conclusion.) By step 5, ∫_{B_s} F_s = ∫_K F_s for all s ∈ (0, s₀), hence eventually along 𝓝[>] 0. By steps 9 and 10, ∫_K F_s → h(z)·∫ f(Lb) db. Therefore ∫_{B_s} h(z + sb) f(s⁻¹(g(z + sb) − g(z))) db → h(z)·∫_{ℝ^n} f(Dg(z)b) db as s ↓ 0. ∎

Implementation note (not part of the mathematics). Mathlib alone suffices; no import beyond the frozen header is needed. The appendix below is a Lean proof of exactly this type. It compiled with `lake env lean` after `import GMT.Ch07.Submission` in the comparator's replayed contract scope, with no warnings; `#print axioms` gives [propext, Classical.choice, Quot.sound]. It adapts the accepted proof of codim1_rdo_c1pt_rescaled_integral_tendsto, replacing global continuity by ContinuousOn on B. Key names: HasCompactSupport.isCompact, Bornology.IsBounded.subset_closedBall_lt, Metric.mem_nhds_iff, IsCompact.isClosed, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, IsCompact.exists_bound_of_continuousOn, Continuous.bounded_above_of_compact_support, tendsto_integral_filter_of_dominated_convergence, ContinuousOn.comp, ContinuousOn.aestronglyMeasurable, integrableOn_const, ContinuousOn.continuousAt, HasFDerivAt.lim, tendsto_inv_nhdsGT_zero, setIntegral_eq_integral_of_forall_compl_eq_zero, integral_const_mul, Tendsto.congr'.

Appendix (verified Lean draft, scope: namespace GMT.Ch07 with the contract's open commands):
```lean
theorem Submission.dtc_bc_lc_sl_c1t_rescaled_tendsto : (∀ (P n : ℕ) (g : Euclid n → Euclid P) (h : Euclid n → ℝ) (B : Set (Euclid n)) (z : Euclid n) (m : ℝ) (f : Euclid P → ℝ), IsCompact B → B ∈ 𝓝 z → ContinuousOn g B → DifferentiableAt ℝ g z → ContinuousOn h B → 0 < m → (∀ a ∈ B, m * ‖a - z‖ ≤ ‖g a - g z‖) → (∀ v : Euclid n, m * ‖v‖ ≤ ‖fderiv ℝ g z v‖) → Continuous f → HasCompactSupport f → Tendsto (fun s : ℝ => ∫ b in {b : Euclid n | z + s • b ∈ B}, h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z))) (𝓝[>] 0) (𝓝 (h z * ∫ b, f (fderiv ℝ g z b)))) := by
  intro P n g h B z m f hBc hBz hg hgz hh hm hgB hL hf hfs
  -- Step 1: `f = 0` off `closedBall 0 R`
  obtain ⟨R, hR, hRf⟩ : ∃ R : ℝ, 0 < R ∧ ∀ y, R < ‖y‖ → f y = 0 := by
    obtain ⟨R, hR, hsub⟩ := hfs.isCompact.isBounded.subset_closedBall_lt 0 0
    refine ⟨R, hR, fun y hy => ?_⟩
    by_contra hne
    have hy' := hsub (subset_tsupport f hne)
    rw [mem_closedBall, dist_zero_right] at hy'
    linarith
  -- Step 2: `closedBall z ρ ⊆ B`
  obtain ⟨ρ, hρ, hρB⟩ : ∃ ρ : ℝ, 0 < ρ ∧ closedBall z ρ ⊆ B := by
    obtain ⟨ε, hε, hεB⟩ := Metric.mem_nhds_iff.1 hBz
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεB⟩
  -- Steps 3–4: `K = closedBall 0 (R / m)`, `s₀ = m ρ / R`; the integrand vanishes on `B_s \ K`
  have hs₀ : 0 < m * ρ / R := div_pos (mul_pos hm hρ) hR
  have hKB : ∀ s : ℝ, 0 < s → s ≤ m * ρ / R → ∀ b ∈ closedBall (0 : Euclid n) (R / m),
      z + s • b ∈ B := by
    intro s hs hss b hb
    apply hρB
    rw [mem_closedBall, dist_zero_right] at hb
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le]
    calc s * ‖b‖ ≤ m * ρ / R * (R / m) := mul_le_mul hss hb (norm_nonneg _) hs₀.le
      _ = ρ := by field_simp
  have hout : ∀ s : ℝ, 0 < s → ∀ b : Euclid n, z + s • b ∈ B →
      b ∉ closedBall (0 : Euclid n) (R / m) → f (s⁻¹ • (g (z + s • b) - g z)) = 0 := by
    intro s hs b hbB hbK
    apply hRf
    rw [mem_closedBall, dist_zero_right, not_le, div_lt_iff₀ hm] at hbK
    have h1 := hgB _ hbB
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le] at h1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
    calc R < ‖b‖ * m := hbK
      _ = s⁻¹ * (m * (s * ‖b‖)) := by field_simp
      _ ≤ s⁻¹ * ‖g (z + s • b) - g z‖ := by gcongr
  -- Step 5: localisation to `K`
  have hloc : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      (∫ b in closedBall (0 : Euclid n) (R / m), h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z))) =
        ∫ b in {b : Euclid n | z + s • b ∈ B}, h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z)) := by
    filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    · exact (hBc.isClosed.preimage (continuous_const.add (continuous_const_smul s))).measurableSet
    · intro b hb
      exact hKB s hs.1 hs.2.le b hb
    · rintro b ⟨hbB, hbK⟩
      rw [hout s hs.1 b hbB hbK, mul_zero]
  -- Step 6: uniform bounds
  obtain ⟨Λ, hΛ⟩ := hBc.exists_bound_of_continuousOn hh
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfs
  -- Steps 7–9: measurability, pointwise limit and dominated convergence on `K`
  have hdom : Tendsto (fun s : ℝ => ∫ b in closedBall (0 : Euclid n) (R / m),
      h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z))) (𝓝[>] 0)
      (𝓝 (∫ b in closedBall (0 : Euclid n) (R / m), h z * f (fderiv ℝ g z b))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => Λ * C) ?_ ?_ ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs
      have hz : Continuous fun b : Euclid n => z + s • b :=
        continuous_const.add (continuous_const_smul s)
      have hmaps : MapsTo (fun b : Euclid n => z + s • b) (closedBall (0 : Euclid n) (R / m)) B :=
        fun b hb => hKB s hs.1 hs.2.le b hb
      have hcont : ContinuousOn (fun b : Euclid n => h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z)))
          (closedBall (0 : Euclid n) (R / m)) :=
        (hh.comp hz.continuousOn hmaps).mul (hf.comp_continuousOn
          (((hg.comp hz.continuousOn hmaps).sub continuousOn_const).const_smul s⁻¹))
      exact hcont.aestronglyMeasurable measurableSet_closedBall
    · filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with b hb
      have hmem := hKB s hs.1 hs.2.le b hb
      rw [norm_mul]
      exact mul_le_mul (hΛ _ hmem) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hΛ _ hmem))
    · exact integrableOn_const measure_closedBall_lt_top.ne
    · refine Eventually.of_forall fun b => Tendsto.mul ?_ ?_
      · -- `h (z + s • b) → h z`
        have h1 : Tendsto (fun s : ℝ => z + s • b) (𝓝 0) (𝓝 (z + (0 : ℝ) • b)) :=
          (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
        rw [zero_smul, add_zero] at h1
        exact (hh.continuousAt hBz).tendsto.comp (h1.mono_left nhdsWithin_le_nhds)
      · -- difference quotients: `s⁻¹ • (g (z + s • b) - g z) → L b`
        have hc : Tendsto (fun s : ℝ => ‖s⁻¹‖) (𝓝[>] 0) atTop :=
          tendsto_norm_atTop_atTop.comp tendsto_inv_nhdsGT_zero
        have hlim := hgz.hasFDerivAt.lim b hc
        simp only [inv_inv] at hlim
        exact (hf.tendsto _).comp hlim
  -- Step 10: identification of the limit
  have hid : ∫ b in closedBall (0 : Euclid n) (R / m), h z * f (fderiv ℝ g z b) =
      h z * ∫ b, f (fderiv ℝ g z b) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero, integral_const_mul]
    intro b hb
    rw [mem_closedBall, dist_zero_right, not_le, div_lt_iff₀ hm] at hb
    rw [hRf _ (hb.trans_le ((mul_comm _ _).le.trans (hL b))), mul_zero]
  rw [← hid]
  exact hdom.congr' hloc
```

## Key steps

1. Choose R with f = 0 off closedBall(0, R) and ρ with closedBall(z, ρ) ⊆ B; for 0 < s < s₀ = mρ/R the ball K = closedBall(0, R/m) satisfies z + sK ⊆ B.
2. The lower bound m|a − z| ≤ |g(a) − g(z)| on B gives |G_s(b)| ≥ m|b| > R off K, so the integral over B_s equals the integral over K for 0 < s < s₀.
3. On K the integrand is continuous, bounded by sup_B|h|·sup|f| (B compact), and converges pointwise to h(z)f(Dg(z)b) (continuity of h at z, differentiability of g at z).
4. Dominated convergence along 𝓝[>]0 and f(Dg(z)b) = 0 off K (from m|v| ≤ |Dg(z)v|) give the limit h(z)∫ f(Dg(z)b) db.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD in snapshot mathlib (25730c7c759d108ef87ab70af2342a196760f79d) and project (b4d606db1da5da8fa2c0292ad4924d97de8b3c4b); simongmt rev 2b3663083f3fe399b6296fb8eaee52169170e197 in snapshot project/lake-manifest.json = workspace .lake/packages/simongmt HEAD; diff snapshot project/GMT/Ch07/Contract.lean vs workspace Contract.lean and Submission.lean (identical; Submission is a byte copy)`
- `sed -n 1,160p .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (blowUpMap, HasApproximateTangentSpaceAt = finrank ∧ Tendsto over 𝓝[>] 0 for every f : C_c)`
- `grep -n '^theorem' SimonGMT Chapter02/{WeightedArea,AreaLinearWeighted,AreaWeighted}.lean; sed WeightedArea.lean (integral_area_formula_of_injective_derivative, weighted_area_formula_volume_of_injective_derivative), AreaLinearWeighted.lean (weighted_linear_area_formula), Area.lean (areaJacobianAt), AreaApproximation.lean (continuous_normDet, measurable_areaJacobianAt)`
- `python3 -I import-closure walk from the Submission.lean imports over .lake/packages/simongmt: SimonGMT closure = Chapter01.{Basic,Hausdorff,MetricCriterion}, Chapter02.Lipschitz, Chapter03.Rectifiable (no WeightedArea / AreaLinearWeighted / AreaFormula)`
- `python3 -I tally of import headers over accepted candidate commits (892 keep the frozen header; some add Chapter02.WeightedArea, Chapter02.AreaLipschitz, BumpFunction.SmoothApprox); sed verifier/gmt-compare.py frozen_inputs/candidate_inputs (Submission.lean is excluded from the frozen byte check)`
- `python3 -I scans of dag.json (1523 nodes): lean_statement containing HasApproximateTangentSpaceAt together with ContDiff/fderiv/Lipschitz/graph; lean_name matching c1_image|lower_lipschitz; children of root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.rectifiable_density_one-a1.c1_piece_tangent-a1`
- `python3 -I /tmp/c1t_scripts/verify_reuse.py: git show <candidate_commit>:GMT/Ch07/Submission.lean, whitespace-normalised type comparison and sorry scan for codim1_rdo_c1pt_{fderiv_lower_bound,rescaled_area_formula,linear_range_integral,rescaled_integral_tendsto} and codim1_rdo_c1_piece_approxTangent (all IDENTICAL, no sorry); import-line count of commits dd15d7b, e2ca8ae, 9a707fe, 9ff7690 (8 = frozen header)`
- `lake env lean /tmp/c1t_check/reuse/Sub9ff.lean (commit 9ff76906 Submission + #print axioms)`
- `rg -n in snapshot mathlib/Mathlib: 'theorem ContDiffAt.hasStrictFDerivAt ', 'alias ⟨HasStrictFDerivAt.isLittleO', 'theorem IsCompact.tendsto_subseq ', 'theorem tendsto_one_div_add_atTop_nhds_zero_nat', 'theorem IsLittleO.tendsto_div_nhds_zero', 'theorem IsLittleO.comp_tendsto', 'theorem tendsto_integral_filter_of_dominated_convergence', 'theorem setIntegral_eq_of_subset_of_forall_sdiff_eq_zero', 'theorem HasFDerivAt.lim', 'theorem ContDiffOn.continuousOn_fderiv_of_isOpen'; grep mem_sphere_zero_iff_norm, IsLittleO.norm_norm, Filter.Tendsto.prodMk_nhds`
- `grep -rl dtc_bc_lc_sl_c1t over the run directory (0 files); git log --all --oneline -S 'dtc_bc_lc_sl_c1t' over 6398 refs (0 commits)`
- `python3 -I /tmp/c1t_scripts/scope.py and /tmp/c1t_scripts/gen.py (gmt-compare.contract_scope and child_modules in contract mode; lean_contract.validate_lean_statement on all five child types)`
- `lake env lean /tmp/c1t_check/final/Challenge_{lower_lipschitz,rescaled_tendsto,fderiv_lower_bound,rescaled_area_formula,linear_range_integral}.lean, /tmp/c1t_check/assembly/Assembly.lean, /tmp/c1t_check/childA/ChildA.lean, /tmp/c1t_check/childB/ChildB.lean, /tmp/c1t_check/final/Combined.lean, /tmp/c1t_check/final/EndToEnd.lean (with #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Asymptotics/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Asymptotics/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLinearWeighted.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-3c37190a96/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-09907e06c7/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-e9bb54472d/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-bab615aebf/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-272e126047/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/c1t_check/reuse/Sub9ff.lean`
- `/tmp/c1t_check/final/Challenge_lower_lipschitz.lean`
- `/tmp/c1t_check/final/Challenge_rescaled_tendsto.lean`
- `/tmp/c1t_check/final/Challenge_fderiv_lower_bound.lean`
- `/tmp/c1t_check/final/Challenge_rescaled_area_formula.lean`
- `/tmp/c1t_check/final/Challenge_linear_range_integral.lean`
- `/tmp/c1t_check/assembly/Assembly.lean`
- `/tmp/c1t_check/childA/ChildA.lean`
- `/tmp/c1t_check/childB/ChildB.lean`
- `/tmp/c1t_check/final/Combined.lean`
- `/tmp/c1t_check/final/EndToEnd.lean`

Pins match: snapshot Mathlib 25730c7c and project b4d606db; workspace SimonGMT at 2b366308. The snapshot Contract.lean equals the workspace Contract.lean, and Submission.lean is a byte copy of it.

SimonGMT has the cited weighted area formulas, in Chapter02/WeightedArea.lean and Chapter02/AreaLinearWeighted.lean, but neither is in Submission.lean's import closure.

The DAG already has comparator-accepted, sorry-free declarations whose types are verbatim the Bochner/√det forms of supplied steps 3 and 7, plus the derivative lower bound:
- codim1_rdo_c1pt_rescaled_area_formula (e2ca8ae)
- codim1_rdo_c1pt_linear_range_integral (9a707fe)
- codim1_rdo_c1pt_fderiv_lower_bound (dd15d7b)
Their commits keep the frozen header, and their axioms are [propext, Classical.choice, Quot.sound]. These three are reused.

No accepted declaration covers step 2 on a compact set, or steps 4–6 with g C¹ only on U and the closed ball:
- codim1_rdo_c1pt_rescaled_integral_tendsto needs g and the weight continuous everywhere and B open;
- codim1_rdo_c1cov_local_lower_lipschitz is only local and needs global ContDiff;
- dor_lmbsf_c1_image_approxTangent is still decomposing.
So there are two new leaves. Snapshot Mathlib supplies everything they need: ContDiffAt.hasStrictFDerivAt, IsCompact.tendsto_subseq, the isLittleO calculus, tendsto_integral_filter_of_dominated_convergence and setIntegral_eq_of_subset_of_forall_sdiff_eq_zero.

All five child types validate and elaborate in the comparator contract scope. The frozen parent type is derived from them with no sorry, and its axioms are [propext, Classical.choice, Quot.sound].
