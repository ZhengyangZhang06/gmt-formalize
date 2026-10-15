# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.product_support_density-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.product_support_density-a1.radial_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent proof (density of S at t + y), applied there to the profile f(r) = μ₀(B_r(y)). The parent rescales s = t − ρσ and applies dominated convergence; here the same two inputs, namely (i) the limit of f(r)/(ω_m r^m), which gives two-sided bounds valid for all small radii, and (ii) the slice identity ω_m ∫_{B_1}(1 − |σ|²)^{m/2} dσ = ω_{d+m} (sibling ball_volume_slice, used at radius ρ), are combined by a direct two-sided comparison. This needs neither the change of variables nor a dominated-convergence theorem, because every radius r_ρ(σ) := √(ρ² − ‖σ‖²) lies in [0, ρ], so the convergence is uniform in σ. Notation: ℝ^k = Euclid k = EuclideanSpace ℝ (Fin k); L^k = volume on ℝ^k (Lebesgue measure); H^d = μHE[d] (Mathlib's normalized d-dimensional Hausdorff measure); ω_k = unitBallVolume k = L^k(B_1(0)); B_r(c) = Metric.ball c r (open; empty for r ≤ 0); √ = Real.sqrt (√c = 0 for c ≤ 0); integrals of [0, ∞]-valued functions are lower Lebesgue integrals (lintegral); ‖·‖ and ⟨·,·⟩ are the Euclidean norm and inner product. Further notation: v(r) := L^m(B_r(0)) for r ∈ ℝ (ball in ℝ^m); c(ρ) := ω_{d+m}·ofReal(ρ^{d+m}); g(ρ) := (∫_{ℝ^d} f(r_ρ(σ)) dL^d(σ)) / c(ρ).
1. (Ball volumes.) For k ∈ ℕ and r > 0, L^k(B_r(0)) = ω_k·ofReal(r^k) (Measure.addHaar_ball_of_pos together with finrank ℝ (Euclid k) = k, finrank_euclideanSpace_fin). Moreover ω_k ≠ 0 (a nonempty open ball has positive Lebesgue measure, measure_ball_pos) and ω_k ≠ ∞ (balls are bounded, measure_ball_lt_top). Hence c(ρ) ∈ (0, ∞) for ρ > 0 and ω_m·ofReal(r^m) ∈ (0, ∞) for r > 0. Also v(0) = L^m(∅) = 0 and v(r) = ω_m·ofReal(r^m) for r > 0.
2. (Slice identity.) For ρ > 0, the sibling ball_volume_slice (with ρ ≥ 0) and step 1 in dimension d + m give ∫_{ℝ^d} v(r_ρ(σ)) dL^d(σ) = L^{d+m}(B_ρ(0)) = c(ρ).
3. (Radii.) For ρ > 0 and σ ∈ ℝ^d: 0 ≤ r_ρ(σ) ≤ √(ρ²) = ρ, since ρ² − ‖σ‖² ≤ ρ² and √ is monotone (Real.sqrt_le_sqrt, Real.sqrt_sq).
4. (Reduction.) In [0, ∞] with its order topology, g(ρ) → θ along ρ ↓ 0 iff (i) for every a < θ, eventually a < g(ρ), and (ii) for every b > θ, eventually g(ρ) < b (tendsto_order). Both are proved below; when θ = ∞, (ii) is vacuous.
5. (Lower bound, (i).) Let a < θ and choose a' with a < a' < θ (exists_between); in particular a' < ∞. Since f(r)/(ω_m ofReal(r^m)) → θ and a' < θ, there is s > 0 with a' < f(r)/(ω_m ofReal(r^m)) for every r ∈ (0, s) (mem_nhdsGT_iff_exists_Ioo_subset); multiplying by the number ω_m ofReal(r^m) ∈ (0, ∞) gives a'·ω_m·ofReal(r^m) < f(r) (ENNReal.lt_div_iff_mul_lt). Let ρ ∈ (0, s) and σ ∈ ℝ^d. If r_ρ(σ) = 0, then a'·v(r_ρ(σ)) = a'·0 = 0 ≤ f(r_ρ(σ)). If r_ρ(σ) > 0, then r_ρ(σ) ∈ (0, s) by step 3, so a'·v(r_ρ(σ)) = a'·ω_m·ofReal(r_ρ(σ)^m) ≤ f(r_ρ(σ)). Integrating this pointwise inequality (lintegral_mono, which needs no measurability) and pulling out the finite constant a' (lintegral_const_mul') gives, by step 2, a'·c(ρ) ≤ ∫_{ℝ^d} f(r_ρ(σ)) dL^d(σ). Dividing by c(ρ) ∈ (0, ∞): a' = a'·c(ρ)/c(ρ) ≤ g(ρ) (ENNReal.mul_div_cancel_right, ENNReal.div_le_div_right), hence a < g(ρ) for every ρ ∈ (0, s), and (0, s) is a neighbourhood of 0 within (0, ∞) (Ioo_mem_nhdsGT).
6. (Upper bound, (ii).) Let b > θ and choose b' with θ < b' < b; in particular b' < ∞. There is s > 0 with f(r)/(ω_m ofReal(r^m)) < b', i.e. f(r) < b'·ω_m·ofReal(r^m) (ENNReal.div_lt_iff), for every r ∈ (0, s). Let ρ ∈ (0, s) and σ ∈ ℝ^d. If r_ρ(σ) = 0, then f(r_ρ(σ)) = f(0) = 0 ≤ b'·v(r_ρ(σ)). If r_ρ(σ) > 0, then r_ρ(σ) ∈ (0, s) and f(r_ρ(σ)) ≤ b'·ω_m·ofReal(r_ρ(σ)^m) = b'·v(r_ρ(σ)). Integrating as in step 5: ∫_{ℝ^d} f(r_ρ(σ)) dL^d(σ) ≤ b'·c(ρ), so g(ρ) ≤ b'·c(ρ)/c(ρ) = b' < b for every ρ ∈ (0, s).
7. By steps 4–6, g(ρ) → θ as ρ ↓ 0. ∎

Lean reference implementation (kernel-checked during this decomposition against GMT.Ch07.Submission, Lean v4.35.0-rc3, Mathlib 25730c7c, inside `namespace GMT.Ch07` with the contract's opens `open Filter Function Set MeasureTheory Metric`, `open scoped ENNReal Topology`, `open Poincare.SimonGMT.Chapter06`, `open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt)`; #print axioms gives propext, Classical.choice, Quot.sound once the sibling ball_volume_slice is available; in the check the sibling was itself fully proved, see that child):
theorem Submission.dimred_cs_psd_radial_density : ∀ (d m : ℕ) (f : ℝ → ℝ≥0∞) (θ : ℝ≥0∞), f 0 = 0 → Tendsto (fun r : ℝ => f r / (unitBallVolume m * ENNReal.ofReal (r ^ m))) (𝓝[>] 0) (𝓝 θ) → Tendsto (fun ρ : ℝ => (∫⁻ σ : Euclid d, f (Real.sqrt (ρ ^ 2 - ‖σ‖ ^ 2))) / (unitBallVolume (d + m) * ENNReal.ofReal (ρ ^ (d + m)))) (𝓝[>] 0) (𝓝 θ) := by
  intro d m f θ hf0 hlim
  -- volumes of balls
  have hvol : ∀ (k : ℕ) (r : ℝ), 0 < r →
      volume (ball (0 : Euclid k) r) = unitBallVolume k * ENNReal.ofReal (r ^ k) := by
    intro k r hr
    rw [Measure.addHaar_ball_of_pos volume (0 : Euclid k) hr, finrank_euclideanSpace_fin, mul_comm]
    rfl
  have hω0 : ∀ k : ℕ, unitBallVolume k ≠ 0 := fun k =>
    (measure_ball_pos volume (0 : Euclid k) one_pos).ne'
  have hωt : ∀ k : ℕ, unitBallVolume k ≠ ⊤ := fun k => measure_ball_lt_top.ne
  have hc0 : ∀ (k : ℕ) (r : ℝ), 0 < r → unitBallVolume k * ENNReal.ofReal (r ^ k) ≠ 0 := by
    intro k r hr
    exact mul_ne_zero (hω0 k) (ENNReal.ofReal_pos.2 (pow_pos hr k)).ne'
  have hct : ∀ (k : ℕ) (r : ℝ), unitBallVolume k * ENNReal.ofReal (r ^ k) ≠ ⊤ := fun k r =>
    ENNReal.mul_ne_top (hωt k) ENNReal.ofReal_ne_top
  -- the profile `v r = Lᵐ(B_r(0))`
  set v : ℝ → ℝ≥0∞ := fun r => volume (ball (0 : Euclid m) r) with hv
  have hv0 : v 0 = 0 := by simp [hv]
  have hslice : ∀ ρ : ℝ, 0 < ρ → ∫⁻ σ : Euclid d, v (Real.sqrt (ρ ^ 2 - ‖σ‖ ^ 2)) =
      unitBallVolume (d + m) * ENNReal.ofReal (ρ ^ (d + m)) := by
    intro ρ hρ
    rw [← hvol _ _ hρ, Submission.dimred_cs_psd_ball_volume_slice d m ρ hρ.le]
  have hsq_le : ∀ ρ : ℝ, 0 < ρ → ∀ σ : Euclid d, Real.sqrt (ρ ^ 2 - ‖σ‖ ^ 2) ≤ ρ := by
    intro ρ hρ σ
    calc Real.sqrt (ρ ^ 2 - ‖σ‖ ^ 2) ≤ Real.sqrt (ρ ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [norm_nonneg σ])
      _ = ρ := Real.sqrt_sq hρ.le
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · -- lower bound
    obtain ⟨a', haa', ha'θ⟩ := exists_between ha
    have h1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), a' < f r / (unitBallVolume m * ENNReal.ofReal (r ^ m)) :=
      (tendsto_order.1 hlim).1 a' ha'θ
    obtain ⟨s, hs, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h1
    filter_upwards [Ioo_mem_nhdsGT hs] with ρ hρ
    have hbound : ∀ σ : Euclid d, a' * v (Real.sqrt (ρ ^ 2 - ‖σ‖ ^ 2)) ≤
        f (Real.sqrt (ρ ^ 2 - ‖σ‖ ^ 2)) := by
      intro σ
      rcases (Real.sqrt_nonneg (ρ ^ 2 - ‖σ‖ ^ 2)).eq_or_lt with h | h
      · rw [← h, hv0, mul_zero]
        exact zero_le
      · have hr : Real.sqrt (ρ ^ 2 - ‖σ‖ ^ 2) ∈ Ioo 0 s :=
          ⟨h, lt_of_le_of_lt (hsq_le ρ hρ.1 σ) hρ.2⟩
        have h2 := hsub hr
        simp only [mem_ofPred_eq] at h2
        rw [ENNReal.lt_div_iff_mul_lt (Or.inl (hc0 m _ h)) (Or.inl (hct m _))] at h2
        rw [hv]
        simp only
        rw [hvol m _ h]
        exact h2.le
    have hint := lintegral_mono (μ := (volume : Measure (Euclid d))) hbound
    rw [lintegral_const_mul' _ _ (ne_top_of_lt ha'θ), hslice ρ hρ.1] at hint
    calc a < a' := haa'
      _ = a' * (unitBallVolume (d + m) * ENNReal.ofReal (ρ ^ (d + m))) /
            (unitBallVolume (d + m) * ENNReal.ofReal (ρ ^ (d + m))) :=
          (ENNReal.mul_div_cancel_right (hc0 _ _ hρ.1) (hct _ _)).symm
      _ ≤ _ := ENNReal.div_le_div_right hint _
  · -- upper bound
    obtain ⟨b', hθb', hb'b⟩ := exists_between hb
    have h1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), f r / (unitBallVolume m * ENNReal.ofReal (r ^ m)) < b' :=
      (tendsto_order.1 hlim).2 b' hθb'
    obtain ⟨s, hs, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h1
    filter_upwards [Ioo_mem_nhdsGT hs] with ρ hρ
    have hbound : ∀ σ : Euclid d, f (Real.sqrt (ρ ^ 2 - ‖σ‖ ^ 2)) ≤
        b' * v (Real.sqrt (ρ ^ 2 - ‖σ‖ ^ 2)) := by
      intro σ
      rcases (Real.sqrt_nonneg (ρ ^ 2 - ‖σ‖ ^ 2)).eq_or_lt with h | h
      · rw [← h, hf0]
        exact zero_le
      · have hr : Real.sqrt (ρ ^ 2 - ‖σ‖ ^ 2) ∈ Ioo 0 s :=
          ⟨h, lt_of_le_of_lt (hsq_le ρ hρ.1 σ) hρ.2⟩
        have h2 := hsub hr
        simp only [mem_ofPred_eq] at h2
        rw [ENNReal.div_lt_iff (Or.inl (hc0 m _ h)) (Or.inl (hct m _))] at h2
        rw [hv]
        simp only
        rw [hvol m _ h]
        exact h2.le
    have hint := lintegral_mono (μ := (volume : Measure (Euclid d))) hbound
    rw [lintegral_const_mul' _ _ (ne_top_of_lt hb'b), hslice ρ hρ.1] at hint
    calc _ ≤ b' * (unitBallVolume (d + m) * ENNReal.ofReal (ρ ^ (d + m))) /
            (unitBallVolume (d + m) * ENNReal.ofReal (ρ ^ (d + m))) :=
          ENNReal.div_le_div_right hint _
      _ = b' := ENNReal.mul_div_cancel_right (hc0 _ _ hρ.1) (hct _ _)
      _ < b := hb'b

## Key steps

1. L^k(B_r(0)) = ω_k·r^k for r > 0 with ω_k ∈ (0, ∞), and L^m(B_0) = 0 = f(0).
2. By ball_volume_slice, ∫_{ℝ^d} L^m(B_{√(ρ² − ‖σ‖²)}(0)) dσ = ω_{d+m}·ρ^{d+m} for ρ > 0.
3. Every radius √(ρ² − ‖σ‖²) lies in [0, ρ]; for a' < θ < b' the hypothesis gives s > 0 with a'·ω_m r^m ≤ f(r) ≤ b'·ω_m r^m on (0, s), hence a'·L^m(B_r) ≤ f(r) ≤ b'·L^m(B_r) for r ∈ [0, s).
4. Integrating these pointwise bounds and dividing by ω_{d+m}ρ^{d+m} gives a' ≤ g(ρ) ≤ b' for ρ ∈ (0, s); tendsto_order in [0, ∞] gives g(ρ) → θ.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-product-support-density-a1/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.md}; cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/problem.md; cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `sed -n 200,600p GMT/Ch07/Contract.lean (IMRep.measure, unitBallVolume, HasMassDensity)`
- `python3 over dag.json: status/lean_statement/depends_on of im_mass_measure-a1, cone_splitting-a1, product_support_density-a1; accepted lean_statements mentioning HasMassDensity, unitBallVolume, Real.sqrt, 'volume (ball', μHE; regex for a density-uniqueness lemma; lean_name scan for psd|slice|radial|uniq`
- `python3 over nodes/root-dimension-reduction-results-a1-cone-splitting-a1/decomposition-v1.json (reuse-child precedent: tangent_projection_measurable, orientation_norm)`
- `git show 045731be7c74a51a79d0c3895070d67408b82f53:GMT/Ch07/Submission.lean | grep theorem; git show 01ae2c59e8d725f9f3839402fe6fe9bf93c32c3a:GMT/Ch07/Submission.lean | grep -n dimred_im_mass_measure`
- `sed -n 1,400p local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (Isometry.map_euclideanHausdorffMeasure, EuclideanSpace.euclideanHausdorffMeasure_eq_volume)`
- `grep -n 'addHaar_ball_of_pos|addHaar_ball ' Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean; sed -n 736,810p Mathlib/MeasureTheory/Constructions/Pi.lean; sed -n 160,240p Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean; sed -n 370,395p Mathlib/Analysis/InnerProductSpace/PiL2.lean; sed -n 985,1010p Mathlib/Analysis/Normed/Lp/PiLp.lean; grep prod_norm_sq_eq_of_L2 Mathlib/Analysis/Normed/Lp/ProdLp.lean; grep 'le_sqrt|lt_sqrt|sqrt_le_sqrt|sqrt_sq' Mathlib/Analysis/Real/Sqrt.lean (all in the snapshot mathlib)`
- `grep -c dimred_cs_psd dag.json; grep -rl dimred_cs_psd GMT .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes lake-packages-25730c7c/simongmt/Poincare; grep -rl --include=*.lean dimred_cs_psd workspaces/.swarm-worktrees (no match anywhere)`
- `LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/psd-decomp/{Smoke,Assembly,ProveA,ProveC,ProveFD,Final}.lean (#check with pp.coercions, #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-product-support-density-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-product-support-density-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-im-mass-measure-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Real/Sqrt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/.swarm-worktrees`
- `/tmp/psd-decomp/Assembly.lean`
- `/tmp/psd-decomp/Final.lean`

Pins. The snapshot manifest gives project b4d606d and mathlib 25730c7c. All Lean checks used the matching workspace build, Lean v4.35.0-rc3.

Library.
- The snapshot Mathlib has everything the four new children need:
  - H^d on a d-plane equals Lebesgue measure: Isometry.map_euclideanHausdorffMeasure and EuclideanSpace.euclideanHausdorffMeasure_eq_volume.
  - Cavalieri slicing of balls: LinearIsometryEquiv.piLpCongrLeft with finSumFinEquiv, PiLp.sumPiLpEquivProdLpPiLp, WithLp.volume_preserving_ofLp, WithLp.prod_norm_sq_eq_of_L2 and Measure.prod_apply.
  - Ball volumes: Measure.addHaar_ball_of_pos.
  - Translation invariance: lintegral_sub_right_eq_self.
  - Square roots: Real.lt_sqrt and Real.le_sqrt.
- SimonGMT has no product or slicing results for currents.
- dag.json has no accepted lemma on ball slicing, radial densities or density uniqueness, so the only possible reuse is the mass–measure identity.

Reuse. dimred_im_mass_measure (node im_mass_measure-a1, status accepted, candidate 01ae2c59, Submission.lean line 1730) has a frozen type byte-identical to the child's. It is missing from this node's proof base 045731b, so it is listed as a reused child.

Names. dimred_cs_psd_* occurs nowhere: not in dag.json, GMT, the node records, SimonGMT or the 3004 worktrees.

Lean.
- All 5 child types elaborate after import GMT.Ch07.Submission, in namespace GMT.Ch07 with the contract opens.
- The 4 new children are fully proved, using only the axioms propext, Classical.choice and Quot.sound.
- The frozen parent type is assembled from the 5 children. Its only sorryAx comes from the stub of the accepted dimred_im_mass_measure.
