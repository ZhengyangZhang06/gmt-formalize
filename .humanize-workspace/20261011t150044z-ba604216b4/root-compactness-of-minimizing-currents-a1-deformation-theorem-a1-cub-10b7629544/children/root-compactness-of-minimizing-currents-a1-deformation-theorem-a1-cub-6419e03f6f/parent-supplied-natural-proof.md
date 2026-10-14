# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_trace-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_trace-a1.coord_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2–4 of the parent proof of `cmcdt_cbm_smooth_trace`, for a single coordinate i and a C¹ field component g in place of G_i:
- the fundamental theorem of calculus along each coordinate line (the divergence theorem in direction e_i, via Fubini (F2));
- the boundary bound |vg| ≤ |v|;
- the face (trace) estimate, with side length s = 1 − 2δ ≥ 1/2.
The only change from the parent text is the order of operations. The parent first integrates the boundary terms over the face variable x' ∈ Q' and then bounds each face integral. Here the same two inequalities (steps 3 and 4 of the parent) are applied on each line, for fixed x', before integrating over x'. This avoids separate face integrals and gives the same constant: 2·(2∫|v| + ∫‖Dv‖) = 4∫|v| + 2∫‖Dv‖.

Notation and hypotheses.
- m ∈ ℕ and n := m + 1. ℝⁿ := `Euclid n` (Lebesgue measure), with coordinates z_j := z.ofLp j. ℝ^m := Fin m → ℝ (product Lebesgue measure).
- 0 ≤ δ ≤ 1/4, a := δ, b := 1 − δ.
- Q := {z ∈ ℝⁿ : δ < z_j < 1 − δ for all j} and Q' := {y ∈ ℝ^m : δ < y_k < 1 − δ for all k}.
- i ∈ Fin n and e_i := EuclideanSpace.single i 1, the i-th standard unit vector (‖e_i‖ = 1, `PiLp.norm_single`).
- ι(t, y) := toLp 2 (Fin.insertNth i t y) for t ∈ ℝ, y ∈ ℝ^m.
- v, g : ℝⁿ → ℝ are C¹ (`ContDiff ℝ 1`), and |g(y)| ≤ 1 for all y.

Claim: |∫_Q D(vg)(x)e_i dx| ≤ 4 ∫_Q |v| + 2 ∫_Q ‖Dv‖, where D(vg)(x)e_i = fderiv ℝ (fun y => v y * g y) x (EuclideanSpace.single i 1).

Sibling lemmas used:
- `cmcdt_cbm_st_box_integrableOn`: continuous functions are integrable on boxes {a < z_j < b}.
- `cmcdt_cbm_st_slice_integral`: for a ≤ b and h integrable on the box, y ↦ ∫_a^b h(ι(t, y)) dt is integrable on Q', and ∫_Q h = ∫_{Q'} ∫_a^b h(ι(t, y)) dt dy.
- `cmcdt_cbm_st_interval_bound`: for a < b, C¹ φ, γ with |γ| ≤ 1, |∫_a^b (φγ)'| ≤ (2/(b − a)) ∫_a^b |φ| + 2 ∫_a^b |φ'|.

0. Since δ ≤ 1/4, b − a = 1 − 2δ ≥ 1/2 > 0. So a < b (in particular a ≤ b) and 2/(b − a) ≤ 4. The hypothesis 0 ≤ δ is carried only to match the parent's hypotheses; this lemma does not use it.
1. Lines. For all t and y, ι(t, y) = ι(0, y) + t·e_i. Check coordinatewise, splitting j ∈ Fin n into j = i and j = i.succAbove k (`Fin.succAboveCases`):
   - at i: t = 0 + t·1;
   - at i.succAbove k ≠ i: y_k = y_k + t·0.
   Hence, for fixed y, t ↦ ι(t, y) is affine, C¹, with derivative e_i at every t (`HasDerivAt` of t ↦ c + t·e_i).
2. Integrands.
   - vg is C¹ (product), so x ↦ D(vg)(x) is continuous, and F(x) := D(vg)(x)e_i is continuous.
   - |v| and ‖Dv‖ are continuous because v is C¹, so H(x) := 4|v(x)| + 2‖Dv(x)‖ is continuous.
   - By `cmcdt_cbm_st_box_integrableOn` with box parameters δ and 1 − δ, the functions F, H, |v| and ‖Dv‖ are integrable on Q.
3. Slicing (`cmcdt_cbm_st_slice_integral`, valid since a ≤ b).
   - Applied to F: ∫_Q F = ∫_{Q'} (∫_a^b F(ι(t, y)) dt) dy.
   - Applied to H: K(y) := ∫_a^b H(ι(t, y)) dt is integrable on Q', and ∫_Q H = ∫_{Q'} K.
4. Linearity on Q. By the integrability of step 2, ∫_Q H = 4 ∫_Q |v| + 2 ∫_Q ‖Dv‖.
5. Line estimate: for every y ∈ ℝ^m, |∫_a^b F(ι(t, y)) dt| ≤ K(y).
   5a. φ(t) := v(ι(t, y)) and γ(t) := g(ι(t, y)) are C¹ (C¹ functions composed with the affine map of step 1), and |γ| ≤ 1.
   5b. By the chain rule (`HasFDerivAt.comp_hasDerivAt`) with step 1, for every t: (φγ)'(t) = D(vg)(ι(t, y))e_i = F(ι(t, y)) and φ'(t) = Dv(ι(t, y))e_i.
   5c. By `cmcdt_cbm_st_interval_bound` (a < b) and 5b: |∫_a^b F(ι(t, y)) dt| ≤ (2/(b − a)) ∫_a^b |φ| + 2 ∫_a^b |Dv(ι(t, y))e_i| dt.
   5d. Two comparisons:
       - ∫_a^b |φ| ≥ 0 (a ≤ b, nonnegative integrand) and 2/(b − a) ≤ 4, so (2/(b − a)) ∫_a^b |φ| ≤ 4 ∫_a^b |φ|.
       - For every x, |Dv(x)e_i| ≤ ‖Dv(x)‖·‖e_i‖ = ‖Dv(x)‖ by the operator-norm bound (`ContinuousLinearMap.le_opNorm`). Both integrands are continuous in t, so monotonicity of the interval integral (a ≤ b) gives ∫_a^b |Dv(ι(t, y))e_i| dt ≤ ∫_a^b ‖Dv(ι(t, y))‖ dt.
   5e. Continuous integrands are interval integrable, so by linearity K(y) = 4 ∫_a^b |φ| + 2 ∫_a^b ‖Dv(ι(t, y))‖ dt. Combining 5c–5e gives the line estimate.
6. Conclusion.
   - |∫_Q F| = |∫_{Q'} ∫_a^b F(ι(t, y)) dt dy| by step 3.
   - This is ≤ ∫_{Q'} |∫_a^b F(ι(t, y)) dt| dy, since |∫f| ≤ ∫|f|.
   - This is ≤ ∫_{Q'} K by monotonicity (`integral_mono_of_nonneg`): the left integrand is ≥ 0, K is integrable on Q' (step 3), and the pointwise bound is step 5.
   - ∫_{Q'} K = ∫_Q H by step 3, and ∫_Q H = 4 ∫_Q |v| + 2 ∫_Q ‖Dv‖ by step 4. ∎

Formalization notes. A scratch build checked the Lean proof below against exactly this frozen type. It used Lean v4.35.0-rc3 and Mathlib 25730c7c, with the declaration inserted into a copy of `GMT/Ch07/Submission.lean` after the contract's `noncomputable section … end` and before `main_theorem`, in namespace `GMT.Ch07` with the contract's `open`s. It needs no imports beyond the frozen header, and `#print axioms` lists only propext, Classical.choice and Quot.sound. The proof calls the three sibling declarations by their final names `Submission.cmcdt_cbm_st_box_integrableOn`, `Submission.cmcdt_cbm_st_slice_integral` and `Submission.cmcdt_cbm_st_interval_bound`. `Fin.succAboveCases` is used with `induction j using Fin.succAboveCases i with | x => … | p j => …`. `PiLp.norm_single` replaces the deprecated `EuclideanSpace.norm_single`.

```lean
theorem Submission.cmcdt_cbm_st_coord_bound : ∀ (m : ℕ) (v g : Euclid (m + 1) → ℝ) (i : Fin (m + 1)) (δ : ℝ), ContDiff ℝ 1 v → ContDiff ℝ 1 g → (∀ y, |g y| ≤ 1) → 0 ≤ δ → δ ≤ 1 / 4 → |∫ x in {z : Euclid (m + 1) | ∀ j, δ < z j ∧ z j < 1 - δ}, fderiv ℝ (fun y => v y * g y) x (EuclideanSpace.single i 1)| ≤ 4 * (∫ x in {z : Euclid (m + 1) | ∀ j, δ < z j ∧ z j < 1 - δ}, |v x|) + 2 * ∫ x in {z : Euclid (m + 1) | ∀ j, δ < z j ∧ z j < 1 - δ}, ‖fderiv ℝ v x‖ := by
  intro m v g i δ hv hg hgb hδ0 hδ1
  set Q : Set (Euclid (m + 1)) := {z : Euclid (m + 1) | ∀ j, δ < z j ∧ z j < 1 - δ} with hQ
  set Q' : Set (Fin m → ℝ) := {y : Fin m → ℝ | ∀ j, δ < y j ∧ y j < 1 - δ} with hQ'
  have hab : δ < 1 - δ := by linarith
  -- the line `t ↦ ι t y` through the slice point `y` in direction `e_i`
  set ι : ℝ → (Fin m → ℝ) → Euclid (m + 1) := fun t y => WithLp.toLp 2 (Fin.insertNth i t y)
    with hι
  have hι_affine : ∀ t y, ι t y = ι 0 y + t • EuclideanSpace.single i 1 := by
    intro t y
    ext j
    induction j using Fin.succAboveCases i with
    | x => simp [ι]
    | p j => simp [ι, Fin.succAbove_ne]
  have hι_deriv : ∀ t y, HasDerivAt (fun s => ι s y) (EuclideanSpace.single i 1) t := by
    intro t y
    have : (fun s => ι s y) = fun s => ι 0 y + s • EuclideanSpace.single i (1 : ℝ) := by
      funext s; exact hι_affine s y
    rw [this]
    simpa using ((hasDerivAt_id t).smul_const (EuclideanSpace.single i (1 : ℝ))).const_add (ι 0 y)
  have hι_cd : ∀ y, ContDiff ℝ 1 (fun s => ι s y) := by
    intro y
    have : (fun s => ι s y) = fun s => ι 0 y + s • EuclideanSpace.single i (1 : ℝ) := by
      funext s; exact hι_affine s y
    rw [this]
    exact contDiff_const.add (contDiff_id.smul contDiff_const)
  have hvg : ContDiff ℝ 1 (fun y => v y * g y) := hv.mul hg
  set F : Euclid (m + 1) → ℝ := fun x => fderiv ℝ (fun y => v y * g y) x (EuclideanSpace.single i 1)
    with hF
  set H : Euclid (m + 1) → ℝ := fun x => 4 * |v x| + 2 * ‖fderiv ℝ v x‖ with hH
  have hFc : Continuous F := (hvg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hvc : Continuous fun x => |v x| := hv.continuous.abs
  have hDvc : Continuous fun x => ‖fderiv ℝ v x‖ := (hv.continuous_fderiv one_ne_zero).norm
  have hHc : Continuous H := (continuous_const.mul hvc).add (continuous_const.mul hDvc)
  obtain ⟨-, hFslice⟩ := Submission.cmcdt_cbm_st_slice_integral m i δ (1 - δ) F hab.le
    (Submission.cmcdt_cbm_st_box_integrableOn _ _ _ _ hFc)
  obtain ⟨hHint, hHslice⟩ := Submission.cmcdt_cbm_st_slice_integral m i δ (1 - δ) H hab.le
    (Submission.cmcdt_cbm_st_box_integrableOn _ _ _ _ hHc)
  have hHsplit : ∫ x in Q, H x = 4 * (∫ x in Q, |v x|) + 2 * ∫ x in Q, ‖fderiv ℝ v x‖ := by
    rw [integral_add ((Submission.cmcdt_cbm_st_box_integrableOn _ _ _ _ hvc).const_mul 4)
      ((Submission.cmcdt_cbm_st_box_integrableOn _ _ _ _ hDvc).const_mul 2),
      integral_const_mul, integral_const_mul]
  -- the one-dimensional estimate on each line
  have hline : ∀ y, |∫ t in δ..(1 - δ), F (ι t y)| ≤ ∫ t in δ..(1 - δ), H (ι t y) := by
    intro y
    have hφ : ContDiff ℝ 1 (fun s => v (ι s y)) := hv.comp (hι_cd y)
    have hγ : ContDiff ℝ 1 (fun s => g (ι s y)) := hg.comp (hι_cd y)
    have hderiv_prod : ∀ t, deriv (fun s => v (ι s y) * g (ι s y)) t = F (ι t y) := by
      intro t
      have := ((hvg.differentiable one_ne_zero (ι t y)).hasFDerivAt).comp_hasDerivAt t
        (hι_deriv t y)
      exact this.deriv
    have hderiv_v : ∀ t, deriv (fun s => v (ι s y)) t =
        fderiv ℝ v (ι t y) (EuclideanSpace.single i 1) := by
      intro t
      have := ((hv.differentiable one_ne_zero (ι t y)).hasFDerivAt).comp_hasDerivAt t
        (hι_deriv t y)
      exact this.deriv
    have h1 := Submission.cmcdt_cbm_st_interval_bound (fun s => v (ι s y)) (fun s => g (ι s y))
      δ (1 - δ) hφ hγ (fun t => hgb _) hab
    simp only [hderiv_prod, hderiv_v] at h1
    have hcoef : 2 / (1 - δ - δ) ≤ 4 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hint_nonneg : 0 ≤ ∫ t in δ..(1 - δ), |v (ι t y)| :=
      intervalIntegral.integral_nonneg hab.le fun t _ => abs_nonneg _
    have hcont_v : Continuous fun t => |v (ι t y)| := hφ.continuous.abs
    have hcont_Dv : Continuous fun t => ‖fderiv ℝ v (ι t y)‖ := hDvc.comp (hι_cd y).continuous
    have hcont_dv : Continuous fun t => |fderiv ℝ v (ι t y) (EuclideanSpace.single i 1)| :=
      (((hv.continuous_fderiv one_ne_zero).comp (hι_cd y).continuous).clm_apply
        continuous_const).abs
    have hmono : ∫ t in δ..(1 - δ), |fderiv ℝ v (ι t y) (EuclideanSpace.single i 1)| ≤
        ∫ t in δ..(1 - δ), ‖fderiv ℝ v (ι t y)‖ := by
      refine intervalIntegral.integral_mono_on hab.le (hcont_dv.intervalIntegrable _ _)
        (hcont_Dv.intervalIntegrable _ _) fun t _ => ?_
      have := (fderiv ℝ v (ι t y)).le_opNorm (EuclideanSpace.single i 1)
      rw [Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one] at this
      exact this
    have hHline : ∫ t in δ..(1 - δ), H (ι t y) =
        4 * (∫ t in δ..(1 - δ), |v (ι t y)|) + 2 * ∫ t in δ..(1 - δ), ‖fderiv ℝ v (ι t y)‖ := by
      simp only [H]
      rw [intervalIntegral.integral_add ((hcont_v.intervalIntegrable _ _).const_mul 4)
        ((hcont_Dv.intervalIntegrable _ _).const_mul 2), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    rw [hHline]
    calc |∫ t in δ..(1 - δ), F (ι t y)|
        ≤ 2 / (1 - δ - δ) * (∫ t in δ..(1 - δ), |v (ι t y)|) +
            2 * ∫ t in δ..(1 - δ), |fderiv ℝ v (ι t y) (EuclideanSpace.single i 1)| := h1
      _ ≤ 4 * (∫ t in δ..(1 - δ), |v (ι t y)|) + 2 * ∫ t in δ..(1 - δ), ‖fderiv ℝ v (ι t y)‖ := by
        gcongr
  calc |∫ x in Q, F x|
      = |∫ y in Q', ∫ t in δ..(1 - δ), F (ι t y)| := by rw [hFslice]
    _ ≤ ∫ y in Q', |∫ t in δ..(1 - δ), F (ι t y)| := abs_integral_le_integral_abs
    _ ≤ ∫ y in Q', ∫ t in δ..(1 - δ), H (ι t y) :=
        integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _) hHint
          (Eventually.of_forall hline)
    _ = ∫ x in Q, H x := hHslice.symm
    _ = 4 * (∫ x in Q, |v x|) + 2 * ∫ x in Q, ‖fderiv ℝ v x‖ := hHsplit
```

## Key steps

1. a := δ, b := 1 − δ: b − a = 1 − 2δ ≥ 1/2, so a < b and 2/(b − a) ≤ 4.
2. ι(t, y) = ι(0, y) + t e_i, so each coordinate line is affine with derivative e_i.
3. F := D(vg)(·)e_i and H := 4|v| + 2‖Dv‖ are continuous, hence integrable on Q_δ (box_integrable); ∫_Q H = 4∫|v| + 2∫‖Dv‖.
4. Slice F and H in coordinate i (slice_integral); the slice integral of H is integrable on Q'.
5. On each line, the chain rule gives (φγ)' = F∘ι and φ' = Dv(ι)e_i. Then interval_bound, 2/(b − a) ≤ 4 and |Dv(x)e_i| ≤ ‖Dv(x)‖ give |∫_a^b F∘ι| ≤ ∫_a^b H∘ι.
6. |∫_Q F| ≤ ∫_{Q'} |∫_a^b F∘ι| ≤ ∫_{Q'} ∫_a^b H∘ι = ∫_Q H = 4∫_Q|v| + 2∫_Q‖Dv‖.

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean against workspace GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); git -C <snapshot>/mathlib rev-parse HEAD = 25730c7c759d108ef87ab70af2342a196760f79d (matches manifest)`
- `rg -c 'cmcdt_cbm_st_' <snapshot> -g '*.lean' (no match); python3 scan of runs/20261011T150044Z-ba604216b4/dag.json lean_name/theorems fields for the five proposed names (no collision)`
- `rg -n 'theorem volume_preserving_piFinSuccAbove|theorem PiLp.volume_preserving_toLp|theorem integral_prod_symm|theorem MeasurePreserving.setIntegral_preimage_emb|theorem MeasurePreserving.integrableOn_comp_preimage|lemma trace_eq_sum_inner|theorem EuclideanSpace.inner_single_left|theorem norm_apply_le|theorem contDiff_piLp_apply|theorem integral_deriv_eq_sub|theorem integral_mono_interval|theorem norm_integral_le_abs_integral_norm|theorem Integrable.integral_prod_right|theorem forall_iff_succAbove|theorem basisFun_apply' <snapshot>/mathlib/Mathlib -g '*.lean'`
- `grep -n 'def piFinSuccAbove' <snapshot>/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`
- `rg -n 'piFinSuccAbove|insertNth|trace_eq_sum_inner|integral_divergence|integral_prod_symm|volume_preserving_toLp' <snapshot>/project -g '*.lean' (no match) and lake-packages-25730c7c/simongmt -g '*.lean' (only proof-internal uses; euclideanDivergence_eq_sum_inner in Chapter02/BV.lean is a wrapper of LinearMap.trace_eq_sum_inner)`
- `lake env lean /tmp/st-decomp-ch07/final/FromProofs.lean (copy of GMT/Ch07/Submission.lean + the five children + the parent; axioms propext, Classical.choice, Quot.sound); lake env lean /tmp/st-decomp-ch07/final/CompareSim.lean (comparator-style challenges via gmt-compare.py contract_scope); python3 -I verifier/lean_contract.py validate_lean_statement on all six types`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/WithLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-10b7629544/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/st-decomp-ch07/final/FromProofs.lean`
- `/tmp/st-decomp-ch07/final/CompareSim.lean`

Nothing in the snapshot can be reused for this node.
- The snapshot (project b4d606d, Mathlib 25730c7c) has the same contract as the workspace, and Submission.lean is byte-identical to Contract.lean.
- The project has no slicing, Fubini, trace or divergence lemma.
- SimonGMT only wraps LinearMap.trace_eq_sum_inner (euclideanDivergence_eq_sum_inner).

Mathlib 25730c7c supplies every tool used, all within the import closure of GMT.Ch07.Submission:
- volume_preserving_piFinSuccAbove and MeasurableEquiv.piFinSuccAbove;
- PiLp.volume_preserving_toLp;
- MeasurePreserving.setIntegral_preimage_emb and integrableOn_comp_preimage;
- Measure.prod_restrict, integral_prod_symm and Integrable.integral_prod_right;
- intervalIntegral.integral_deriv_eq_sub, integral_mono_interval and norm_integral_le_abs_integral_norm;
- LinearMap.trace_eq_sum_inner, EuclideanSpace.inner_single_left, PiLp.norm_apply_le and contDiff_piLp_apply;
- Fin.forall_iff_succAbove and Fin.succAboveCases.

The five child proofs and the parent assembly compile in a copy of Submission.lean with no extra imports, and #print axioms gives propext, Classical.choice and Quot.sound only. The proposed names cmcdt_cbm_st_* collide with nothing in the snapshot or the DAG.
