# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_trace-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_trace-a1.interval_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the one-dimensional core of steps 2–4 of the parent proof of `cmcdt_cbm_smooth_trace`, on a single coordinate line:
- the fundamental theorem of calculus of step 2 for the boundary term H_i = vG_i;
- the bound |H_i| ≤ |v||G| ≤ |v| of step 3;
- the face (trace) estimate of step 4: FTC along the segment between c and t, then averaging over t in a side of length s = b − a.
It is the elementary one-dimensional case of the trace estimate behind Simon, Ch. 2, 2.8–2.9 (book/chapter-02.txt lines 663–676). For background, the BV trace theory is in Evans–Gariepy, *Measure Theory and Fine Properties of Functions*, Ch. 5. The argument below is self-contained.

Statement. Let a < b and let φ, γ : ℝ → ℝ be C¹ (`ContDiff ℝ 1`) with |γ(t)| ≤ 1 for all t. Write f' := deriv f. All integrals are interval integrals ∫_a^b; since a < b these are ordinary integrals over (a, b]. Claim: |∫_a^b (φγ)'(t) dt| ≤ (2/(b − a)) ∫_a^b |φ| + 2 ∫_a^b |φ'|.

1. FTC for the product. φγ is C¹ as a product of C¹ functions. So it is differentiable everywhere, and its derivative (φγ)' is continuous, hence interval integrable on [a, b]. By the fundamental theorem of calculus (`intervalIntegral.integral_deriv_eq_sub`), ∫_a^b (φγ)' = φ(b)γ(b) − φ(a)γ(a).
2. Pointwise trace inequality. Put D := ∫_a^b |φ'|. Claim: for every c ∈ [a, b], |φ(c)| ≤ (b − a)⁻¹ ∫_a^b |φ| + D.
   2a. Fix t ∈ [a, b]. φ is differentiable with continuous derivative φ', so by FTC, φ(c) − φ(t) = ∫_t^c φ'. Also |∫_t^c φ'| ≤ |∫_t^c |φ'|| (`intervalIntegral.norm_integral_le_abs_integral_norm`). Next, |∫_t^c |φ'|| ≤ D:
       - If t ≤ c, then ∫_t^c |φ'| ≥ 0, and ∫_t^c |φ'| ≤ ∫_a^b |φ'| = D. This holds because a ≤ t ≤ c ≤ b, |φ'| ≥ 0, and |φ'| is continuous, hence interval integrable on [a, b] (`intervalIntegral.integral_mono_interval`).
       - If c < t, then ∫_t^c |φ'| = −∫_c^t |φ'| (`intervalIntegral.integral_symm`). The same argument with a ≤ c ≤ t ≤ b gives |∫_t^c |φ'|| = ∫_c^t |φ'| ≤ D.
       Hence |φ(c) − φ(t)| ≤ D, and |φ(c)| ≤ |φ(t)| + |φ(c) − φ(t)| ≤ |φ(t)| + D.
   2b. Average over t. Integrate the inequality of 2a over t ∈ [a, b]. Both sides are continuous in t, hence interval integrable, and a ≤ b (`intervalIntegral.integral_mono_on`). This gives (b − a)|φ(c)| = ∫_a^b |φ(c)| dt ≤ ∫_a^b (|φ(t)| + D) dt = ∫_a^b |φ| + (b − a)D.
   2c. Since b − a > 0, dividing gives |φ(c)| ≤ (b − a)⁻¹ ∫_a^b |φ| + D.
3. Conclusion. By step 1 and |γ(a)|, |γ(b)| ≤ 1:
   |∫_a^b (φγ)'| = |φ(b)γ(b) − φ(a)γ(a)| ≤ |φ(b)||γ(b)| + |φ(a)||γ(a)| ≤ |φ(b)| + |φ(a)|.
   Apply step 2 with c = b and with c = a (both lie in [a, b]) and add. This gives |φ(b)| + |φ(a)| ≤ 2(b − a)⁻¹ ∫_a^b |φ| + 2D = (2/(b − a)) ∫_a^b |φ| + 2 ∫_a^b |φ'|. ∎

Formalization notes. A scratch build checked the Lean proof below against exactly this frozen type. It used Lean v4.35.0-rc3 and Mathlib 25730c7c, with the declaration inserted into a copy of `GMT/Ch07/Submission.lean` after the contract's `noncomputable section … end` and before `main_theorem`, in namespace `GMT.Ch07` with the contract's `open`s. It needs no imports beyond the frozen header, and `#print axioms` lists only propext, Classical.choice and Quot.sound. API details for this Mathlib: `ContDiff.differentiable` and `ContDiff.continuous_fderiv` take `one_ne_zero`, and `ContDiff.continuous_deriv` takes `le_rfl`. The nested absolute value inside an integral needs parentheses: `|∫ s in t..c, (|deriv φ s|)|`.

```lean
theorem Submission.cmcdt_cbm_st_interval_bound : ∀ (φ γ : ℝ → ℝ) (a b : ℝ), ContDiff ℝ 1 φ → ContDiff ℝ 1 γ → (∀ t, |γ t| ≤ 1) → a < b → |∫ t in a..b, deriv (fun s => φ s * γ s) t| ≤ 2 / (b - a) * (∫ t in a..b, |φ t|) + 2 * ∫ t in a..b, |deriv φ t| := by
  intro φ γ a b hφ hγ hγb hab
  have hφd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hφ'c : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hpc : ContDiff ℝ 1 (fun s => φ s * γ s) := hφ.mul hγ
  -- fundamental theorem of calculus for the product
  have hftc : ∫ t in a..b, deriv (fun s => φ s * γ s) t = φ b * γ b - φ a * γ a :=
    intervalIntegral.integral_deriv_eq_sub (fun t _ => (hpc.differentiable one_ne_zero) t)
      ((hpc.continuous_deriv le_rfl).intervalIntegrable _ _)
  -- the one-dimensional trace inequality at a point `c ∈ [a, b]`
  have htrace : ∀ c ∈ Icc a b,
      |φ c| ≤ (b - a)⁻¹ * (∫ t in a..b, |φ t|) + ∫ t in a..b, |deriv φ t| := by
    intro c hc
    set D := ∫ t in a..b, |deriv φ t| with hD
    have hpt : ∀ t ∈ Icc a b, |φ c| ≤ |φ t| + D := by
      intro t ht
      have hsub : φ c - φ t = ∫ s in t..c, deriv φ s :=
        (intervalIntegral.integral_deriv_eq_sub (fun s _ => hφd s)
          (hφ'c.intervalIntegrable _ _)).symm
      have hle : |∫ s in t..c, deriv φ s| ≤ D := by
        have habs : |∫ s in t..c, deriv φ s| ≤ |∫ s in t..c, (|deriv φ s|)| := by
          simpa only [Real.norm_eq_abs] using
            (intervalIntegral.norm_integral_le_abs_integral_norm (f := deriv φ) (a := t) (b := c)
              (μ := volume))
        refine habs.trans ?_
        rcases le_total t c with htc | hct
        · rw [abs_of_nonneg (intervalIntegral.integral_nonneg htc fun s _ => abs_nonneg _)]
          exact intervalIntegral.integral_mono_interval ht.1 htc hc.2
            (Eventually.of_forall fun s => abs_nonneg _) (hφ'c.abs.intervalIntegrable _ _)
        · rw [intervalIntegral.integral_symm, abs_neg,
            abs_of_nonneg (intervalIntegral.integral_nonneg hct fun s _ => abs_nonneg _)]
          exact intervalIntegral.integral_mono_interval hc.1 hct ht.2
            (Eventually.of_forall fun s => abs_nonneg _) (hφ'c.abs.intervalIntegrable _ _)
      calc |φ c| = |φ t + (φ c - φ t)| := by ring_nf
        _ ≤ |φ t| + |φ c - φ t| := abs_add_le _ _
        _ ≤ |φ t| + D := by rw [hsub]; gcongr
    have hint : ∫ t in a..b, |φ c| ≤ ∫ t in a..b, (|φ t| + D) :=
      intervalIntegral.integral_mono_on hab.le intervalIntegrable_const
        ((hφd.continuous.abs.add continuous_const).intervalIntegrable _ _) hpt
    rw [intervalIntegral.integral_const, intervalIntegral.integral_add
      (hφd.continuous.abs.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul] at hint
    have hba : 0 < b - a := sub_pos.mpr hab
    rw [inv_mul_eq_div, ← sub_le_iff_le_add, le_div_iff₀ hba]
    nlinarith
  have hA := htrace a ⟨le_rfl, hab.le⟩
  have hB := htrace b ⟨hab.le, le_rfl⟩
  rw [hftc]
  have hγa := hγb a
  have hγb' := hγb b
  calc |φ b * γ b - φ a * γ a| ≤ |φ b * γ b| + |φ a * γ a| := abs_sub _ _
    _ = |φ b| * |γ b| + |φ a| * |γ a| := by rw [abs_mul, abs_mul]
    _ ≤ |φ b| * 1 + |φ a| * 1 := by gcongr
    _ = |φ b| + |φ a| := by ring
    _ ≤ 2 / (b - a) * (∫ t in a..b, |φ t|) + 2 * ∫ t in a..b, |deriv φ t| := by
        have : 2 / (b - a) = (b - a)⁻¹ + (b - a)⁻¹ := by ring
        rw [this]; linarith
```

## Key steps

1. FTC: ∫_a^b (φγ)' = φ(b)γ(b) − φ(a)γ(a).
2. For c, t ∈ [a, b]: |φ(c)| ≤ |φ(t)| + ∫_a^b |φ'|, from FTC on the segment between t and c and monotonicity of the integral of |φ'| ≥ 0 in the interval.
3. Average over t ∈ [a, b] and divide by b − a > 0: |φ(c)| ≤ (b − a)⁻¹ ∫_a^b |φ| + ∫_a^b |φ'|.
4. |φ(b)γ(b) − φ(a)γ(a)| ≤ |φ(b)| + |φ(a)|; apply the pointwise bound at c = b and c = a and add.

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
