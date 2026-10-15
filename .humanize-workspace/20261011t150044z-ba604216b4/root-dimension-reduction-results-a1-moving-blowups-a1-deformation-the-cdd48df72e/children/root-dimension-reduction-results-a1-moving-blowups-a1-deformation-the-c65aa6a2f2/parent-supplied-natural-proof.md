# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_trace-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_trace-a1.interval_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the one-dimensional core of steps 2–4 of the supplied proof of `dimred_mbl_dt_cbm_smooth_trace`, on a single coordinate line:
- the fundamental theorem of calculus of step 2 for the boundary term H_i = vG_i;
- the bound |H_i| ≤ |v||G| ≤ |v| of step 3;
- the face (trace) estimate of step 4: FTC along the segment between c and t, then averaging over t in a side of length s = b − a.
It is the elementary one-dimensional case of the trace estimate behind Simon, Ch. 2, 2.8–2.9 (book/chapter-02.txt lines 663–676). The argument below is self-contained.

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

Formalization notes. The Lean proof below was re-compiled in this decomposition session against exactly the frozen type above (Lean v4.35.0-rc3, Mathlib 25730c7c, project commit b4d606db with GMT/Ch07/Submission.lean byte-identical to the frozen Contract). It compiled (a) in a scratch file `import GMT.Ch07.Submission` followed by the contract scope (`open Filter Function Set MeasureTheory Metric`, `open scoped ENNReal Topology`, `namespace GMT.Ch07`, `open Poincare.SimonGMT.Chapter06`, `open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt)`), and (b) inserted into a copy of GMT/Ch07/Submission.lean immediately before `main_theorem`, after the contract's `noncomputable section ... end`. It needs no imports beyond the frozen header, and `#print axioms` lists only propext, Classical.choice and Quot.sound. The comparator form `theorem _root_.HumanizeNodeComparator.target : (<frozen type>) := by exact Submission.dimred_mbl_dt_cbm_st_interval_bound` elaborates in the replayed contract scope. API details for this Mathlib: `ContDiff.differentiable` and `ContDiff.continuous_fderiv` take `one_ne_zero`, and `ContDiff.continuous_deriv` takes `le_rfl`. The nested absolute value inside an integral needs parentheses: `|∫ s in t..c, (|deriv φ s|)|`.

```lean
theorem Submission.dimred_mbl_dt_cbm_st_interval_bound : ∀ (φ γ : ℝ → ℝ) (a b : ℝ), ContDiff ℝ 1 φ → ContDiff ℝ 1 γ → (∀ t, |γ t| ≤ 1) → a < b → |∫ t in a..b, deriv (fun s => φ s * γ s) t| ≤ 2 / (b - a) * (∫ t in a..b, |φ t|) + 2 * ∫ t in a..b, |deriv φ t| := by
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
- `cat SNAPSHOT/manifest.json (project_commit b4d606db1da5…, mathlib_commit 25730c7c759d…); git rev-parse HEAD (b4d606db1da5…); cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean (identical)`
- `rg -n 'theorem volume_preserving_piFinSuccAbove|theorem PiLp.volume_preserving_toLp|theorem integral_prod_symm|theorem Integrable.integral_prod_right|theorem ContinuousOn.integrableOn_compact|theorem prod_restrict|theorem integral_deriv_eq_sub|theorem integral_mono_interval|theorem norm_integral_le_abs_integral_norm|lemma trace_eq_sum_inner|theorem contDiff_piLp_apply|theorem norm_apply_le' SNAPSHOT/mathlib/Mathlib -g '*.lean' (all found: Constructions/Pi.lean:818, Measure/Haar/InnerProductSpace.lean:139, Integral/Prod.lean:338,463, Function/LocallyIntegrable.lean:592, Measure/Prod.lean:778, IntervalIntegral/FundThmCalculus.lean:1176, IntervalIntegral/Basic.lean:743,1405, InnerProductSpace/Trace.lean:25, Calculus/ContDiff/WithLp.lean:83, Normed/Lp/PiLp.lean:713)`
- `rg -n 'abs_integral_le_integral_abs' SNAPSHOT/mathlib/Mathlib (Integral/Bochner/Basic.lean:982); rg -n 'theorem integral_divergence_of_hasFDerivAt_off_countable' (Integral/DivergenceTheorem.lean:266, outside the Submission import closure, not needed by the coordinatewise route)`
- `rg -n -i 'piFinSuccAbove|insertNth|trace_eq_sum_inner|integral_divergence|divergence|trace inequality|BVExtension' SNAPSHOT/project -g '*.lean' (only tangentialDivergence definitions and the unproved Ch02 Props BVExtensionEstimate/BVPoincare; no box divergence theorem or trace inequality)`
- `rg -n 'def euclideanDivergence|theorem .*divergence|piFinSuccAbove|insertNth' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/{BV,SubmanifoldCalculus}.lean (euclideanDivergence, euclideanDivergence_eq_sum_inner only; no trace or Fubini-slicing lemma)`
- `python3 -I scan of RUN/dag.json: twin node cmcdt_cbm_smooth_trace (identical lean_statement, waiting-children) with unaccepted children cmcdt_cbm_st_{box_integrableOn,slice_integral,interval_bound,coord_bound,div_product}; grep -c dimred_mbl_dt_cbm_st dag.json = 0; /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py _existing_lean_name_problem and max_depth logic (depth 5 < 6)`
- `lake env lean /tmp/dimred-st-split/All.lean, /tmp/dimred-st-split/SubmissionCopy.lean, /tmp/dimred-st-split/SolutionCombined.lean and /tmp/dimred-st-split/chal/*_NodeChallenge.lean (generated by verifier/gmt-compare.py child_modules); verifier/lean_contract.py validate_lean_statement on all six types`
- `sed -n 655,680p book/chapter-02.txt (Simon Ch. 2, 2.8–2.9)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/WithLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-10b7629544/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-10b7629544/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-cdd48df72e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/dimred-st-split/All.lean`
- `/tmp/dimred-st-split/SubmissionCopy.lean`
- `/tmp/dimred-st-split/SolutionCombined.lean`

The pins match (project b4d606db, Mathlib 25730c7c), and Submission.lean is byte-identical to the frozen contract. Neither the snapshot project nor SimonGMT contains a box divergence theorem, coordinate-slicing lemma or trace inequality. SimonGMT has only euclideanDivergence and its basis-sum formula, and the Ch02 BVExtensionEstimate is an unproved Prop. All Mathlib ingredients exist at the pinned revision inside the bare Submission import closure: volume_preserving_piFinSuccAbove, PiLp.volume_preserving_toLp, integral_prod_symm, Integrable.integral_prod_right, Measure.prod_restrict, ContinuousOn.integrableOn_compact, intervalIntegral FTC and monotonicity, LinearMap.trace_eq_sum_inner, PiLp.norm_apply_le and abs_integral_le_integral_abs. The five child types are byte-identical to the audited, accepted split of the twin cmcdt_cbm_smooth_trace. Those twin children are unaccepted and owned by another parent, so the fresh names dimred_mbl_dt_cbm_st_* are used; they collide with nothing. In this session all five child proofs and the parent assembly compiled with the exact frozen types and only standard axioms. The comparator challenges elaborate, and both statement validators accept the types.
