# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1.density_estimates-a1.sobolev_indicator-a1.mollified_fderiv_le-a1`
- Child DAG node: `root.de_giorgi-a1.density_estimates-a1.sobolev_indicator-a1.mollified_fderiv_le-a1.fubini_swap-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the last step of the implementation note of the parent proof ("Tonelli's theorem for the non-negative continuous integrand (y, z) ↦ ζ(y)ρ(y − z), which vanishes unless (y, z) ∈ T × K' and may therefore be integrated against the finite measures L^N restricted to T and μ restricted to K'"), together with Step 0 of the parent proof (ζ̃(z) := ∫ζ(y)ρ(y − z)dy vanishes off K'). In the proof of Simon Ch. 2, Lemma 2.5 (chapter-02.txt lines 543-596), this is the step that turns the pointwise bound into the integrated bound by a mollified test function. No sign conditions are needed here: Fubini's theorem for integrable functions is used instead of Tonelli. Since μ is not assumed s-finite, Fubini is applied to the finite measure μ' := μ⌞K'. Notation: T := tsupport ζ (compact) and F(y, z) := ζ(y)ρ(y − z). Lean's Bochner integral is 0 for non-integrable functions; the manipulations in steps 5-6 (pulling out a constant factor, restricting to a set off which the integrand vanishes) hold without any integrability.

1. (Vanishing.) Let y, z ∈ ℝ^N with F(y, z) ≠ 0. Then ζ(y) ≠ 0, so y ∈ T. Also ρ(y − z) ≠ 0, so y − z ∈ tsupport ρ ⊆ B̄_r(0), i.e. dist(z, y) = |y − z| ≤ r. Hence z ∈ cthickening(r, T) = K' (Metric.mem_cthickening_of_dist_le). Contrapositively, F(y, z) = 0 whenever z ∉ K', and also whenever y ∉ T.

2. (The finite measure μ'.) μ' := μ⌞K' satisfies μ'(ℝ^N) = μ(K') < ∞, so μ' is a finite, hence s-finite, measure (isFiniteMeasure_restrict). Lebesgue measure L^N on ℝ^N is σ-finite.

3. (Integrability of F on the product.) F is continuous on ℝ^N × ℝ^N, as the product of ζ ∘ pr₁ and ρ ∘ (pr₁ − pr₂), hence a.e.-strongly measurable for L^N ⊗ μ'. Continuous functions with compact support are bounded, say |ζ| ≤ M_ζ and |ρ| ≤ M_ρ; then |F| ≤ M_ζ M_ρ everywhere. By step 1 the support of F lies in T × ℝ^N. That set has (L^N ⊗ μ')-measure L^N(T)·μ'(ℝ^N) < ∞ (Measure.prod_prod; T is compact, so L^N(T) < ∞). A bounded a.e.-strongly measurable function is integrable on a set of finite measure (Measure.integrableOn_of_bounded). As the support of F is contained in T × ℝ^N, F is L^N ⊗ μ'-integrable (integrableOn_iff_integrable_of_support_subset).

4. (Fubini.) By step 3, Fubini's theorem (integral_integral_swap) gives ∫(∫ F(y, z) dμ'(z)) dL^N(y) = ∫(∫ F(y, z) dL^N(y)) dμ'(z). Moreover y ↦ ∫ F(y, z) dμ'(z) is L^N-integrable (Integrable.integral_prod_left).

5. (Inner integrals.) For each y, F(y, ·) vanishes off K' by step 1. So ∫ F(y, z) dμ'(z) = ∫_{K'} F(y, z) dμ(z) = ∫ F(y, z) dμ(z) (setIntegral_eq_integral_of_forall_compl_eq_zero). This equals ζ(y)∫ρ(y − z) dμ(z) (constant factor; integral_const_mul).

6. (Outer integral.) For z ∉ K', F(·, z) ≡ 0 by step 1, so H(z) := ∫ F(y, z) dL^N(y) = 0. Hence ∫ H dμ' = ∫_{K'} H dμ = ∫ H dμ (setIntegral_eq_integral_of_forall_compl_eq_zero).

7. (Conclusion.) By steps 4 and 5, y ↦ ζ(y)∫ρ(y − z)dμ(z) coincides everywhere with the L^N-integrable function y ↦ ∫F(y, z)dμ'(z), so it is L^N-integrable (Integrable.congr). By steps 4-6, ∫ζ(y)(∫ρ(y − z)dμ(z))dy = ∫(∫F(y, z)dμ'(z))dy = ∫ H dμ' = ∫ H dμ = ∫(∫ζ(y)ρ(y − z)dy)dμ(z). ∎

Appendix (non-binding; the numbered proof above is the contract). Kernel-checked Lean proof of exactly this frozen type, compiled during decomposition after `import GMT.Ch03.Submission` in the comparator scope (namespace GMT.Ch03 with the contract's `open` commands), in the placement `theorem Submission.X` used by accepted leaves; Lean v4.35.0-rc3, Mathlib 25730c7c; axioms: propext, Classical.choice, Quot.sound.
```lean
theorem Submission.deGiorgiSobIndMFL_integral_mul_swap : ∀ (N : ℕ) (μ : Measure (Rn N)) (ζ ρ : Rn N → ℝ) (r : ℝ), Continuous ζ → HasCompactSupport ζ → Continuous ρ → HasCompactSupport ρ → tsupport ρ ⊆ Metric.closedBall (0 : Rn N) r → μ (Metric.cthickening r (tsupport ζ)) < ∞ → Integrable (fun y ↦ ζ y * (∫ z, ρ (y - z) ∂μ)) ∧ ∫ y, ζ y * (∫ z, ρ (y - z) ∂μ) = ∫ z, (∫ y, ζ y * ρ (y - z)) ∂μ := by
  intro N μ ζ ρ r hζ hζc hρ hρc hρr hfin
  have : IsFiniteMeasure (μ.restrict (Metric.cthickening r (tsupport ζ))) :=
    isFiniteMeasure_restrict.2 hfin.ne
  -- the integrand vanishes unless `z` lies in the thickening `K'`
  have hvan : ∀ y z, z ∉ Metric.cthickening r (tsupport ζ) → ζ y * ρ (y - z) = 0 := by
    intro y z hz
    by_contra hne
    have hy : y ∈ tsupport ζ := subset_tsupport _ (left_ne_zero_of_mul hne)
    have h2 := hρr (subset_tsupport _ (right_ne_zero_of_mul hne))
    rw [Metric.mem_closedBall, dist_zero_right] at h2
    exact hz (Metric.mem_cthickening_of_dist_le z y r _ hy
      (by rw [dist_eq_norm, norm_sub_rev]; exact h2))
  have hFc : Continuous (Function.uncurry fun y z : Rn N ↦ ζ y * ρ (y - z)) :=
    (hζ.comp continuous_fst).mul (hρ.comp (continuous_fst.sub continuous_snd))
  obtain ⟨Mζ, hMζ⟩ := hζ.bounded_above_of_compact_support hζc
  obtain ⟨Mρ, hMρ⟩ := hρ.bounded_above_of_compact_support hρc
  have hFint : Integrable (Function.uncurry fun y z : Rn N ↦ ζ y * ρ (y - z))
      ((volume : Measure (Rn N)).prod (μ.restrict (Metric.cthickening r (tsupport ζ)))) := by
    have hsupp : Function.support (Function.uncurry fun y z : Rn N ↦ ζ y * ρ (y - z)) ⊆
        tsupport ζ ×ˢ univ := fun p hp ↦ ⟨subset_tsupport _ (left_ne_zero_of_mul hp), trivial⟩
    refine (integrableOn_iff_integrable_of_support_subset hsupp).1 ?_
    refine Measure.integrableOn_of_bounded ?_ hFc.aestronglyMeasurable (M := Mζ * Mρ)
      (Eventually.of_forall fun p ↦ ?_)
    · rw [Measure.prod_prod]
      exact ENNReal.mul_ne_top hζc.isCompact.measure_lt_top.ne (measure_ne_top _ _)
    · simp only [Function.uncurry, norm_mul]
      exact mul_le_mul (hMζ _) (hMρ _) (norm_nonneg _) ((norm_nonneg _).trans (hMζ p.1))
  have hin : ∀ y, ∫ z in Metric.cthickening r (tsupport ζ), ζ y * ρ (y - z) ∂μ =
      ζ y * ∫ z, ρ (y - z) ∂μ := by
    intro y
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz ↦ hvan y z hz), integral_const_mul]
  have hout : ∫ z in Metric.cthickening r (tsupport ζ), (∫ y, ζ y * ρ (y - z)) ∂μ =
      ∫ z, (∫ y, ζ y * ρ (y - z)) ∂μ := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ ?_
    simp [hvan _ z hz]
  refine ⟨?_, ?_⟩
  · exact hFint.integral_prod_left.congr (Eventually.of_forall fun y ↦ hin y)
  · rw [← hout, ← integral_integral_swap hFint]
    exact integral_congr_ae (Eventually.of_forall fun y ↦ (hin y).symm)
```

## Key steps

1. F(y, z) := ζ(y)ρ(y − z) vanishes unless y ∈ tsupport ζ and z ∈ K' = cthickening(r, tsupport ζ).
2. μ' := μ⌞K' is finite; F is continuous, bounded and supported in tsupport ζ × ℝ^N, a set of finite L^N ⊗ μ' measure, so F is integrable.
3. Fubini (integral_integral_swap) for L^N and μ', with integrability of y ↦ ∫F(y, z)dμ'(z) (Integrable.integral_prod_left).
4. Replace μ' by μ in the inner and outer integrals (the integrands vanish off K') and pull out ζ(y).

## Reference use

### local-project

Queries:
- `python3 -I -c 'json.load(open("<snapshot>/manifest.json"))'; cmp <snapshot>/project/GMT/Ch03/Contract.lean GMT/Ch03/Contract.lean; cmp <snapshot>/project/GMT/Ch03/Submission.lean GMT/Ch03/Submission.lean`
- `grep -n 'theorem hasFDerivAt_integral_of_dominated_of_fderiv_le' <snapshot>/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `grep -rn 'trace_smulRight' <snapshot>/mathlib/Mathlib/LinearAlgebra`
- `grep -rn 'theorem integral_integral_swap\b\|theorem Integrable.integral_prod_left' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `grep -n 'theorem setIntegral_indicator\b\|theorem setIntegral_eq_integral_of_forall_compl_eq_zero\|theorem norm_integral_le_of_norm_le' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `grep -n 'theorem closedBall_subset_cthickening\b\|theorem mem_cthickening_of_dist_le\|IsCompact.cthickening' <snapshot>/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `grep -rn 'theorem fderiv_of_notMem_tsupport\|theorem HasCompactSupport.fderiv\b' <snapshot>/mathlib/Mathlib/Analysis/Calculus/FDeriv/*.lean`
- `grep -rn 'theorem integral_apply' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `rg -n 'hasFDerivAt_integral_of_dominated|trace_smulRight|euclideanDivergence .*smul|fderiv_convolution_eq_zero' .lake/packages/simongmt/Poincare`
- `rg -n 'IsGaussGreenPair' <snapshot>/project/GMT; rg -n -i 'mollif|smulRight|integral_integral_swap' <snapshot>/project/GMT`
- `rg -n 'deGiorgiSobIndMFL' <snapshot>/project .lake/packages/simongmt/Poincare dag.json GMT/Ch03; python3 -I lean_name collision check over dag.json`
- `python3 -I over dag.json: lean_name/status list and statements of related nodes (deGiorgiDens_lipschitz_gaussGreen, indCompact_mollCauchy_setIntegral_continuous, deGiorgiSobInd_* siblings, gaussGreenRep_pairing_eq_continuous, deGiorgiTM_integral_bound_of_ball, indCompact_transEst_abs_setIntegral_fderiv_le)`
- `sed -n 520,600p book/chapter-02.txt; sed -n 680,710p book/chapter-03.txt (Simon Ch. 2 Lemma 2.5 and its use in Ch. 3 §4)`
- `lake env lean GMT/Scratch/MFLNameCheck.lean (#check of every Mathlib lemma cited in the child proofs)`
- `lake env lean GMT/Scratch/MFLSplitAssembly.lean (#print axioms deGiorgiSobInd_mollified_fderiv_le from the exact child stubs)`
- `python3 -I /tmp/mfl/scripts/gen_challenges.py (verifier gmt-compare.py child_modules, contract mode) then lake env lean on each generated NodeChallenge module`
- `lake env lean GMT/Scratch/MFLFinalLeafCheck.lean; lake env lean GMT/Scratch/MFLAppendixCheck.lean (kernel-checked children and parent in the theorem Submission.X placement; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/ConstancyFullDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1-sobolev-indicator-a1-mollified-3df7147d0f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/MFLNameCheck.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/MFLSplitAssembly.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/MFLFullCheck.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/MFLFinalLeafCheck.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/MFLAppendixCheck.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/MFLChildDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/MFLChildGG.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/MFLChildBound.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/MFLChildSwap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/MFLReviewImplication.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/MFLReviewSubFormat.lean`

The snapshot (project d09bc8a1, Mathlib 25730c7c) has Contract.lean and Submission.lean byte-identical to the workspace; Submission is still the contract.

No library or project lemma already states the selected estimate or any of the four children:
- IsGaussGreenPair occurs only in the contract, Submission and README.
- rg for mollif|smulRight|integral_integral_swap in the snapshot project returns no match.
- The four new deGiorgiSobIndMFL_* names occur nowhere in the project, simongmt or dag.json.

Every Mathlib ingredient the child proofs use is present at the pinned revision and inside the contract's import closure:
- hasFDerivAt_integral_of_dominated_of_fderiv_le (ParametricIntegral.lean:208)
- LinearMap.trace_smulRight (Trace.lean:272)
- integral_integral_swap and Integrable.integral_prod_left (Prod.lean:478, 331)
- setIntegral_indicator and setIntegral_eq_integral_of_forall_compl_eq_zero (Bochner/Set.lean:194, 486)
- norm_integral_le_of_norm_le (Bochner/Basic.lean:985)
- Metric.closedBall_subset_cthickening, Metric.mem_cthickening_of_dist_le, IsCompact.cthickening (Thickening.lean:537, 201, 283)
- fderiv_of_notMem_tsupport and HasCompactSupport.fderiv (FDeriv/Const.lean:375, 389)
- ContinuousLinearMap.integral_apply (Bochner/ContinuousLinearMap.lean:73)

SimonGMT relevance:
- Chapter02/BV.lean defines euclideanDivergence as the trace of fderiv, with euclideanDivergence_eq_sum_inner.
- SimonGMT's divergence computations (Chapter04/FirstVariation.lean, Chapter08/ConstancyFullDimension.lean and others) use the same LinearMap.trace_smulRight step as kernel_gauss_green.
- Chapter08/DistributionalConstancy.lean has WeakDerivativesZero.fderiv_convolution_eq_zero, a pattern for differentiating a convolution. It is not needed, because fderiv_setintegral differentiates under the integral sign directly.

DAG reuse:
- deGiorgiDens_lipschitz_gaussGreen is in another subtree, covers the Lipschitz scalar case, and is not accepted, so it is not reused.
- indCompact_mollCauchy_setIntegral_continuous is accepted but not needed on this route.

Lean evidence:
- The four frozen strings elaborate in the verifier-generated comparator challenges.
- The exact parent type compiles from the exact child stubs.
- All four children and the parent compile with full proofs and only propext, Classical.choice and Quot.sound.
- An independent reviewer reproduced these checks and the implications.

A whole-tree rg over the snapshot's Mathlib timed out after 2 minutes, so targeted per-file greps were used instead.
