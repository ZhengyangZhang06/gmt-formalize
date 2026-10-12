# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1.density_estimates-a1.sobolev_indicator-a1.mollified_fderiv_le-a1`
- Child DAG node: `root.de_giorgi-a1.density_estimates-a1.sobolev_indicator-a1.mollified_fderiv_le-a1.fderiv_setintegral-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 1 ("u is C¹; Du(x)k = ∫_G Dρ(x − z)k dz", by differentiation under the integral sign). This is the differentiability of the mollified function u_σ = φ_σ ⋆ ũ used throughout Simon Ch. 2, §2 (mollification paragraph and Lemma 2.5, chapter-02.txt lines 530-596), with χ_G in place of u and a general C¹ kernel ρ in place of φ_σ. Here the differentiation under the integral sign is carried out directly for the measure λ := L^N⌞G (Lebesgue measure restricted to G), which avoids the change of variables to the convolution ρ ⋆ χ_G. Notation: |·| is the Euclidean norm, ‖·‖ the operator norm, B_s(a) and B̄_s(a) the open and closed balls, Dv(t) = fderiv ℝ v t.

1. (Bounds on ρ and Dρ.) Since ρ is C¹, it is differentiable everywhere and Dρ : ℝ^N → L(ℝ^N, ℝ) is continuous (ContDiff.differentiable, ContDiff.continuous_fderiv, both with 1 ≠ 0). The derivative vanishes off the topological support of ρ (fderiv_of_notMem_tsupport), so Dρ has compact support (HasCompactSupport.fderiv). Being continuous with compact support, Dρ is bounded: there is C with ‖Dρ(t)‖ ≤ C for all t (Continuous.bounded_above_of_compact_support). Since tsupport ρ is compact, it is bounded, so there is R with tsupport ρ ⊆ B̄_R(0).

2. (Translates and reflections.) For each fixed a ∈ ℝ^N the map z ↦ a − z is a homeomorphism of ℝ^N (Homeomorph.subLeft a), so z ↦ ρ(a − z) and z ↦ Dρ(a − z) are continuous with compact support (HasCompactSupport.comp_homeomorph). Hence they are L^N-integrable (Continuous.integrable_of_hasCompactSupport) and therefore integrable on G, i.e. λ-integrable (Integrable.integrableOn). Continuous functions are strongly measurable, so they are a.e.-strongly measurable for every measure, in particular for λ.

3. (Pointwise derivative of the integrand.) For fixed z, the map x ↦ ρ(x − z) is ρ composed with x ↦ x − z, whose derivative is the identity (HasFDerivAt.sub_const); by the chain rule it has derivative Dρ(x − z) at every x.

4. (Domination.) Fix x₀ ∈ ℝ^N and let s := B_1(x₀), a neighbourhood of x₀. Define b(z) := C if z ∈ B̄_{R+1}(x₀) and b(z) := 0 otherwise. Claim: ‖Dρ(x − z)‖ ≤ b(z) for all z ∈ ℝ^N and all x ∈ s. If z ∈ B̄_{R+1}(x₀) this is step 1. If z ∉ B̄_{R+1}(x₀), then x − z ∉ tsupport ρ: otherwise |x − z| ≤ R, and |z − x₀| ≤ |z − x| + |x − x₀| < R + 1 (as |x − x₀| < 1), contradicting z ∉ B̄_{R+1}(x₀); hence Dρ(x − z) = 0 (fderiv_of_notMem_tsupport) and the claim holds. The function b is C times the indicator of the compact set B̄_{R+1}(x₀), which has finite Lebesgue measure, so b is L^N-integrable (integrable_indicator_iff, integrableOn_const) and hence λ-integrable.

5. (Differentiation under the integral sign.) Apply the dominated differentiation theorem (Mathlib hasFDerivAt_integral_of_dominated_of_fderiv_le) with the measure λ, the neighbourhood s, F(x, z) := ρ(x − z), F'(x, z) := Dρ(x − z) and the bound b. Its hypotheses hold by steps 2-4: F(x, ·) is a.e.-strongly measurable for every x; F(x₀, ·) is λ-integrable; F'(x₀, ·) is a.e.-strongly measurable; ‖F'(x, z)‖ ≤ b(z) for every z and every x ∈ s; b is λ-integrable; and for every z and every x ∈ s, x ↦ F(x, z) has derivative F'(x, z) at x. Therefore u(x) = ∫ F(x, z) dλ(z) has at x₀ the derivative L := ∫_G Dρ(x₀ − z) dz, a Bochner integral in the Banach space L(ℝ^N, ℝ); thus Du(x₀) = L (HasFDerivAt.fderiv).

6. (Evaluation at w.) Evaluation at w is a continuous linear map L(ℝ^N, ℝ) → ℝ, and z ↦ Dρ(x₀ − z) is λ-integrable by step 2, so evaluation commutes with the integral (ContinuousLinearMap.integral_apply): Du(x₀)w = (∫_G Dρ(x₀ − z) dz)w = ∫_G Dρ(x₀ − z)w dz. Since x₀ and w were arbitrary, this proves the claim. ∎

Remark. The null-measurability of G is not used: λ = L^N⌞G is a measure for every set G. The hypothesis is kept so that the convolution route of the parent proof (integral_indicator₀ plus HasCompactSupport.hasFDerivAt_convolution_left) remains available.

Appendix (non-binding; the numbered proof above is the contract). Kernel-checked Lean proof of exactly this frozen type, compiled during decomposition after `import GMT.Ch03.Submission` in the comparator scope (namespace GMT.Ch03 with the contract's `open` commands), in the placement `theorem Submission.X` used by accepted leaves; Lean v4.35.0-rc3, Mathlib 25730c7c; axioms: propext, Classical.choice, Quot.sound.
```lean
theorem Submission.deGiorgiSobIndMFL_fderiv_setIntegral_apply : ∀ (N : ℕ) (G : Set (Rn N)) (ρ : Rn N → ℝ), NullMeasurableSet G volume → ContDiff ℝ 1 ρ → HasCompactSupport ρ → ∀ x w : Rn N, fderiv ℝ (fun x ↦ ∫ z in G, ρ (x - z)) x w = ∫ z in G, fderiv ℝ ρ (x - z) w := by
  intro N G ρ hG hρ hρc x₀ w
  have hρd : Differentiable ℝ ρ := hρ.differentiable one_ne_zero
  have hρ'c : Continuous (fderiv ℝ ρ) := hρ.continuous_fderiv one_ne_zero
  have hρ'cs : HasCompactSupport (fderiv ℝ ρ) := hρc.fderiv ℝ
  obtain ⟨C, hC⟩ := hρ'c.bounded_above_of_compact_support hρ'cs
  obtain ⟨R, hR⟩ : ∃ R, tsupport ρ ⊆ Metric.closedBall (0 : Rn N) R :=
    hρc.isCompact.isBounded.subset_closedBall 0
  -- translates and reflections of compactly supported functions
  have hrefl : ∀ {E : Type} [NormedAddCommGroup E] (f : Rn N → E) (x : Rn N),
      HasCompactSupport f → HasCompactSupport (fun z ↦ f (x - z)) := by
    intro E _ f x hf
    have : (fun z ↦ f (x - z)) = f ∘ (Homeomorph.subLeft x) := rfl
    rw [this]
    exact hf.comp_homeomorph _
  have hkey : HasFDerivAt (fun x ↦ ∫ z in G, ρ (x - z)) (∫ z in G, fderiv ℝ ρ (x₀ - z)) x₀ := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Metric.ball x₀ 1)
      (bound := (Metric.closedBall x₀ (R + 1)).indicator (fun _ ↦ C))
      (F' := fun x z ↦ fderiv ℝ ρ (x - z)) (Metric.ball_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun x ↦
        (hρ.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    · exact ((hρ.continuous.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
        (hrefl ρ x₀ hρc)).integrableOn
    · exact (hρ'c.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    · refine Eventually.of_forall fun z x hx ↦ ?_
      by_cases hz : z ∈ Metric.closedBall x₀ (R + 1)
      · simpa [hz] using hC (x - z)
      · have hxz : x - z ∉ tsupport ρ := by
          intro h
          apply hz
          have h2 := hR h
          rw [Metric.mem_closedBall, dist_zero_right] at h2
          rw [Metric.mem_ball] at hx
          rw [Metric.mem_closedBall]
          calc dist z x₀ ≤ dist z x + dist x x₀ := dist_triangle _ _ _
            _ = ‖x - z‖ + dist x x₀ := by rw [dist_eq_norm, norm_sub_rev]
            _ ≤ R + 1 := by linarith
        simp [hz, fderiv_of_notMem_tsupport ℝ hxz]
    · exact (integrable_indicator_iff measurableSet_closedBall).2
        (integrableOn_const (isCompact_closedBall x₀ (R + 1)).measure_lt_top.ne)
    · refine Eventually.of_forall fun z x _ ↦ ?_
      have h1 : HasFDerivAt (fun x : Rn N ↦ x - z) (ContinuousLinearMap.id ℝ (Rn N)) x :=
        (hasFDerivAt_id x).sub_const z
      exact ((hρd (x - z)).hasFDerivAt.comp x h1).congr_fderiv (by ext v; simp)
  rw [hkey.fderiv, ContinuousLinearMap.integral_apply]
  exact ((hρ'c.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
    (hrefl (fderiv ℝ ρ) x₀ hρ'cs)).integrableOn
```

## Key steps

1. ρ is C¹ with compact support, so Dρ is continuous, compactly supported and bounded by some C; and tsupport ρ ⊆ B̄_R(0) for some R.
2. For fixed a, z ↦ ρ(a − z) and z ↦ Dρ(a − z) are continuous with compact support, hence integrable on G.
3. Chain rule: x ↦ ρ(x − z) has derivative Dρ(x − z).
4. Domination on B_1(x₀): ‖Dρ(x − z)‖ ≤ C·1_{B̄_{R+1}(x₀)}(z), which is integrable.
5. Apply hasFDerivAt_integral_of_dominated_of_fderiv_le with the measure L^N⌞G to get Du(x₀) = ∫_G Dρ(x₀ − z) dz.
6. Evaluate at w using ContinuousLinearMap.integral_apply.

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
