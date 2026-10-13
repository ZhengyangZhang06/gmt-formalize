# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1.density_estimates-a1.sobolev_indicator-a1.mollified_fderiv_le-a1`
- Child DAG node: `root.de_giorgi-a1.density_estimates-a1.sobolev_indicator-a1.mollified_fderiv_le-a1.kernel_gauss_green-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the implementation note of the parent proof ("apply the Gauss-Green identity to the C¹ field h_w(z) := ρ(y − z)w; its topological support lies in B̄_r(y) ⊆ K' ⊆ U and div h_w(z) = −Dρ(y − z)w. Since Dρ(y − z) = 0 for z ∉ B̄_r(y), in particular for z ∉ U, ... ∫_G Dρ(y − z)w dz = ∫_{G∩U} Dρ(y − z)w dz = ∫ρ(y − z)⟨w, ν(z)⟩ dμ(z)"). This is the pointwise form of the identity ∫ g·∇u_σ = −∫ u div(φ_σ ⋆ g) in the proof of Simon Ch. 2, Lemma 2.5 (chapter-02.txt lines 543-596), tested against the single field ρ(y − ·)w. Notation: φ(z) := ρ(y − z); ⟨·,·⟩ and |·| are the Euclidean inner product and norm; Dv(z) = fderiv ℝ v z; div h(z) = trace Dh(z) (the contract's euclideanDivergence). Lean's Bochner integral is 0 for non-integrable functions; the manipulations below (negation, pointwise rewriting of integrands, restriction by an indicator) are valid without any integrability.

1. (Support of φ.) If φ(z) ≠ 0, then y − z lies in the support of ρ, hence in tsupport ρ ⊆ B̄_r(0), so |z − y| = |y − z| ≤ r, i.e. z ∈ B̄_r(y). Since B̄_r(y) is closed, tsupport φ = closure(support φ) ⊆ B̄_r(y) (closure_minimal). Equivalently, if z ∉ B̄_r(y) then |y − z| > r, so y − z ∉ tsupport ρ.

2. (Derivative of φ.) The map z ↦ y − z has derivative −id (HasFDerivAt.const_sub). Since ρ is C¹ it is differentiable, and by the chain rule φ has derivative Dφ(z) = Dρ(y − z) ∘ (−id) = −Dρ(y − z) at every z (HasFDerivAt.comp, then HasFDerivAt.congr_fderiv).

3. (The test field.) Let h(z) := φ(z)w ∈ ℝ^N. Then h is C¹, being the C¹ scalar function ρ ∘ (y − ·) times a constant vector (ContDiff.comp, ContDiff.smul). Its topological support satisfies tsupport h ⊆ tsupport φ ⊆ B̄_r(y) ⊆ U (tsupport_smul_subset_left and step 1). And h has compact support, because tsupport h is a closed subset of the compact ball B̄_r(y) (ℝ^N is proper; IsCompact.of_isClosed_subset).

4. (Divergence of the test field.) By step 2 and the product rule for a scalar function times a constant vector (HasFDerivAt.smul_const), Dh(z) is the rank-one map k ↦ (Dφ(z)k)w = −(Dρ(y − z)k)w, i.e. Dh(z) = (−Dρ(y − z)).smulRight w. The trace of a rank-one map k ↦ ℓ(k)w equals ℓ(w): use ContinuousLinearMap.coe_smulRight and then LinearMap.trace_smulRight. Alternatively, with an orthonormal basis (e_i), Σ_i ⟨e_i, ℓ(e_i)w⟩ = ℓ(Σ_i ⟨e_i, w⟩e_i) = ℓ(w). Hence div h(z) = −Dρ(y − z)w for every z.

5. (Gauss–Green.) By step 3, h is admissible in the Gauss–Green identity of the pair, so ∫_{G∩U} div h dL^N = −∫ ⟨h(z), ν(z)⟩ dμ(z). By step 4 the left side is ∫_{G∩U} (−Dρ(y − z)w) dz = −∫_{G∩U} Dρ(y − z)w dz (integral_neg). Since ⟨φ(z)w, ν(z)⟩ = φ(z)⟨w, ν(z)⟩ (real_inner_smul_left), the right side is −∫ ρ(y − z)⟨w, ν(z)⟩ dμ(z). Cancelling the minus signs (neg_inj) gives ∫_{G∩U} Dρ(y − z)w dz = ∫ ρ(y − z)⟨w, ν(z)⟩ dμ(z).

6. (From G ∩ U to G.) Let f(z) := Dρ(y − z)w. If z ∉ U, then z ∉ B̄_r(y) (as B̄_r(y) ⊆ U), so y − z ∉ tsupport ρ by step 1, so Dρ(y − z) = 0 (fderiv_of_notMem_tsupport) and f(z) = 0. Hence f = 1_U·f pointwise. Since U is open, hence measurable, ∫_G f dL^N = ∫_G 1_U f dL^N = ∫_{G∩U} f dL^N (setIntegral_indicator). Combining with step 5 gives ∫_G Dρ(y − z)w dz = ∫ ρ(y − z)⟨w, ν(z)⟩ dμ(z). ∎

Remarks. (i) Neither the measurability of G nor r ≥ 0 is needed. If r < 0 then B̄_r(0) = ∅, so ρ ≡ 0, both sides vanish, and the argument above covers this case verbatim. (ii) In Lean the conjuncts of IsGaussGreenPair U G μ ν are, in order: μ Uᶜ = 0; finiteness on compact subsets of U; AEStronglyMeasurable ν μ; ‖ν‖ = 1 μ-a.e.; the Gauss–Green identity. So the identity is hGG.2.2.2.2.

Appendix (non-binding; the numbered proof above is the contract). Kernel-checked Lean proof of exactly this frozen type, compiled during decomposition after `import GMT.Ch03.Submission` in the comparator scope (namespace GMT.Ch03 with the contract's `open` commands), in the placement `theorem Submission.X` used by accepted leaves; Lean v4.35.0-rc3, Mathlib 25730c7c; axioms: propext, Classical.choice, Quot.sound.
```lean
theorem Submission.deGiorgiSobIndMFL_setIntegral_fderiv_kernel_eq : ∀ (N : ℕ) (U G : Set (Rn N)) (μ : Measure (Rn N)) (ν : Rn N → Rn N), IsOpen U → IsGaussGreenPair U G μ ν → ∀ (ρ : Rn N → ℝ) (r : ℝ) (y w : Rn N), ContDiff ℝ 1 ρ → HasCompactSupport ρ → tsupport ρ ⊆ Metric.closedBall (0 : Rn N) r → Metric.closedBall y r ⊆ U → ∫ z in G, fderiv ℝ ρ (y - z) w = ∫ z, ρ (y - z) * inner ℝ w (ν z) ∂μ := by
  intro N U G μ ν hU hGG ρ r y w hρ hρc hρr hyU
  have hρd : Differentiable ℝ ρ := hρ.differentiable one_ne_zero
  -- derivative of the reflected kernel `z ↦ ρ (y - z)`
  have hφd : ∀ z, HasFDerivAt (fun z ↦ ρ (y - z)) (-(fderiv ℝ ρ (y - z))) z := by
    intro z
    have h1 : HasFDerivAt (fun z : Rn N ↦ y - z) (-(ContinuousLinearMap.id ℝ (Rn N))) z :=
      (hasFDerivAt_id z).const_sub y
    have h2 := (hρd (y - z)).hasFDerivAt.comp z h1
    exact h2.congr_fderiv (by ext v; simp)
  -- support of the reflected kernel
  have hφsupp : tsupport (fun z ↦ ρ (y - z)) ⊆ Metric.closedBall y r := by
    refine closure_minimal ?_ Metric.isClosed_closedBall
    intro z hz
    have h1 : y - z ∈ tsupport ρ := subset_tsupport _ hz
    have h2 := hρr h1
    rw [Metric.mem_closedBall, dist_zero_right] at h2
    rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
    exact h2
  -- the vector field `h z = ρ (y - z) • w`
  have hhC : ContDiff ℝ 1 (fun z ↦ ρ (y - z) • w) :=
    (hρ.comp (contDiff_const.sub contDiff_id)).smul contDiff_const
  have hhsupp : tsupport (fun z ↦ ρ (y - z) • w) ⊆ Metric.closedBall y r :=
    (tsupport_smul_subset_left (fun z ↦ ρ (y - z)) (fun _ ↦ w)).trans hφsupp
  have hhc : HasCompactSupport (fun z ↦ ρ (y - z) • w) :=
    (isCompact_closedBall y r).of_isClosed_subset (isClosed_tsupport _) hhsupp
  have hGGh := hGG.2.2.2.2 (fun z ↦ ρ (y - z) • w) hhC hhc (hhsupp.trans hyU)
  -- its divergence
  have hdiv : ∀ z, Poincare.SimonGMT.Chapter02.euclideanDivergence (fun z ↦ ρ (y - z) • w) z =
      -(fderiv ℝ ρ (y - z) w) := by
    intro z
    have hfd : fderiv ℝ (fun z ↦ ρ (y - z) • w) z = (-(fderiv ℝ ρ (y - z))).smulRight w :=
      ((hφd z).smul_const w).fderiv
    unfold Poincare.SimonGMT.Chapter02.euclideanDivergence
    rw [hfd, ContinuousLinearMap.coe_smulRight, LinearMap.trace_smulRight]
    simp
  -- the integrand vanishes off `U`
  have hvan : ∀ z, z ∉ U → fderiv ℝ ρ (y - z) w = 0 := by
    intro z hz
    have hz' : z ∉ Metric.closedBall y r := fun h ↦ hz (hyU h)
    have : y - z ∉ tsupport ρ := by
      intro h
      apply hz'
      have h2 := hρr h
      rw [Metric.mem_closedBall, dist_zero_right] at h2
      rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
      exact h2
    rw [fderiv_of_notMem_tsupport ℝ this]
    simp
  have hrestr : ∫ z in G, fderiv ℝ ρ (y - z) w = ∫ z in G ∩ U, fderiv ℝ ρ (y - z) w := by
    rw [← setIntegral_indicator hU.measurableSet]
    refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
    by_cases hz : z ∈ U
    · simp [hz]
    · simp [hz, hvan z hz]
  rw [hrestr]
  have hL : ∫ z in G ∩ U, Poincare.SimonGMT.Chapter02.euclideanDivergence (fun z ↦ ρ (y - z) • w) z =
      -∫ z in G ∩ U, fderiv ℝ ρ (y - z) w := by
    rw [← integral_neg]
    exact integral_congr_ae (Eventually.of_forall hdiv)
  have hR : ∫ z, inner ℝ ((fun z ↦ ρ (y - z) • w) z) (ν z) ∂μ = ∫ z, ρ (y - z) * inner ℝ w (ν z) ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
    simp [real_inner_smul_left]
  rw [hL, hR] at hGGh
  exact neg_inj.mp hGGh
```

## Key steps

1. For φ(z) := ρ(y − z): tsupport φ ⊆ B̄_r(y), and y − z ∉ tsupport ρ whenever z ∉ B̄_r(y).
2. Chain rule: Dφ(z) = −Dρ(y − z).
3. h := φ·w is C¹ with compact support and tsupport h ⊆ B̄_r(y) ⊆ U.
4. div h(z) = trace((−Dρ(y − z)).smulRight w) = −Dρ(y − z)w (LinearMap.trace_smulRight).
5. Gauss–Green identity of the pair for h, then cancel the signs: ∫_{G∩U} Dρ(y − z)w dz = ∫ρ(y − z)⟨w, ν⟩ dμ.
6. The integrand vanishes off U, so ∫_G = ∫_{G∩U} (setIntegral_indicator).

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
