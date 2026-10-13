# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.im_completeness-a1`
- Child DAG node: `root.deformation-a1.im_completeness-a1.l1_cauchy_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 3 of the parent proof (printed (2)–(3) of Simon 3.13): "the series κ₁ + Σ_j(κ_{j+1} − κ_j) … converge λ-a.e. (absolutely) to functions κ, θ, with ∫|κ_j − κ|dλ ≤ Σ_{i≥j}∫|κ_{i+1} − κ_i|dλ → 0 … (only the differences need to be integrable)". Here this classical Riesz–Fischer argument is stated for an arbitrary measure (no σ-finiteness) and an arbitrary complete normed group; the parent applies it to the coordinate vectors of the k-vector densities, with values in EuclideanSpace ℝ (SimonMultiIndex k N).

1. (Increments.) Put d_n(x) := ‖f_{n+1}(x) − f_n(x)‖ₑ ∈ [0, ∞]. Since f_{n+1} − f_n is μ-a.e. strongly measurable, d_n is μ-a.e. measurable. Let S(x) := Σ_n d_n(x) ∈ [0, ∞]. By the monotone convergence theorem for series of nonnegative a.e.-measurable functions (lintegral_tsum), ∫⁻ S dμ = Σ_n ∫⁻ d_n dμ < ∞ by hypothesis. Hence S(x) < ∞ for μ-a.e. x (ae_lt_top).

2. (Pointwise Cauchy property.) Fix x with S(x) < ∞ and put T_n(x) := Σ_{i≥n} d_i(x). For m ≥ n the triangle inequality gives ‖f_m(x) − f_n(x)‖ₑ ≤ Σ_{i=n}^{m−1} d_i(x) ≤ T_n(x), and T_n(x) → 0 as n → ∞, being the tails of a series with finite sum S(x) (ENNReal.tendsto_sum_nat_add). So (f_n(x))_n is a Cauchy sequence in the complete space E and converges.

3. (The limit g.) Define g(x) := lim_n f_n(x) when this limit exists and g(x) := 0 otherwise (e.g. g(x) := limUnder atTop (fun n ↦ f_n(x)) when the sequence converges). By Steps 1–2, f_n(x) → g(x) for μ-a.e. x. Being a μ-a.e. limit of μ-a.e. strongly measurable functions (the filter atTop on ℕ is countably generated), g is μ-a.e. strongly measurable (aestronglyMeasurable_of_tendsto_ae).

4. (Tail bound.) Let x be as in Step 2 and n ∈ ℕ. Since f_m(x) → g(x) and ‖·‖ₑ is continuous, ‖f_n(x) − g(x)‖ₑ = lim_m ‖f_n(x) − f_m(x)‖ₑ ≤ T_n(x) by Step 2. Hence ‖f_n − g‖ₑ ≤ T_n μ-a.e.

5. (L¹ convergence.) By Step 4, monotonicity of the lintegral and lintegral_tsum, ∫⁻ ‖f_n − g‖ₑ dμ ≤ ∫⁻ T_n dμ = Σ_{i≥n} ∫⁻ d_i dμ. The right side is the n-th tail of the series Σ_i ∫⁻ d_i dμ, whose sum is finite, so it tends to 0 as n → ∞ (ENNReal.tendsto_sum_nat_add). Hence ∫⁻ ‖f_n − g‖ₑ dμ → 0. Together with Step 3 this proves the statement. ∎

Formalization note. The following Lean proof of exactly this declaration compiles against the frozen commit d8d46c9 (lake env lean in the comparator scope, default maxHeartbeats, no set_option, no sorry; #print axioms: propext, Classical.choice, Quot.sound). It follows Steps 1–5: lintegral_tsum and ae_lt_top' (Step 1), cauchySeq_of_edist_le_of_tsum_ne_top (Step 2), limUnder and aestronglyMeasurable_of_tendsto_ae (Step 3), edist_le_tsum_of_edist_le_of_tendsto (Step 4), ENNReal.tendsto_sum_nat_add (Step 5).
```lean
theorem Submission.imc_ae_tendsto_of_summable_lintegral :
    ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (E : Type) [NormedAddCommGroup E] [CompleteSpace E] (f : ℕ → X → E), (∀ n, AEStronglyMeasurable (f n) μ) → (∑' n, ∫⁻ x, ‖f (n + 1) x - f n x‖ₑ ∂μ) ≠ ∞ → ∃ g : X → E, AEStronglyMeasurable g μ ∧ (∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) ∧ Tendsto (fun n => ∫⁻ x, ‖f n x - g x‖ₑ ∂μ) atTop (𝓝 0) := by
  intro X _ μ E _ _ f hf hsum
  set d : ℕ → X → ℝ≥0∞ := fun n x => ‖f (n + 1) x - f n x‖ₑ with hd_def
  have hd : ∀ n, AEMeasurable (d n) μ := fun n => ((hf (n + 1)).sub (hf n)).enorm
  have hS : ∫⁻ x, ∑' n, d n x ∂μ = ∑' n, ∫⁻ x, d n x ∂μ := lintegral_tsum hd
  have hfin : ∀ᵐ x ∂μ, ∑' n, d n x < ∞ :=
    ae_lt_top' (AEMeasurable.tsum hd) (by rw [hS]; exact hsum)
  have hedist : ∀ x n, edist (f n x) (f (n + 1) x) ≤ d n x := fun x n => by
    rw [edist_comm, edist_eq_enorm_sub]
  have hcauchy : ∀ᵐ x ∂μ, CauchySeq (fun n => f n x) := by
    filter_upwards [hfin] with x hx
    exact cauchySeq_of_edist_le_of_tsum_ne_top (fun n => d n x) (hedist x) hx.ne
  set g : X → E := fun x => limUnder atTop (fun n => f n x) with hg_def
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
    filter_upwards [hcauchy] with x hx
    exact hx.tendsto_limUnder
  refine ⟨g, aestronglyMeasurable_of_tendsto_ae atTop hf hlim, hlim, ?_⟩
  have htail : ∀ n, ∀ᵐ x ∂μ, ‖f n x - g x‖ₑ ≤ ∑' m, d (n + m) x := by
    intro n
    filter_upwards [hfin, hlim] with x hx hxl
    rw [← edist_eq_enorm_sub]
    exact edist_le_tsum_of_edist_le_of_tendsto (fun m => d m x) (hedist x) hxl n
  have hbound : ∀ n, ∫⁻ x, ‖f n x - g x‖ₑ ∂μ ≤ ∑' m, ∫⁻ x, d (n + m) x ∂μ := by
    intro n
    calc ∫⁻ x, ‖f n x - g x‖ₑ ∂μ ≤ ∫⁻ x, ∑' m, d (n + m) x ∂μ := lintegral_mono_ae (htail n)
      _ = ∑' m, ∫⁻ x, d (n + m) x ∂μ := lintegral_tsum fun m => hd (n + m)
  have htend : Tendsto (fun n => ∑' m, ∫⁻ x, d (n + m) x ∂μ) atTop (𝓝 0) := by
    have := ENNReal.tendsto_sum_nat_add (fun m => ∫⁻ x, d m x ∂μ) hsum
    simpa [add_comm] using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htend (fun n => bot_le) hbound
```

## Key steps

1. ∫⁻ Σ_n ‖f_{n+1} − f_n‖ₑ = Σ_n ∫⁻ ‖f_{n+1} − f_n‖ₑ < ∞ (lintegral_tsum), so the increment series converges μ-a.e.
2. Where it converges, (f_n(x)) is Cauchy; completeness of E gives g(x); g is a.e. strongly measurable as an a.e. limit.
3. ‖f_n − g‖ₑ ≤ Σ_{i≥n} ‖f_{i+1} − f_i‖ₑ a.e.; integrating, ∫⁻‖f_n − g‖ₑ is bounded by the vanishing tail of a convergent series.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp workspaces/gmt-ch06/GMT/Ch06/Contract.lean <snapshot>/project/GMT/Ch06/Contract.lean; cmp GMT/Ch06/Submission.lean GMT/Ch06/Contract.lean; cmp <snapshot>/project/GMT/Ch06/Contract.lean <snapshot>/project/GMT/Ch06/Submission.lean (all byte-identical)`
- `grep '^import' <snapshot>/project/GMT/Ch06/Contract.lean (8 imports) and a transitive SimonGMT import-closure walk (13 modules; Chapter01.Lusin not included)`
- `rg -n 'theorem MemLp.exists_hasCompactSupport_eLpNorm_sub_le|exists_hasCompactSupport_integral_sub_le' <snapshot>/mathlib/Mathlib (ContinuousMapDense.lean:141, :226); rg -n 'theorem ContinuousMap.exists_extension' <snapshot>/mathlib/Mathlib (TietzeExtension.lean:77): both files are outside the frozen closure`
- `rg -n 'theorem cauchySeq_of_edist_le_of_tsum_ne_top|theorem edist_le_tsum_of_edist_le_of_tendsto|theorem tendsto_integral_of_L1|theorem lintegral_tsum|theorem integral_indicator₀|theorem dist_convolution_le|theorem exists_continuous_zero_one_of_isClosed' <snapshot>/mathlib/Mathlib`
- `rg -n 'imc_' <snapshot>/project <snapshot>/mathlib and lake-packages-25730c7c/simongmt (no match); git log --all -S <each new imc_ name> (no commit); grep of the new names over runs/*/nodes (no match)`
- `python3 -I over dag.json: status, candidate commit, parent and lean_statement of the five reused names and of lpf_wtc_ae_zero_density_off_set; comparison of every new child type against all DAG node types (no duplicate); simulation of runtime.py _existing_lean_name_problem/_accepted_checkpoint and _topological on the current DAG (no problem; acyclic)`
- `sed -n 6532,6575p /runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py (reuse rule), leaf_verification.py check_source_delta (no set_option in a leaf delta), decomposition_scope.py (recomputed parent_contract_digest 94deade2…)`
- `git show 12d217bba2a4:GMT/Ch06/Submission.lean (accepted zero-density proof) and git show 83e1f61809c1:GMT/Ch06/Submission.lean (accepted fiw_im_mass_formula: inline L¹ density and mollification)`
- `lake env lean /tmp/imc_v2/lean/Avail2.lean, Api3–Api7.lean (closure probes: Tietze, ContinuousMapDense, UniformContinuous.exists_contDiff_dist_le and Measurable.nat_floor absent; ContDiffBump, HasCompactSupport.contDiff_convolution_left and Lp.ae_tendsto_of_cauchy_eLpNorm present; NVector ContinuousAdd/PseudoMetrizableSpace workarounds)`
- `python3 -I /tmp/imc_v2/scripts/build_stmts.py (validate_lean_statement on all 13 types) and lake env lean /tmp/imc_v2/lean/Stmts.lean (all elaborate; only sorry warnings)`
- `lake env lean /tmp/imc_v2/lean/Test_deformation_im_completeness.lean, Test_imc_im_density_limit.lean, Test_imc_isRectifiableTriple_of_eventually_mem.lean, Test_imc_ae_tendsto_of_summable_lintegral.lean, Test_imc_ae_zero_density_off_set.lean (all compile at default heartbeats; standard axioms plus the stand-in sibling axioms)`
- `sed -n 560,735p book/sources/chapter-01-source.txt (Simon Ch. 1, 3.3–3.7 and the 5-times covering lemma)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/TietzeExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/UrysohnsLemma.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-completeness-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-completeness-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-zero-3299c8304e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-zero-3299c8304e/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1-pairing-expansion-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-local-to-global-im-a1-tau-integrable-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-lusi-5c440af24d/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-frame-sign-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-blow-7c8d1035a6/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-mass-formula-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-01-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/decomposition_scope.py`
- `/tmp/imc_v2/lean/Stmts.lean`
- `/tmp/imc_v2/lean/Test_deformation_im_completeness.lean`
- `/tmp/imc_v2/lean/Test_imc_im_density_limit.lean`
- `/tmp/imc_v2/lean/Test_imc_isRectifiableTriple_of_eventually_mem.lean`
- `/tmp/imc_v2/lean/Test_imc_ae_tendsto_of_summable_lintegral.lean`
- `/tmp/imc_v2/lean/Test_imc_ae_zero_density_off_set.lean`

Pinned revisions confirmed: the frozen contract is byte-identical to the snapshot (Submission = Contract). The frozen import closure lacks Tietze (TietzeExtension.lean), L¹ density of C_c (ContinuousMapDense.lean) and SimonGMT Lusin. So mass_lower_bound's approximation step is proved inline from regularity, Urysohn and MemLp.induction_dense, as the accepted fiw_im_mass_formula does. Mathlib supplies the Riesz–Fischer and limit tools used by l1_cauchy_limit and density_limit (cauchySeq_of_edist_le_of_tsum_ne_top, edist_le_tsum_of_edist_le_of_tendsto, tendsto_integral_of_L1). Following the correction, the zero-density child uses the fresh name imc_ae_zero_density_off_set and is the W = ℝ^Q case of the accepted lpf_wtc_ae_zero_density_off_set; its Lean proof embeds that accepted proof (commit 12d217bb) and compiles. The five reused names are accepted checkpoints with identical types, and the controller's name check simulated on the current DAG passes. All 13 types validate and elaborate in the comparator scope. The parent compiles from mass_lower_bound, density_limit and tau_integrable; density_limit, limit_triple and l1_cauchy_limit also compile from their siblings; all at default heartbeats with axioms propext, Classical.choice and Quot.sound only. No imc_ name occurs in the project, SimonGMT, Mathlib, git history or the DAG.
