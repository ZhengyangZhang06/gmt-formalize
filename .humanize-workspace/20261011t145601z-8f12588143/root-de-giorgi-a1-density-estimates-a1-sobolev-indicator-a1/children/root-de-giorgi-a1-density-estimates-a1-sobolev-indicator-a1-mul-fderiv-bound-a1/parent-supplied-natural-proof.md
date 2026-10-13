# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1.density_estimates-a1.sobolev_indicator-a1`
- Child DAG node: `root.de_giorgi-a1.density_estimates-a1.sobolev_indicator-a1.mul_fderiv_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 1 ("w_σ := ζu_σ ... is Lipschitz (a product of bounded Lipschitz functions) and vanishes outside T, so it has compact support. At every point where ζ is differentiable (L^N-a.e., by Rademacher), Dw_σ = u_σDζ + ζDu_σ, so ∫|Dw_σ| ≤ ∫ζ|∇u_σ| + ∫u_σ|Dζ|"), stated for an arbitrary Lipschitz u with values in [0, 1] (in the parent u = u_σ). Notation: T := tsupport ζ, which is compact; M := sup_y ζ(y); Dv(y) := fderiv ℝ v y and |Dv(y)| its operator norm. No step uses N ≥ 1.

1. (Bound on ζ.) ζ is continuous (being Lipschitz) with compact support, so M < ∞ (M := 0 if T = ∅) and 0 ≤ ζ ≤ M.

2. (Lipschitz.) For x, y ∈ ℝ^N, ζ(x)u(x) − ζ(y)u(y) = ζ(x)(u(x) − u(y)) + u(y)(ζ(x) − ζ(y)), so |ζ(x)u(x) − ζ(y)u(y)| ≤ M·L|x − y| + 1·K|x − y|, using 0 ≤ ζ ≤ M and 0 ≤ u ≤ 1. Hence ζu is K'-Lipschitz with K' := ML + K ∈ ℝ≥0.

3. (Compact support.) ζ(y)u(y) ≠ 0 implies ζ(y) ≠ 0, so support(ζu) ⊆ support ζ and tsupport(ζu) ⊆ T. A closed subset of the compact set T is compact, so ζu has compact support.

4. (Pointwise a.e. bound.) By Rademacher's theorem (Mathlib LipschitzWith.ae_differentiableAt, L^N being an additive Haar measure on the finite-dimensional space ℝ^N), ζ is differentiable at L^N-a.e. point and u is differentiable at L^N-a.e. point; hence both are differentiable at L^N-a.e. y. At such y the product rule gives D(ζu)(y) = ζ(y)Du(y) + u(y)Dζ(y), hence ‖D(ζu)(y)‖ ≤ |ζ(y)|‖Du(y)‖ + |u(y)|‖Dζ(y)‖ = ζ(y)‖Du(y)‖ + u(y)‖Dζ(y)‖, because ζ(y) ≥ 0 and u(y) ≥ 0. Thus ‖D(ζu)‖ ≤ ζ‖Du‖ + u‖Dζ‖ holds L^N-a.e.

5. (Integrability.) For every v : ℝ^N → ℝ the map y ↦ Dv(y) is Borel measurable (measurable_fderiv), so the three functions ‖D(ζu)‖, ζ‖Du‖ and u‖Dζ‖ are measurable. If v is C-Lipschitz then ‖Dv(y)‖ ≤ C for every y (norm_fderiv_le_of_lipschitz), and Dv(y) = 0 for y ∉ tsupport v (fderiv_of_notMem_tsupport). Hence, by steps 1-3, 0 ≤ ‖D(ζu)‖ ≤ K'·1_T, 0 ≤ ζ‖Du‖ ≤ LM·1_T and 0 ≤ u‖Dζ‖ ≤ K·1_T. As T is compact, L^N(T) < ∞, so all three functions are L^N-integrable.

6. (Conclusion.) By step 4 and monotonicity of the integral for integrable functions (integral_mono_ae), ∫‖D(ζu)‖ ≤ ∫(ζ‖Du‖ + u‖Dζ‖), and by additivity of the integral of integrable functions (integral_add, step 5) the right-hand side equals (∫ζ‖Du‖) + ∫u‖Dζ‖. Together with steps 2 and 3 this proves all three assertions. ∎

## Key steps

1. M := sup ζ < ∞; |ζ(x)u(x) − ζ(y)u(y)| ≤ (ML + K)|x − y|, so ζu is (ML + K)-Lipschitz.
2. support(ζu) ⊆ support ζ, hence tsupport(ζu) ⊆ tsupport ζ is compact.
3. Rademacher: ζ and u are differentiable a.e.; the product rule gives ‖D(ζu)‖ ≤ ζ‖Du‖ + u‖Dζ‖ a.e.
4. All three integrands are measurable (measurable_fderiv) and bounded by constants times 1_{tsupport ζ}, hence integrable.
5. integral_mono_ae and integral_add give the integral inequality.

## Reference use

### local-project

Queries:
- `diff GMT/Ch03/Contract.lean GMT/Ch03/Submission.lean; cmp <snapshot>/project/GMT/Ch03/Contract.lean GMT/Ch03/Contract.lean; cmp <snapshot>/project/GMT/Ch03/Submission.lean GMT/Ch03/Submission.lean`
- `sed -n 600,760p book/chapter-03.txt; sed -n 500,600p book/chapter-02.txt (Lemma 2.5 and its proof)`
- `python3 -I over dag.json: lean_name list, byte-check of parent/sibling frozen strings, collision check of deGiorgiSobInd_* names`
- `grep -rl 'deGiorgiSobInd\|sobInd_\|SobInd' GMT/Scratch/ dag.json`
- `sed -n 1,200p <snapshot>/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `grep -n 'theorem\|lemma\|def \|structure' <snapshot>/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean <snapshot>/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `grep -n -A6 'theorem eLpNorm_lim_le_liminf_eLpNorm' <snapshot>/mathlib/Mathlib/MeasureTheory/Function/LpSpace/Complete.lean; grep -n '^namespace' same file`
- `rg -n 'IsCompact.cthickening|isCompact_cthickening' <snapshot>/mathlib/Mathlib/Topology/MetricSpace/`
- `rg -n 'integrableOn_of_bounded' <snapshot>/mathlib/Mathlib/MeasureTheory`
- `rg -n 'protected theorem indicator₀' <snapshot>/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/`
- `rg -n 'tendsto_one_div_add_atTop_nhds_zero_nat' <snapshot>/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `grep -n 'notation3 "∫ "' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `grep -rn 'theorem integral_indicator₀' <snapshot>/mathlib/Mathlib/MeasureTheory`
- `rg -n -i 'mollif|convolution|ContDiffBump' .lake/packages/simongmt/Poincare`
- `lake env lean GMT/Scratch/SobIndAvail.lean (#check after import GMT.Ch03.Submission: ContDiffBump.normed, convolution, eLpNorm_lim_le_liminf_eLpNorm, ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable, HasCompactSupport.hasFDerivAt_convolution_left/contDiff_convolution_left, IsCompact.exists_cthickening_subset_open, LipschitzWith.ae_differentiableAt, measurable_fderiv, norm_fderiv_le_of_lipschitz, fderiv_of_notMem_tsupport, integral_integral_swap, gradient)`
- `lake env lean GMT/Scratch/SobIndSplitStatements.lean`
- `lake env lean GMT/Scratch/SobIndSplitAssembly.lean (#print axioms deGiorgiDens_sobolev_indicator)`
- `lake env lean GMT/Scratch/SobIndReuseCheck.lean (#print axioms Poincare.SimonGMT.Chapter08.ae_constancyMollifier_convolution_tendsto and WeakDerivativesZero.fderiv_convolution_eq_zero; application on Rn N)`
- `lake env lean GMT/Scratch/SobIndNameCheck.lean (#check of every Mathlib lemma name cited in the child proofs)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Ch03/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1-sobolev-indicator-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1-lipschitz-sobolev-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/LpSpace/Complete.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyPartition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/SobIndAvail.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/SobIndSplitStatements.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/SobIndSplitAssembly.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/SobIndReuseCheck.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/SobIndNameCheck.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/LipschitzSobolevSplitAssembly.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/DensityEstimatesSplitAllStatements.lean`

The snapshot's Contract.lean and Submission.lean are byte-identical to the workspace copies (project d09bc8a, Mathlib 25730c7c), and Submission is still identical to Contract.

Nothing in the library proves the Sobolev inequality for ζχ_G or the mollified-gradient bound for a Gauss–Green pair. Mathlib has no Gauss–Green/BV theory. SimonGMT Chapter02/BV.lean only defines euclideanDivergence (the trace of fderiv) and IsLocallyBV, and states that mollification is left open. The related DAG nodes (lipschitz_smooth_approx, lipschitz_gauss_green, the indicator_compactness mollifier lemmas) have different statements and none of them is a dependency.

Available inside the contract's import closure, so usable in frozen statements and proofs:
- MeasureTheory.convolution
- HasCompactSupport.contDiff_convolution_left and HasCompactSupport.hasFDerivAt_convolution_left
- IsCompact.exists_cthickening_subset_open, IsCompact.cthickening, Metric.cthickening_mono, Metric.mem_cthickening_of_dist_le
- LipschitzWith.ae_differentiableAt, measurable_fderiv, norm_fderiv_le_of_lipschitz, fderiv_of_notMem_tsupport
- integral_integral_swap, Measure.integrableOn_of_bounded, AEStronglyMeasurable.indicator₀, integral_indicator₀
- Lp.eLpNorm_lim_le_liminf_eLpNorm (namespace MeasureTheory.Lp), so the parent assembly needs no extra import

Outside the closure, so usable only in proofs after adding imports:
- ContDiffBump.normed and ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (Mathlib.Analysis.Calculus.BumpFunction.{Normed,Convolution})
- gradient
For this reason the frozen child statements use a generic C¹ kernel ρ.

SimonGMT Chapter08/DistributionalConstancy.lean provides constancyMollifier (rIn = r/(k+1)/2, rOut = r/(k+1)) and ae_constancyMollifier_convolution_tendsto. Both apply on Euclidean N = Rn N and use only propext, Classical.choice and Quot.sound, so they can be reused for mollifier_seq. The same file's WeakDerivativesZero.fderiv_convolution_eq_zero is a Lean pattern for the key estimate.

Mathlib's ∫-notation parses its body at precedence 60, so `∫ y, A + ∫ y, B` reads as a single integral; mul_fderiv_bound needed explicit parentheses for this reason.

Lean evidence: all four frozen strings elaborate in the comparator scope and pass the rfl parse and instance checks. The exact parent type compiles from the exact stubs, with axioms propext, sorryAx (from the stubs only), Classical.choice and Quot.sound.
