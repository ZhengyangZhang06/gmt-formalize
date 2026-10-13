# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1.density_estimates-a1`
- Child DAG node: `root.de_giorgi-a1.density_estimates-a1.lipschitz_sobolev-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

(Implementation note: eLpNorm_le_eLpNorm_fderiv_one lives in Mathlib.Analysis.FunctionalSpaces.SobolevInequality and eLpNorm_lim_le_liminf_eLpNorm in Mathlib.MeasureTheory.Function.LpSpace.Complete; these modules must be imported.)
Source: parent proof Step 7, paragraph 'Constants' (the Gagliardo-Nirenberg-Sobolev inequality [GT01, Thm 7.10] for N ≥ 2; for N = 1 the one-dimensional bound sup|w| ≤ ½∫|w'|, erratum E6; extension from C¹_c to compactly supported Lipschitz functions by approximation), with the approximation supplied by sibling lipschitz_smooth_approx. Notation: N = n + 1; p as in the statement; ‖·‖_q := eLpNorm(·, q, L^N); Dv(y) := fderiv ℝ v y and |Dv(y)| its operator norm.

1. (Smooth case, n ≥ 1.) finrank ℝ ℝ^N = N ≥ 2, and N and p = N/(N − 1) are Hölder conjugate (1/p = n/(n + 1) = 1 − 1/N). Mathlib's Gagliardo-Nirenberg-Sobolev inequality (eLpNorm_le_eLpNorm_fderiv_one for the measure L^N and this conjugate pair; equivalently eLpNorm_le_eLpNorm_fderiv_of_eq with p = 1, p' = N/(N − 1)) gives C_N ∈ ℝ≥0 such that ‖v‖_p ≤ C_N ‖Dv‖_1 for every C¹ function v : ℝ^N → ℝ with compact support. For such v, |Dv| is continuous with compact support, so ‖Dv‖_1 = ∫⁻ |Dv| = ENNReal.ofReal(∫ |Dv| dL^N). Put c := C_N + 1 > 0; then (∗) ‖v‖_p ≤ ENNReal.ofReal(c ∫ |Dv| dL^N) for every C¹ function v with compact support.

2. (Smooth case, n = 0.) Here N = 1 and p = (0 + 1)/0 = ∞ in ℝ≥0∞. Let v : ℝ^1 → ℝ be C¹ with compact support. Identify ℝ^1 = EuclideanSpace ℝ (Fin 1) with ℝ through the linear isometry ι : ℝ → ℝ^1, t ↦ t e₀ (e₀ the unit basis vector); ι is measure preserving from Lebesgue measure on ℝ to L^1 (Mathlib: ι = WithLp.toLp 2 ∘ (t ↦ (fun _ : Fin 1 ↦ t)), and (PiLp.volume_preserving_toLp (Fin 1)).comp (volume_preserving_funUnique (Fin 1) ℝ).symm is MeasurePreserving), and every point of ℝ^1 is ι(t) for some t. The function f := v ∘ ι : ℝ → ℝ is C¹ with compact support, f'(t) = Dv(ι t) e₀, and |f'(t)| = |Dv(ι t)| (a linear functional L on the one-dimensional space ℝ^1 has operator norm |L e₀|, e₀ = EuclideanSpace.single 0 1). By the fundamental theorem of calculus, f(t) = ∫_{−∞}^t f'(s) ds = −∫_t^∞ f'(s) ds, so 2|f(t)| ≤ ∫_ℝ |f'(s)| ds = ∫_{ℝ^1} |Dv| dL^1. Hence |v(y)| ≤ ½ ∫ |Dv| dL^1 for every y, and ‖v‖_∞ ≤ ENNReal.ofReal(½ ∫ |Dv| dL^1). Put c := 1/2 > 0; then (∗) holds for every C¹ function v with compact support.

In both cases c > 0 depends only on n, and (∗) holds for every C¹ function v : ℝ^N → ℝ with compact support.

3. (Approximation.) Let u be K-Lipschitz with compact support and T := tsupport u. Sibling lipschitz_smooth_approx gives C¹ functions v_j with compact support, tsupport v_j ⊆ cthickening(1/(j + 1), T) ⊆ K₁ := cthickening(1, T) (compact, so L^N(K₁) < ∞), |Dv_j| ≤ K everywhere, v_j → u uniformly, and Dv_j → Du L^N-a.e.

4. (Gradient integrals converge.) |Dv_j(y)| ≤ K 1_{K₁}(y) for every y (Dv_j = 0 outside tsupport v_j), the bound is integrable, the functions |Dv_j| are measurable, and |Dv_j(y)| → |Du(y)| for L^N-a.e. y (continuity of the norm). By dominated convergence, ∫ |Dv_j| dL^N → ∫ |Du| dL^N.

5. (Passage to the limit.) v_j → u pointwise (indeed uniformly) and all these functions are continuous, hence a.e. strongly measurable. Mathlib eLpNorm_lim_le_liminf_eLpNorm (valid for every exponent, including ∞) gives ‖u‖_p ≤ liminf_j ‖v_j‖_p ≤ liminf_j ENNReal.ofReal(c ∫ |Dv_j|) by (∗). By step 4 and the continuity of t ↦ ENNReal.ofReal(c t), the right side equals ENNReal.ofReal(c ∫ |Du| dL^N). ∎

## Key steps

1. n ≥ 1: Mathlib's GNS inequality (eLpNorm_le_eLpNorm_fderiv_one) for C¹_c functions at the conjugate exponent N/(N−1) = (n+1)/n, with c := C_N + 1.
2. n = 0 (p = ∞): via the isometry ℝ ≅ ℝ^1 and the fundamental theorem of calculus, |v| ≤ ½∫|Dv| for C¹_c functions; c := 1/2.
3. Approximate a compactly supported Lipschitz u by the C¹ functions v_j of sibling lipschitz_smooth_approx.
4. ∫|Dv_j| → ∫|Du| by dominated convergence, and ‖u‖_p ≤ liminf‖v_j‖_p (eLpNorm_lim_le_liminf_eLpNorm).

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch03/Contract.lean GMT/Ch03/Contract.lean`
- `cmp <snapshot>/project/GMT/Ch03/Submission.lean GMT/Ch03/Submission.lean`
- `rg -n -i "gauss.?green|lipschitz.*divergence|divergence.*lipschitz" <snapshot>/project`
- `rg -n -i "gauss.?green|reducedBoundary|reduced_boundary|perimeter" .lake/packages/simongmt/Poincare`
- `rg -n -i "isoperimetric|density_estimate|densityEstimate|relative isoperimetric" <snapshot>/mathlib/Mathlib .lake/packages/simongmt/Poincare`
- `rg -n -i "cutoff|cut-off|radial" .lake/packages/simongmt/Poincare`
- `rg -n -i "sobolev|eLpNorm_le_eLpNorm_fderiv" .lake/packages/simongmt/Poincare`
- `rg -n -i "integral_divergence|divergence_theorem" <snapshot>/mathlib/Mathlib`
- `grep -n euclideanDivergence .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `grep 'theorem eLpNorm_le_eLpNorm_fderiv_of_eq|theorem eLpNorm_le_eLpNorm_fderiv_one|def SNormLESNormFDerivOfEqConst' <snapshot>/mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`
- `grep 'theorem Monotone.ae_differentiableAt|MonotoneOn.intervalIntegral_deriv_mem_uIcc|MonotoneOn.intervalIntegrable_deriv|hasDerivAt_iff_tendsto_slope|HasDerivAt.tendsto_slope_zero_left|LipschitzWith.ae_differentiableAt|tendsto_integral_filter_of_dominated_convergence|addHaar_ball|addHaar_sphere' <snapshot>/mathlib/Mathlib`
- `grep "eLpNorm_indicator_const'|eLpNormEssSup_indicator_const_eq|eLpNorm_mono|integral_indicator_one|integrableOn_const|integrable_indicator_iff" <snapshot>/mathlib/Mathlib/MeasureTheory`
- `grep 'measurable_fderiv|norm_fderiv_le_of_lipschitz|fderiv_of_notMem_tsupport|AEStronglyMeasurable.inner|integral_inner|Filter.Tendsto.limUnder_eq|HasDerivAt.rpow_const|integral_mul_le_Lp_mul_Lq_of_nonneg' <snapshot>/mathlib/Mathlib`
- `rg -n 'ae_convolution_tendsto_right_of_locallyIntegrable|HasCompactSupport.contDiff_convolution_left|hasFDerivAt_convolution_left|eLpNorm_lim_le_liminf_eLpNorm|IsCompact.exists_cthickening_subset_open|cthickening_empty|PiLp.volume_preserving_toLp|volume_preserving_funUnique' <snapshot>/mathlib/Mathlib`
- `python3 -I scope.py (importlib of verifier/gmt-compare.py; contract_scope(Contract.lean, 'GMT.Ch03.main_theorem')) -> NodeChallenge prefix`
- `lake env lean on GMT/Scratch/DensityEstimatesSplit{AllStatements,Statements,StatementsJL,Instances,Assembly,GlueB,GlueD,GlueF,GlueH,GlueI,LeafA,LeafC,LeafG}.lean`
- `python3 -I dag.json lean_name collision check and stub/frozen statement byte-identity check (extract.py)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/FinitePerimeter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/RadialCutoffDifferentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/Sobolev.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/Indicator.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/LpSpace/Complete.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Inner.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/L2Space.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Separation/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/LinearAlgebra/AffineSpace/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/DensityEstimatesSplitAllStatements.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/DensityEstimatesSplitInstances.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/DensityEstimatesSplitAssembly.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/DensityEstimatesSplitGlueB.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/DensityEstimatesSplitGlueD.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/DensityEstimatesSplitGlueF.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/DensityEstimatesSplitGlueH.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/DensityEstimatesSplitGlueI.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/DensityEstimatesSplitLeafA.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/DensityEstimatesSplitLeafC.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/DensityEstimatesSplitLeafG.lean`

The snapshot Contract.lean and Submission.lean are byte-identical to the workspace (project d09bc8a, Mathlib 25730c7c).

Not in the library (so these become children): Mathlib and the pinned SimonGMT contain no Gauss–Green identity for Lipschitz test functions, no BV/indicator Sobolev inequality for Gauss–Green pairs, no radial cut-off coarea identity, no density estimate, and no isoperimetric differential inequality. Within SimonGMT, Chapter03/FinitePerimeter.lean has only the §4 definitions; Chapter04/Sobolev.lean is the varifold (Michael–Simon) inequality; the Chapter08 radial cut-offs are smooth varifold cut-offs, not applicable here. No DAG node overlaps; the accepted gauss_green-a1 children concern existence and uniqueness of the pair, not these lemmas.

Library facts located for the child proofs:
- GNS: eLpNorm_le_eLpNorm_fderiv_one / _of_eq; applicability at exponent (n+1)/n was confirmed in Lean.
- Rademacher: LipschitzWith.ae_differentiableAt; Lebesgue: Monotone.ae_differentiableAt.
- MonotoneOn.intervalIntegral_deriv_mem_uIcc and MonotoneOn.intervalIntegrable_deriv.
- ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (values in any complete normed space) and HasCompactSupport.contDiff_convolution_left.
- eLpNorm_indicator_const' (every p ≠ 0, including ⊤) and eLpNorm_lim_le_liminf_eLpNorm (every p).
- Measure.addHaar_ball / addHaar_sphere; measurable_fderiv; norm_fderiv_le_of_lipschitz; fderiv_of_notMem_tsupport.
- IsCompact.exists_cthickening_subset_open and cthickening_empty.
- PiLp.volume_preserving_toLp with volume_preserving_funUnique; integral_inner; HasDerivAt.rpow_const; Filter.Tendsto.limUnder_eq.

Several of these lie outside the contract's import closure; the child proofs carry implementation notes naming the modules to import.

Lean evidence: listed in the rationale; all checks use only standard axioms apart from the stubs' sorryAx.
