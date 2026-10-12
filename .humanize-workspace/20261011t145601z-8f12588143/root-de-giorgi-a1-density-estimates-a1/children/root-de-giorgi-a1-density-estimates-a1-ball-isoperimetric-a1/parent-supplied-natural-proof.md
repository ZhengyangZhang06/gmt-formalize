# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1.density_estimates-a1`
- Child DAG node: `root.de_giorgi-a1.density_estimates-a1.ball_isoperimetric-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 8(ii) (Simon, chapter-03.txt lines 706-722: 'replacing ζ by a sequence ζ_k as in (4), we get for a.e. ρ: L^{n+1}(E ∩ B_ρ)^{n/(n+1)} ≤ c(μ_E(B_ρ) + d/dρ L^{n+1}(E ∩ B_ρ))'), at a single radius ρ, with the cut-offs indexed by s ∈ (0, ρ). Notation: B_r := B_r(x), B̄_r := closed ball, V(r) := L^N(G ∩ B_r).toReal (finite since L^N(B_r) < ∞, and non-decreasing in r), a := n/(n + 1) ≥ 0, p := (n + 1)/n ∈ ℝ≥0∞.

0. Let c > 0 be the constant given by sibling sobolev_indicator for this n. Note p ≠ 0 and 1/p.toReal = a in both cases: for n = 0, p = ∞, p.toReal = 0 and 1/0 = 0 = a (Lean conventions); for n ≥ 1, p.toReal = (n + 1)/n.

1. μ(B_ρ) ≤ μ(B̄_ρ) < ∞ because B̄_ρ is a compact subset of U. V(ρ) > 0 because 0 < L^N(G ∩ B_ρ) < ∞.

2. (Inequality at an inner radius.) Fix s ∈ (0, ρ) with L^N(G ∩ B_s) > 0, and let ζ_s be the function given by sibling radial_cutoff for (x, s, ρ). Since ζ_s ≥ 0 is Lipschitz with compact support and tsupport ζ_s ⊆ B̄_ρ ⊆ U, sobolev_indicator gives
 eLpNorm(G.indicator ζ_s, p) ≤ ENNReal.ofReal(c (∫ ζ_s dμ + ∫_G |Dζ_s|)).
 (a) ∫_G |Dζ_s| = (V(ρ) − V(s))/(ρ − s) by radial_cutoff (applied to G); this is ≥ 0 since V is non-decreasing.
 (b) 0 ≤ ζ_s ≤ 1_{B_ρ} pointwise (ζ_s ≤ 1, and ζ_s = 0 outside B_ρ). ζ_s is μ-integrable (continuous and bounded by 1_{B̄_ρ}, with μ(B̄_ρ) < ∞) and 1_{B_ρ} is μ-integrable, so ∫ ζ_s dμ ≤ ∫ 1_{B_ρ} dμ = μ(B_ρ).toReal.
 (c) For every y, |1_{G∩B_s}(y)| ≤ |(G.indicator ζ_s)(y)|, since ζ_s = 1 on B_s. By monotonicity of eLpNorm (Mathlib eLpNorm_mono) and Mathlib eLpNorm_indicator_const' (valid for every p ≠ 0, including p = ∞, because L^N(G ∩ B_s) ≠ 0): L^N(G ∩ B_s)^a = eLpNorm(1_{G∩B_s}, p) ≤ eLpNorm(G.indicator ζ_s, p).
 Combining (a)-(c), and passing to real numbers (all quantities are finite, c(∫ ζ_s dμ + (V(ρ) − V(s))/(ρ − s)) ≥ 0, and (L^N(G ∩ B_s)^a).toReal = V(s)^a), we get
 (∗) V(s)^a ≤ c (μ(B_ρ).toReal + (V(ρ) − V(s))/(ρ − s)).

3. (Limit s ↑ ρ.) V is differentiable at ρ, hence continuous there, so V(s) → V(ρ) > 0 as s → ρ⁻; in particular V(s) > 0, i.e. L^N(G ∩ B_s) > 0, for all s in some interval (ρ − η, ρ) ∩ (0, ρ), and (∗) holds for these s. Moreover V(s)^a → V(ρ)^a (t ↦ t^a is continuous at t = V(ρ) > 0; Mathlib Tendsto.rpow_const), and (V(ρ) − V(s))/(ρ − s) = (V(s) − V(ρ))/(s − ρ) → d as s → ρ⁻ (Mathlib hasDerivAt_iff_tendsto_slope). Passing to the limit in (∗) along 𝓝[<]ρ (Mathlib le_of_tendsto_of_tendsto) gives V(ρ)^a ≤ c (μ(B_ρ).toReal + d), i.e. L^N(G ∩ B_ρ(x)).toReal^{n/(n+1)} ≤ c (μ(B_ρ(x)).toReal + d). ∎

## Key steps

1. Take c from sibling sobolev_indicator; with p = (n+1)/n, 1/p.toReal = n/(n+1) (also for n = 0, where p = ∞).
2. For s ∈ (0, ρ) with L^N(G ∩ B_s) > 0, apply sobolev_indicator to the cut-off ζ_s of sibling radial_cutoff: ∫_G|Dζ_s| = (V(ρ) − V(s))/(ρ − s), ∫ζ_s dμ ≤ μ(B_ρ), and eLpNorm(χ_Gζ_s, p) ≥ eLpNorm(1_{G∩B_s}, p) = L^N(G ∩ B_s)^{n/(n+1)}.
3. Hence V(s)^{n/(n+1)} ≤ c(μ(B_ρ) + (V(ρ) − V(s))/(ρ − s)) for s near ρ.
4. Let s ↑ ρ: V is continuous at ρ with V(ρ) > 0, rpow is continuous there, and the difference quotient tends to d.

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
