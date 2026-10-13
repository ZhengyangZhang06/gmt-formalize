# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1.density_estimates-a1.lipschitz_sobolev-a1`
- Child DAG node: `root.de_giorgi-a1.density_estimates-a1.lipschitz_sobolev-a1.one_dim_smooth-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

(Implementation notes: every lemma named below is already in the import closure of GMT.Ch03.Submission. For reference:
- HasCompactSupport.integral_Iic_deriv_eq and integral_Ioi_of_hasDerivAt_of_tendsto' are in Mathlib.MeasureTheory.Integral.IntegralEqImproper.
- intervalIntegral.integral_Iic_add_Ioi is in Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic.
- PiLp.volume_preserving_toLp is in Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace.
- volume_preserving_funUnique is in Mathlib.MeasureTheory.Constructions.Pi.
Parenthesize sums of set integrals: `∫ s in Iic t, g s + ∫ s in Ioi t, g s` parses as one integral of a sum, so write `(∫ s in Iic t, g s) + ∫ s in Ioi t, g s`.)
Source: parent proof Step 2 (Simon Ch. 3, proof of Theorem 4.3, Step 7 'Constants', erratum E6). For N = 1 the Sobolev inequality is replaced by sup|w| ≤ ½∫|w'|, which follows from w(t) = ∫_{−∞}^t w' = −∫_t^∞ w'. Notation: ℝ^1 := Rn 1 = EuclideanSpace ℝ (Fin 1) with its volume L^1; Dv(y) := fderiv ℝ v y, with operator norm ‖Dv(y)‖.

Let v : ℝ^1 → ℝ be C¹ with compact support.
1. (Parametrisation.) Let e₀ := EuclideanSpace.single 0 1 ∈ ℝ^1, so ‖e₀‖ = 1. Let ι : ℝ →L[ℝ] ℝ^1 be the continuous linear map ι(t) = t·e₀ (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) e₀). Then ‖ι(t)‖ = |t|·‖e₀‖ = |t|, so ι is an isometry and hence a closed embedding (Isometry.isClosedEmbedding; ℝ is complete). Every y ∈ ℝ^1 satisfies y = ι(y 0), because y and (y 0)·e₀ have the same unique coordinate.
2. (Measure preservation.) Let E := (MeasurableEquiv.funUnique (Fin 1) ℝ).symm.trans (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)), the measurable equivalence t ↦ toLp 2 (fun _ ↦ t). Comparing the single coordinate shows that ι agrees with E pointwise. E is measure preserving from Lebesgue measure on ℝ to L^1, being the composite of (volume_preserving_funUnique (Fin 1) ℝ).symm and PiLp.volume_preserving_toLp (Fin 1). Hence, by MeasurePreserving.integral_comp', ∫_ℝ ‖Dv(ι t)‖ dt = ∫_{ℝ^1} ‖Dv(y)‖ dL^1(y).
3. (The one-variable function.) Let f := v ∘ ι : ℝ → ℝ. f is C¹, as the composition of v with the smooth map ι, and has compact support (HasCompactSupport.comp_isClosedEmbedding with step 1). ι has derivative e₀ at every t, so by the chain rule (HasFDerivAt.comp_hasDerivAt) f'(t) := deriv f t = Dv(ι t)(e₀). Hence |f'(t)| ≤ ‖Dv(ι t)‖·‖e₀‖ = ‖Dv(ι t)‖ (ContinuousLinearMap.le_opNorm).
4. (Integrability and comparison.) f' is continuous (ContDiff.continuous_deriv) with compact support (HasCompactSupport.deriv), hence integrable on ℝ. The function t ↦ ‖Dv(ι t)‖ is continuous. It has compact support: y ↦ ‖Dv(y)‖ has compact support because Dv vanishes off tsupport v, and composing with the closed embedding ι preserves compact support. Hence it is integrable. By step 3 and monotonicity of the integral, ∫_ℝ |f'| ≤ ∫_ℝ ‖Dv(ι t)‖ dt, which equals ∫_{ℝ^1} ‖Dv‖ dL^1 by step 2.
5. (FTC from the left.) Since f is C¹ with compact support, ∫_{(−∞,t]} f'(s) ds = f(t) for every t (HasCompactSupport.integral_Iic_deriv_eq). Hence |f(t)| ≤ ∫_{(−∞,t]} |f'(s)| ds (norm_integral_le_integral_norm).
6. (FTC from the right.) f vanishes outside a compact set, so f(s) = 0 for all sufficiently large s, and f(s) → 0 as s → +∞ (atTop ≤ cocompact). f is differentiable everywhere and f' is integrable on (t, ∞), so integral_Ioi_of_hasDerivAt_of_tendsto' gives ∫_{(t,∞)} f'(s) ds = 0 − f(t). Hence |f(t)| = |∫_{(t,∞)} f'| ≤ ∫_{(t,∞)} |f'(s)| ds.
7. (Adding the two bounds.) |f'| is integrable on (−∞, t] and on (t, ∞), and these two sets partition ℝ, so ∫_{(−∞,t]} |f'| + ∫_{(t,∞)} |f'| = ∫_ℝ |f'| (intervalIntegral.integral_Iic_add_Ioi). With steps 5, 6 and 4 this gives 2|f(t)| ≤ ∫_ℝ |f'| ≤ ∫_{ℝ^1} ‖Dv‖ dL^1. That is, |f(t)| ≤ ½ ∫ ‖Dv‖ dL^1 for every t ∈ ℝ.
8. (Pointwise bound on ℝ^1.) For y ∈ ℝ^1, step 1 gives v(y) = v(ι(y 0)) = f(y 0). So |v(y)| ≤ ½ ∫ ‖Dv‖ dL^1 for every y ∈ ℝ^1.
9. (Essential supremum.) v is continuous, hence a.e. strongly measurable, so eLpNorm v ∞ L^1 = eLpNormEssSup v L^1 (eLpNorm_exponent_top). The bound of step 8 holds everywhere, in particular a.e., so eLpNormEssSup v L^1 ≤ ENNReal.ofReal(½ ∫ ‖Dv‖ dL^1) (eLpNormEssSup_le_of_ae_bound). ∎

## Key steps

1. ι(t) = t • EuclideanSpace.single 0 1 is an isometric, measure-preserving parametrisation of Rn 1 (it agrees with toLp 2 ∘ (funUnique (Fin 1) ℝ).symm), so ∫_ℝ ‖Dv(ι t)‖ = ∫_{Rn 1} ‖Dv‖ and y = ι(y 0).
2. f := v ∘ ι is C¹ with compact support and |f'(t)| = |Dv(ι t) e₀| ≤ ‖Dv(ι t)‖, so ∫|f'| ≤ ∫‖Dv‖.
3. f(t) = ∫_{Iic t} f' = −∫_{Ioi t} f' (compact-support FTC on both sides).
4. 2|f(t)| ≤ ∫_{Iic t}|f'| + ∫_{Ioi t}|f'| = ∫|f'| ≤ ∫‖Dv‖, so |v(y)| ≤ ½∫‖Dv‖ for every y.
5. The pointwise bound gives eLpNorm v ∞ = eLpNormEssSup v ≤ ofReal(½∫‖Dv‖).

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch03/Contract.lean GMT/Ch03/Contract.lean; cmp <snapshot>/project/GMT/Ch03/Submission.lean GMT/Ch03/Submission.lean`
- `grep -n -A12 'theorem eLpNorm_le_eLpNorm_fderiv_one|theorem eLpNorm_le_eLpNorm_fderiv_of_eq' <snapshot>/mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean (and lines 290-460: variables, eLpNormLESNormFDerivOneConst, lintegral_pow_le_pow_lintegral_fderiv_aux)`
- `grep -n -A8 'theorem eLpNorm_lim_le_liminf_eLpNorm' <snapshot>/mathlib/Mathlib/MeasureTheory/Function/LpSpace/Complete.lean; grep -n '^namespace' same file`
- `grep -n -A10 'theorem tendsto_integral_of_dominated_convergence' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `rg -n 'IsCompact\.cthickening|theorem aestronglyMeasurable_of_tendsto_ae|volume_preserving_toLp|Continuous\.integrable_of_hasCompactSupport' <snapshot>/mathlib/Mathlib`
- `rg -n 'abbrev HolderConjugate|structure HolderTriple' <snapshot>/mathlib/Mathlib (found Mathlib/Basic/Real/ConjExponents.lean)`
- `rg -n 'lintegral_Ici_deriv|lintegral_Iic_deriv' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral <snapshot>/mathlib/Mathlib/Analysis/Calculus; sed -n 975,1060p IntegralEqImproper.lean`
- `rg -n 'integral_Iic_add_Ioi' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral`
- `grep -n 'fderiv_of_notMem_tsupport|HasCompactSupport.fderiv' <snapshot>/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `grep -n 'eLpNorm_one_eq_lintegral_enorm|eLpNorm_exponent_top|eLpNormEssSup_le_of_ae_bound|ofReal_integral_norm_eq_lintegral_enorm' in LpSeminorm/Defs.lean, LpSeminorm/Basic.lean, Integral/Bochner/Basic.lean`
- `grep -n 'volume_preserving_funUnique|def funUnique|MeasurePreserving.integral_comp' in Constructions/Pi.lean, MeasurableSpace/Embedding.lean, Integral/Bochner/Basic.lean; sed -n 118,175p Measure/Haar/InnerProductSpace.lean`
- `rg -n 'EuclideanSpace.single|norm_single' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `rg -n 'theorem cthickening_mono|TendstoUniformly.tendsto_at|HasFDerivAt.comp_hasDerivAt|ContDiff.continuous_deriv|Isometry.isClosedEmbedding|isometry_of_norm|indicator_of_notMem|integrableOn_const' in the corresponding Mathlib files`
- `grep -c deGiorgiDensSob .humanize/.../dag.json; grep -rn deGiorgiDensSob GMT/ .lake/packages/simongmt`
- `python3 -I byte-identity check of the parent/sibling frozen types (handoff, dag.json) against the assembly file`
- `lake env lean GMT/Scratch/LipschitzSobolevSplit{Assembly,ChildProofs,FullCheck,Imports}.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Ch03/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1-lipschitz-sobolev-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Basic/Real/ConjExponents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/LpSpace/Complete.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/ContDiff/Deriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Group/Uniform.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Algebra/Notation/Indicator.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/LipschitzSobolevSplitAssembly.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/LipschitzSobolevSplitChildProofs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/LipschitzSobolevSplitFullCheck.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/LipschitzSobolevSplitImports.lean`

The snapshot's `Contract.lean` and `Submission.lean` are byte-identical to the workspace (project d09bc8a, Mathlib 25730c7c).

Library facts that are available and confirmed in Lean:
- GNS: `eLpNorm_le_eLpNorm_fderiv_one` takes `NNReal.HolderConjugate (finrank ℝ E) p` with p : ℝ≥0 and has constant `eLpNormLESNormFDerivOneConst μ p`. It is applicable at p = (n+1)/n because (p : ℝ≥0∞) = (n+1)/n for n ≠ 0.
- Compact-support FTC: `HasCompactSupport.integral_Iic_deriv_eq`, `integral_Ioi_of_hasDerivAt_of_tendsto'` and `intervalIntegral.integral_Iic_add_Ioi`. There is also `HasCompactSupport.enorm_le_lintegral_Ici_deriv`, but it has constant 1, not 1/2.
- ℝ ≅ ℝ^1 measure preservation: `PiLp.volume_preserving_toLp` composed with `(volume_preserving_funUnique (Fin 1) ℝ).symm`.
- Fatou for eLpNorm is `MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm`. It sits in namespace `MeasureTheory.Lp` and needs `AEStronglyMeasurable` of the limit, supplied by `aestronglyMeasurable_of_tendsto_ae`.
- Also used: `tendsto_integral_of_dominated_convergence`, `fderiv_of_notMem_tsupport`, `HasCompactSupport.fderiv`, `IsCompact.cthickening`, `Metric.cthickening_mono`, `TendstoUniformly.tendsto_at`, `eLpNorm_one_eq_lintegral_enorm`, `ofReal_integral_norm_eq_lintegral_enorm`, `eLpNorm_exponent_top` and `eLpNormEssSup_le_of_ae_bound`.
- Only `Mathlib.Analysis.FunctionalSpaces.SobolevInequality` lies outside the import closure of `GMT.Ch03.Submission`.

Not in Mathlib or the pinned SimonGMT, so these become the children:
- the GNS bound for C¹_c functions in the form ofReal(c∫‖Dv‖) at exponent (n+1)/n;
- the one-dimensional endpoint inequality sup|v| ≤ ½∫‖Dv‖ on `Rn 1`;
- the Fatou/dominated-convergence closure lemma.

No name collisions: `deGiorgiDensSob` appears nowhere in dag.json, GMT/ or simongmt.

All three children were proved in scratch using only the standard axioms. The assembly proves the frozen parent from the children plus the sibling `deGiorgiDens_lipschitz_smooth_approx`.
