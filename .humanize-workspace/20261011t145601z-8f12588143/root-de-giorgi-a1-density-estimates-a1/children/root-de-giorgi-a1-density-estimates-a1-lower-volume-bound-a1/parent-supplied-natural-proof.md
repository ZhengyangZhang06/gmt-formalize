# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1.density_estimates-a1`
- Child DAG node: `root.de_giorgi-a1.density_estimates-a1.lower_volume_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 8 (i)-(iii) (Simon (10), (11), chapter-03.txt lines 706-733), for an arbitrary Gauss-Green pair (μ, ν) of (U, G) and an arbitrary vector w; the parent applies it to (G, ν, w) = (E, ν, e) and to (U ∖ E, −ν, −e) (erratum E5). Notation: N = n + 1, B_r := B_r(x), B̄_r := closed ball, V(r) := L^N(G ∩ B_r).toReal, m(r) := μ(B_r).toReal.

0. Let c_F > 0 be the constant given by sibling ball_isoperimetric for n, put K := 3c_F > 0 and c := (1/((n + 1)K))^{n+1} > 0 (c depends only on n).

1. V is finite and non-decreasing on ℝ. For r ∈ (0, ρ₁): B̄_r ⊆ B_{ρ₁} ⊆ U, so μ(B_r) ≤ μ(B̄_r) < ∞ (B̄_r is a compact subset of U); together with μ(B_r) > 0 (hypothesis) this gives m(r) > 0.

2. ((i) Positivity.) Let r ∈ (0, ρ₁) and suppose V(r) ≤ 0. Then V(t) = 0 for all t ≤ r (0 ≤ V(t) ≤ V(r)). Put r' := r/2 ∈ (0, ρ₁). V vanishes on the open neighbourhood (−∞, r) of r', so V has derivative 0 at r'. Sibling first_variation_bound at r' (B̄_{r'} ⊆ U, |w| ≤ 1, d = 0) gives ∫_{B_{r'}} ⟨ν, w⟩ dμ ≤ 0, whereas the hypothesis and step 1 give 0 < m(r') ≤ 2∫_{B_{r'}} ⟨ν, w⟩ dμ — a contradiction. Hence V(r) > 0, and so L^N(G ∩ B_r) > 0, for every r ∈ (0, ρ₁).

3. ((ii) Differential inequality.) By Mathlib Monotone.ae_differentiableAt, V is differentiable at L¹-a.e. r. For such r ∈ (0, ρ₁), with d := V'(r): first_variation_bound gives ∫_{B_r} ⟨ν, w⟩ dμ ≤ d, so m(r) ≤ 2d by hypothesis; and ball_isoperimetric (B̄_r ⊆ U, L^N(G ∩ B_r) > 0 by step 2, V has derivative d at r) gives V(r)^{n/(n+1)} ≤ c_F (m(r) + d) ≤ c_F (2d + d) = K d.

4. ((iii) Integration.) Sibling ode_lower_bound, applied to n, K, ρ₁ and V (non-decreasing on (0, ρ₁), positive there by step 2, with the a.e. hypothesis provided by step 3), yields V(ρ) ≥ (ρ/((n + 1)K))^{n+1} = c ρ^{n+1} for every ρ ∈ (0, ρ₁).

5. Since L^N(G ∩ B_ρ) < ∞, L^N(G ∩ B_ρ(x)) = ENNReal.ofReal(V(ρ)) ≥ ENNReal.ofReal(c ρ^{n+1}). ∎

## Key steps

1. c := (3(n+1)c_F)^{−(n+1)} with c_F from sibling ball_isoperimetric.
2. Positivity: if L^N(G ∩ B_r) = 0, V vanishes near r/2, so V'(r/2) = 0 and sibling first_variation_bound contradicts 0 < μ(B_{r/2}) ≤ 2∫_{B_{r/2}}⟨ν, w⟩dμ.
3. At a.e. r: first_variation_bound gives μ(B_r) ≤ 2V'(r); ball_isoperimetric gives V^{n/(n+1)} ≤ c_F(μ(B_r) + V') ≤ 3c_F V'.
4. Sibling ode_lower_bound integrates this to V(ρ) ≥ cρ^{n+1}; convert to ENNReal.

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
