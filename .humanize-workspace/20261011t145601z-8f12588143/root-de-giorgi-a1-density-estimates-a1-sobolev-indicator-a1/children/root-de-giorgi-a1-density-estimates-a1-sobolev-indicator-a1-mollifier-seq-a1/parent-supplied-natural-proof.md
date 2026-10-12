# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1.density_estimates-a1.sobolev_indicator-a1`
- Child DAG node: `root.de_giorgi-a1.density_estimates-a1.sobolev_indicator-a1.mollifier_seq-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

(Implementation note: ContDiffBump.normed and its lemmas live in Mathlib.Analysis.Calculus.BumpFunction.Normed, and ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable lives in Mathlib.Analysis.Calculus.BumpFunction.Convolution; neither is in the contract's import closure, so these modules must be imported by the proof. The pinned SimonGMT module Poincare.SimonGMT.Chapter08.DistributionalConstancy already defines exactly the bump family of step 1 on Euclidean N = Rn N (constancyMollifier r hr k, with rIn = r/(k+1)/2 and rOut = r/(k+1)) and proves step 5 for it (ae_constancyMollifier_convolution_tendsto, with the convolution written f ⋆ φ; axioms propext, Classical.choice, Quot.sound only); it may be reused; in that f ⋆ φ order, u_j(y) = (χ_G ⋆ ρ_j)(y) = ∫ χ_G(t)ρ_j(y − t) dt follows directly from convolution_def and integral_indicator₀, so the swap of step 2 is not needed.)
Source: parent proof Step 1 (u_σ := φ_σ * χ_G with 0 ≤ u_σ ≤ 1 and u_σ Lipschitz) and Step 3 (u_{σ_j} → χ_G L^N-a.e. by the Lebesgue differentiation theorem for mollifiers, and ∫ u_{σ_j}|Dζ| → ∫_G |Dζ| by dominated convergence), with the radii s_j := r/(j + 1) in place of σ_j; the mollifiers are those of Simon Ch. 2, §2 (chapter-02.txt lines 531-545). Notation: s_j := r/(j + 1) > 0; B_j := B̄_{s_j}(0); (f ⋆ g)(y) := ∫ f(t) g(y − t) dt is Mathlib's convolution with the bilinear map lsmul ℝ ℝ (multiplication); χ_G := G.indicator 1; Dv(x) := fderiv ℝ v x. No step uses N ≥ 1.

1. (Construction.) For j ∈ ℕ let φ_j be Mathlib's smooth bump function centred at 0 with inner radius s_j/2 and outer radius s_j (a ContDiffBump (0 : ℝ^N) with rIn = s_j/2 < rOut = s_j), and put ρ_j := φ_j.normed L^N = φ_j / ∫ φ_j dL^N. Since L^N is locally finite and positive on non-empty open sets, Mathlib gives: ρ_j is C^∞, in particular C¹ (ContDiffBump.contDiff_normed); ρ_j ≥ 0 (nonneg_normed); ∫ ρ_j dL^N = 1 (integral_normed); tsupport ρ_j = B̄_{s_j}(0) = B_j (tsupport_normed_eq); and ρ_j has compact support (hasCompactSupport_normed). These are the five properties required of the ρ_j.

Now fix a Lebesgue null-measurable G ⊆ ℝ^N. The function χ_G is bounded by 1 and a.e.-strongly measurable, hence locally integrable.

2. (Convolution form.) For all j and y, u_j(y) = ∫ ρ_j(y − z) χ_G(z) dz = (ρ_j ⋆ χ_G)(y). Indeed ∫_G f dL^N = ∫ χ_G f dL^N for null-measurable G (integral_indicator₀), and (ρ_j ⋆ χ_G)(y) = ∫ ρ_j(t) χ_G(y − t) dt = ∫ ρ_j(y − z) χ_G(z) dz by the measure-preserving substitution z = y − t (convolution_eq_swap).

3. (Bounds (ii).) Since ρ_j ≥ 0, the integrand of u_j(y) is non-negative, so u_j(y) ≥ 0. The function z ↦ ρ_j(y − z) is non-negative and integrable, so u_j(y) = ∫_G ρ_j(y − z) dz ≤ ∫ ρ_j(y − z) dz = ∫ ρ_j dL^N = 1, the middle equality by invariance of L^N under z ↦ y − z (integral_sub_left_eq_self).

4. (Lipschitz (i).) Dρ_j is continuous (ρ_j is C¹) and vanishes off the compact set tsupport ρ_j (fderiv_of_notMem_tsupport; HasCompactSupport.fderiv), so A_j := sup_x ‖Dρ_j(x)‖ < ∞, and by the mean value inequality |ρ_j(a) − ρ_j(b)| ≤ A_j |a − b| for all a, b. For y, y' ∈ ℝ^N,
 |u_j(y) − u_j(y')| ≤ ∫_G |ρ_j(y − z) − ρ_j(y' − z)| dz ≤ ∫ |ρ_j(y − z) − ρ_j(y' − z)| dz.
The last integrand is at most A_j |y − y'| and vanishes unless y − z ∈ B_j or y' − z ∈ B_j, i.e. unless z ∈ (y − B_j) ∪ (y' − B_j), a set of Lebesgue measure at most 2 L^N(B_j) < ∞. Hence |u_j(y) − u_j(y')| ≤ 2 A_j L^N(B_j) |y − y'|, so u_j is Lipschitz with constant L_j := 2 A_j L^N(B_j) ∈ ℝ≥0. (Equivalently: by Mathlib HasCompactSupport.hasFDerivAt_convolution_left, u_j = ρ_j ⋆ χ_G is differentiable everywhere with Du_j(y)k = ∫ (Dρ_j(t)k) χ_G(y − t) dt, so ‖Du_j(y)‖ ≤ ∫ ‖Dρ_j‖ dL^N for all y, and u_j is Lipschitz with this constant by lipschitzWith_of_nnnorm_fderiv_le.) In particular every u_j is continuous.

5. (a.e. convergence (iii).) rOut(φ_j) = s_j → 0 as j → ∞, and rOut(φ_j) = 2·rIn(φ_j) for every j. L^N is an additive Haar measure on the finite-dimensional space ℝ^N and χ_G is locally integrable, so Mathlib's Lebesgue differentiation theorem for mollifiers, ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (with ratio constant K = 2), gives (ρ_j ⋆ χ_G)(y) → χ_G(y) as j → ∞ for L^N-a.e. y. By step 2 this is (iii).

6. (Weak convergence (iv).) Let h be L^N-integrable. For each j the function y ↦ u_j(y) h(y) is a.e.-strongly measurable (u_j is continuous by step 4, h is a.e.-strongly measurable) and |u_j(y) h(y)| ≤ |h(y)| for all y by (ii); by (iii), u_j h → χ_G h L^N-a.e. By dominated convergence with the integrable bound |h|, ∫ u_j h dL^N → ∫ χ_G h dL^N = ∫_G h dL^N (integral_indicator₀). This is (iv). ∎

## Key steps

1. ρ_j := normalized ContDiffBump at 0 with radii s_j/2 < s_j, s_j = r/(j+1): C¹, ≥ 0, ∫ρ_j = 1, tsupport ρ_j = B̄_{s_j}(0), compact support.
2. u_j(y) = ∫_G ρ_j(y − z)dz = (ρ_j ⋆ χ_G)(y) (convolution_eq_swap, integral_indicator₀).
3. 0 ≤ u_j(y) ≤ ∫ρ_j(y − z)dz = 1 (translation invariance).
4. u_j is Lipschitz with constant 2·sup‖Dρ_j‖·L^N(B̄_{s_j}(0)) (or via ‖Du_j‖ ≤ ∫‖Dρ_j‖).
5. u_j → χ_G L^N-a.e. by ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (rOut = 2·rIn → 0).
6. ∫u_j h → ∫_G h by dominated convergence with bound |h|.

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
