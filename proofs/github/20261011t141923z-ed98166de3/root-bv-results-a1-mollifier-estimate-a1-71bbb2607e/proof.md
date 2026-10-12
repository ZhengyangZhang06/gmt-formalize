# Parent-supplied natural-language proof

- Parent DAG node: `root.bv_results-a1`
- Child DAG node: `root.bv_results-a1.mollifier_estimate-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Section T, step T7 (translation and mollification estimate: “for |z| ≤ σ: ∫_Q |u(x − z) − u(x)| dx ≤ |z||Du|(W), and ∫_Q |u_σ − u| ≤ σ|Du|(W)”). Simon's printed proof of Theorem 2.6 uses this estimate when it reduces precompactness in L¹_loc to the smooth case via Lemma 2.5 and [GT01, Thm 7.22]. Here the kernel is an arbitrary continuous kernel ρ ≥ 0 with ∫ρ = 1 and support in B(0,σ). The hypothesis Q + B̄(0,3σ) ⊆ W of the parent is relaxed to closedBall(x,σ) ⊆ W for x ∈ Q; the proof below uses the strict inequality ‖z‖ < σ, valid on the support of ρ.

Notation. E := ℝⁿ = EuclideanSpace ℝ (Fin n), μ := volume (translation invariant). F := 1_W u = W.indicator u. For a kernel κ, κ * G := convolution κ G (lsmul ℝ ℝ) volume, i.e. (κ * G)(x) = ∫ κ(t) G(x − t) dt. Dh := fderiv ℝ h. |Du|(W) := Chapter02.bvVariationOn u W.

0. Preliminaries. W is open, hence measurable, so F ∈ L¹(E). Since ∫ρ = 1, ρ ≢ 0, so B(0,σ) ≠ ∅ and σ > 0. ρ is continuous with support in B(0,σ), hence bounded and integrable. Put M := |Du|(W). If M = ∞ the right side is ofReal(σ)·∞ = ∞ (because ofReal σ ≠ 0), and there is nothing to prove. Assume M < ∞.

1. Translation estimate. Claim: for every z ∈ E with ‖z‖ < σ,
   ∫⁻_Q |F(x − z) − F(x)| dx ≤ ofReal(‖z‖)·M.
 (a) Smooth approximants. Let m₀ := σ − ‖z‖ > 0 and τ_j := m₀/(j + 2) for j ∈ ℕ, so τ_j → 0. Let ψ_j be a C^∞ kernel with ψ_j ≥ 0, support ψ_j ⊆ B(0,τ_j) and ∫ψ_j = 1; e.g. ψ_j := c_j.normed volume for the ContDiffBump c_j centred at 0 with rIn = τ_j/2 and rOut = τ_j (Mathlib contDiff_normed, continuous_normed, nonneg_normed, support_normed_eq, integral_normed). Let w_j := ψ_j * F. It is C^∞ (HasCompactSupport.contDiff_convolution_left), in particular C², and ψ_j is C².
 (b) Gradient bound on translates of Q. For s ∈ [0,1] let Q_s := {x − s z : x ∈ Q}, a measurable set (a translate of Q). If y = x − s z with x ∈ Q, then
   closedBall(y,τ_j) ⊆ closedBall(x, s‖z‖ + τ_j) ⊆ closedBall(x,σ) ⊆ W,
 because s‖z‖ + τ_j ≤ ‖z‖ + m₀ = σ. So the sibling theorem Submission.bv_mollifier_fderiv_lintegral_le (with W, K := Q_s, u, kernel ψ_j and radius τ_j) gives
   ∫⁻_{Q_s} ‖Dw_j(y)‖ₑ dy ≤ M   for every s ∈ [0,1] and every j.
 (c) Fundamental theorem of calculus. For each x, the C¹ function s ↦ w_j(x − s z) has derivative −Dw_j(x − s z)[z]. So
   w_j(x − z) − w_j(x) = −∫_0^1 Dw_j(x − s z)[z] ds,  hence  |w_j(x − z) − w_j(x)| ≤ ‖z‖ ∫_0^1 ‖Dw_j(x − s z)‖ ds.
 The function (x,s) ↦ ‖Dw_j(x − s z)‖ is continuous. By Tonelli (lintegral_lintegral_swap) and translation invariance (∫⁻_Q f(x − s z) dx = ∫⁻_{Q_s} f(y) dy),
   ∫⁻_Q |w_j(x − z) − w_j(x)| dx ≤ ofReal‖z‖ · ∫⁻_{s∈[0,1]} ∫⁻_{Q_s} ‖Dw_j‖ₑ dy ds ≤ ofReal‖z‖ · M.
 (d) Limit j → ∞. By the sibling theorem Submission.bv_mollifier_tendsto_L1 (with F, kernels ψ_j, radii τ_j → 0), e_j := ∫⁻_E |w_j − F| → 0. By translation invariance,
   ∫⁻_Q |w_j(x − z) − F(x − z)| dx ≤ ∫⁻_E |w_j(y) − F(y)| dy = e_j,  and  ∫⁻_Q |w_j − F| ≤ e_j.
 By the pointwise triangle inequality |F(x − z) − F(x)| ≤ |F(x − z) − w_j(x − z)| + |w_j(x − z) − w_j(x)| + |w_j(x) − F(x)| and additivity of ∫⁻ for a.e.-measurable functions,
   ∫⁻_Q |F(x − z) − F(x)| dx ≤ 2e_j + ofReal‖z‖·M  for every j.
 Letting j → ∞ proves the claim.

2. Pointwise representation on Q. Let x ∈ Q. Then x ∈ closedBall(x,σ) ⊆ W, so F(x) = u(x). Since ρ is bounded with compact support and F ∈ L¹, t ↦ ρ(t)F(x − t) is integrable; and ∫ρ = 1. Therefore
   (ρ * F)(x) − u(x) = ∫ ρ(t)(F(x − t) − F(x)) dt,
 and, since ρ ≥ 0, in [0,∞]:
   ‖(ρ * F)(x) − u(x)‖ₑ ≤ ∫⁻ ofReal(ρ(t))·‖F(x − t) − F(x)‖ₑ dt.
 (Here ρ * F is exactly convolution ρ (W.indicator u) (lsmul ℝ ℝ) volume.)

3. Integration over Q and Tonelli. The function (x,t) ↦ ofReal(ρ(t))·‖F(x − t) − F(x)‖ₑ is a.e.-measurable on E × E: F is a.e.-strongly measurable and (x,t) ↦ x − t is quasi-measure-preserving. By step 2 and Tonelli (lintegral_lintegral_swap),
   ∫⁻_Q ‖ρ * F − u‖ₑ ≤ ∫⁻_t ofReal(ρ(t)) (∫⁻_Q ‖F(x − t) − F(x)‖ₑ dx) dt.
 If ρ(t) ≠ 0 then ‖t‖ < σ, so by step 1 the inner integral is ≤ ofReal(‖t‖)·M ≤ ofReal(σ)·M. If ρ(t) = 0 the integrand vanishes. Hence
   ∫⁻_Q ‖ρ * F − u‖ₑ ≤ ofReal(σ)·M·∫⁻ ofReal(ρ(t)) dt = ofReal(σ)·M,
 because ∫⁻ ofReal ρ = ofReal(∫ρ) = 1 (ofReal_integral_eq_lintegral_ofReal, ρ ≥ 0 integrable). This is the claim. ∎

## Key steps

1. Reduce to |Du|(W) = M < ∞; σ > 0 because ∫ρ = 1 and support ρ ⊆ B(0,σ).
2. Translation estimate for ‖z‖ < σ: mollify with C^∞ kernels ψ_j of radius τ_j ≤ σ − ‖z‖; FTC along segments + Tonelli + Submission.bv_mollifier_fderiv_lintegral_le on the translates Q − sz give ∫_Q |w_j(x−z) − w_j(x)| ≤ ‖z‖M.
3. Pass to F = 1_W u with Submission.bv_mollifier_tendsto_L1 and translation invariance: ∫_Q |F(x − z) − F(x)| ≤ ‖z‖M.
4. Write (ρ*F)(x) − u(x) = ∫ ρ(t)(F(x−t) − F(x)) dt for x ∈ Q, integrate over Q, Tonelli, and use ‖t‖ < σ on support ρ: total ≤ σM.

## Reference use

### local-project

Queries:
- `rg -n 'theorem (normed_neg|integral_normed|nonneg_normed|support_normed_eq|tsupport_normed_eq|hasCompactSupport_normed|contDiff_normed|continuous_normed)' mathlib/Mathlib/Analysis/Calculus/BumpFunction/`
- `rg -n 'contDiff_convolution_left|contDiff_convolution_right|hasFDerivAt_convolution_right' mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `rg -n 'convolution_tendsto_right' mathlib/Mathlib; rg -n 'notation.*convolution' mathlib/Mathlib/Analysis/Convolution.lean`
- `rg -in 'eLpNorm.*convolution|convolution.*eLpNorm|lintegral.*convolution|young' mathlib/Mathlib; rg -iln 'mollif' mathlib/Mathlib`
- `rg -n 'exists_hasCompactSupport' mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `rg -n 'theorem (integral_lineDeriv_mul_eq|ae_lineDeriv_sum_eq|ae_differentiableAt)' mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `rg -n 'def (infEdist|infEDist|infDist|cthickening|thickening)' mathlib/Mathlib/Topology/MetricSpace`
- `rg -n 'exists_cthickening_subset_open|exists_infDist_eq_dist|lineDeriv_eq_fderiv|addHaar_frontier|countable_meas_pos_of_disjoint|lintegral_lintegral_swap|integral_comp_comm|support_convolution_subset|lipschitzWith_of_hasCompactSupport|exists_contDiff_tsupport_subset|exists_contMDiffMap_one_nhds_of_subset_interior' mathlib/Mathlib`
- `grep -n 'theorem|def' simongmt/Poincare/SimonGMT/Chapter02/BV.lean, then a full read of BV.lean`
- `grep -n 'BV|2.6|2.7|2.8|open' project/GMT/Ch02/README.md; cmp project/GMT/Ch02/Contract.lean against the workspace GMT/Ch02/Contract.lean; rg -n 'Submission.|namespace Submission' project --glob '*.lean'`
- `lean Avail.lean: #check convolution, ContDiffBump, HasCompactSupport.contDiff_convolution_left, Metric.infDist, Metric.infEDist, lineDeriv, LipschitzWith.ae_differentiableAt, LipschitzWith.integral_lineDeriv_mul_eq, Convex.addHaar_frontier, gradient, Integrable.exists_hasCompactSupport_lintegral_sub_le after import GMT.Ch02.Submission`
- `python3 -I gen_checks.py (verifier gmt-compare.py contract_scope and child_modules plus lean_contract.validate_lean_statement), then lean on NodeChallenge_00..07.lean, AssemblyCheck.lean and Sanity.lean against a scratch olean of GMT.Ch02.Submission`
- `grep -rl for each of the 8 proposed lean_names in the run directory; list lean_name of every dag.json node and every nodes/*/decomposition-v1.json subproblem`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Convex/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1/parent-child-handoff.json`
- `/tmp/bvdecomp-tYsCkA/checks/NodeChallenge_00.lean`
- `/tmp/bvdecomp-tYsCkA/checks/NodeChallenge_07.lean`
- `/tmp/bvdecomp-tYsCkA/checks/AssemblyCheck.lean`
- `/tmp/bvdecomp-tYsCkA/checks/Sanity.lean`
- `/tmp/bvdecomp-tYsCkA/checks/Avail.lean`

The snapshot Contract.lean is byte-identical to the workspace contract and defines BVCompactness, BVPoincare and BVExtensionEstimate exactly as split. README rows 7–9 and the errata at lines 87 and 94–95 match the readings used: open W in 2.6; u ∈ L¹ in 2.7; and in 2.8, u = 0 a.e. off Ū with the conclusion encoded as |Du|(ℝⁿ∖Ū) = 0. The pinned SimonGMT BV.lean supplies the definitions and every lemma cited: euclideanDivergence_eq_sum_inner, measurable_euclideanDivergence, norm_euclideanDivergence_le_of_lipschitz, support_euclideanDivergence_subset, ofReal_integral_le_bvVariationOn, IsC1TestField.isLipschitzTestField, bvVariationOn_le_liminf_of_locallyL1, isLocallyBV_of_locallyL1_of_uniform_bound and isLocallyBV_zero. The snapshot Mathlib supplies the analytic tools: ContDiffBump.normed (contDiff_normed, nonneg_normed, support_normed_eq, integral_normed), HasCompactSupport.contDiff_convolution_left/right, hasFDerivAt_convolution_right, support_convolution_subset, LipschitzWith.integral_lineDeriv_mul_eq, LipschitzWith.ae_differentiableAt, DifferentiableAt.lineDeriv_eq_fderiv, Integrable.exists_hasCompactSupport_lintegral_sub_le, IsCompact.exists_cthickening_subset_open, IsClosed.exists_infDist_eq_dist, Convex.addHaar_frontier and Measure.countable_meas_pos_of_disjoint_iUnion. Mathlib has no lemma for L¹ convergence of mollifiers (no 'mollif' match and no convolution lemma with eLpNorm or lintegral), and no BV compactness, Poincaré or extension theorem, so those are genuine new obligations. In the frozen import closure, ContDiffBump.normed, gradient, Convex.addHaar_frontier and Integrable.exists_hasCompactSupport_lintegral_sub_le are unavailable (unknown field or constant). The child statements therefore use only convolution, kernel hypotheses that avoid ContDiffBump, fderiv, ball/closedBall and SimonGMT names; child proofs may add Mathlib imports to the Submission, which the verifier permits. With the comparator's own scope replay and statement validator, all 8 lean_statements elaborate and all 8 generated NodeChallenge modules compile. Sanity.lean confirms that normed ContDiffBumps satisfy the kernel hypotheses and that convolution ρ F (lsmul ℝ ℝ) volume x = ∫ t, ρ t * F (x - t). The assembly ⟨Submission.bv_compactness_theorem, Submission.bv_poincare_theorem, Submission.bv_extension_estimate_theorem⟩ type-checks against the selected type; apart from the sorry placeholders, it depends only on propext, Classical.choice and Quot.sound. The project snapshot has no Submission.* declarations, and neither dag.json nor any node file mentions the 8 proposed names, so none of them collides with a reserved declaration.
