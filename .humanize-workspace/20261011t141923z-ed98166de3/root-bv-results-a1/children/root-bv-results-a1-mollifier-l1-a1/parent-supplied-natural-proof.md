# Parent-supplied natural-language proof

- Parent DAG node: `root.bv_results-a1`
- Child DAG node: `root.bv_results-a1.mollifier_l1-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Section T, step T2 (L¹ convergence of mollifiers). The parent uses it in T7, T8 and B4, and it is the “convergence in L¹_loc is standard” part of Simon's printed Lemma 2.5. Here it is stated for an arbitrary sequence of continuous, nonnegative, normalized kernels with shrinking supports, instead of the dilates φ_σ of one fixed mollifier; the argument is the same.

Notation. E := ℝⁿ = EuclideanSpace ℝ (Fin n) and μ := volume (Lebesgue measure; it is invariant under translations and under x ↦ −x). For G : E → ℝ, (ρ_j * G)(x) := convolution (ρ j) G (lsmul ℝ ℝ) volume x = ∫ ρ_j(t)·G(x − t) dt, by definition of Mathlib's convolution. ‖·‖₁ denotes ∫⁻ |·| dμ ∈ [0,∞].

1. Properties of the kernels.
 Since ∫ρ_j = 1 ≠ 0, the function ρ_j is not identically 0, so B(0,σ_j) ≠ ∅ and σ_j > 0. Because ρ_j is continuous with support in B(0,σ_j), we have tsupport ρ_j ⊆ closedBall(0,σ_j), which is compact. Hence ρ_j is bounded and integrable, and ∫|ρ_j| = ∫ρ_j = 1.

2. Pointwise existence, linearity and the L¹ contraction.
 Let G ∈ L¹(μ). For every x, t ↦ G(x − t) is integrable (μ is invariant under t ↦ x − t) and ρ_j is bounded and measurable. So t ↦ ρ_j(t)G(x − t) is integrable, and (ρ_j * G)(x) is an absolutely convergent integral. In particular G ↦ (ρ_j * G)(x) is linear on L¹.
 Moreover, by Tonelli and translation invariance,
   ∫⁻ |(ρ_j * G)(x)| dx ≤ ∫⁻∫⁻ ρ_j(t)|G(x − t)| dt dx = ∫⁻ ρ_j(t) (∫⁻ |G(x − t)| dx) dt = (∫ρ_j)·‖G‖₁ = ‖G‖₁.
 The joint measurability of (x,t) ↦ ρ_j(t)|G(x − t)| holds because G is a.e.-strongly measurable and (x,t) ↦ x − t is quasi-measure-preserving (Mathlib AEStronglyMeasurable.comp_quasiMeasurePreserving / quasiMeasurePreserving_sub).

3. Approximation of F. Fix ε > 0 (real). By density of continuous compactly supported functions in L¹ (Mathlib Integrable.exists_hasCompactSupport_lintegral_sub_le), choose F₀ : E → ℝ continuous with compact support such that ∫⁻ |F − F₀| ≤ ofReal ε. Then F − F₀ ∈ L¹, and by step 2, ∫⁻ |ρ_j * (F − F₀)| ≤ ofReal ε for every j.

4. Uniform approximation of F₀.
 Let S := tsupport F₀ + closedBall(0,1). It is compact (a sum of compact sets), so μ(S) < ∞. Put ε' := ε/(μ(S).toReal + 1) > 0.
 F₀ is uniformly continuous (continuous with compact support), so choose r ∈ (0,1] with |F₀(y) − F₀(y')| ≤ ε' whenever ‖y − y'‖ < r. Since σ_j → 0, there is J with σ_j < r for all j ≥ J.
 Fix j ≥ J and x ∈ E. Since ∫ρ_j = 1,
   (ρ_j * F₀)(x) − F₀(x) = ∫ ρ_j(t)(F₀(x − t) − F₀(x)) dt,
 and ρ_j(t) ≠ 0 only when ‖t‖ < σ_j < r. Hence |(ρ_j * F₀)(x) − F₀(x)| ≤ ∫ ρ_j(t)·ε' dt = ε'.
 If x ∉ S, then for ‖t‖ < 1 the point x − t is not in tsupport F₀ (otherwise x = (x − t) + t ∈ S). So F₀(x − t) = 0 whenever ρ_j(t) ≠ 0, and also F₀(x) = 0; hence (ρ_j * F₀)(x) − F₀(x) = 0.
 Therefore ∫⁻ |ρ_j * F₀ − F₀| ≤ ofReal(ε')·μ(S) ≤ ofReal ε for all j ≥ J.

5. Triangle inequality. By step 2 (linearity), ρ_j * F − ρ_j * F₀ = ρ_j * (F − F₀) pointwise. So for every x,
   |(ρ_j * F)(x) − F(x)| ≤ |(ρ_j * (F − F₀))(x)| + |(ρ_j * F₀)(x) − F₀(x)| + |F₀(x) − F(x)|.
 Integrate with ∫⁻; the lower integral is monotone and additive for a.e.-measurable functions, and all three terms are a.e.-measurable. Using steps 3 and 4, for all j ≥ J:
   ∫⁻ |ρ_j * F − F| ≤ ofReal ε + ofReal ε + ofReal ε = ofReal(3ε).

6. Conclusion. For every real ε > 0 the [0,∞]-valued sequence a_j := ∫⁻ |ρ_j * F − F| eventually satisfies a_j ≤ ofReal(3ε). Hence a_j → 0 (ENNReal.tendsto_nhds_zero; ε is arbitrary). This is the claim. ∎

Remark (n = 0). E is a point of measure 1 and (ρ_j * F)(0) = ρ_j(0)F(0) = F(0), so a_j = 0. The general argument covers this case too.

## Key steps

1. ∫ρ_j = 1 forces σ_j > 0; ρ_j is bounded, compactly supported and integrable.
2. Young/Tonelli contraction: ‖ρ_j * G‖₁ ≤ ‖G‖₁ for G ∈ L¹, and convolution is linear in G.
3. Density: choose F₀ ∈ C_c with ‖F − F₀‖₁ ≤ ε (Integrable.exists_hasCompactSupport_lintegral_sub_le).
4. Uniform continuity: ρ_j * F₀ → F₀ uniformly with support in tsupport F₀ + closedBall(0,1), hence in L¹.
5. Triangle inequality gives limsup ‖ρ_j * F − F‖₁ ≤ 3ε for every ε, hence convergence to 0.

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
