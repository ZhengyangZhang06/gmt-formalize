# Parent-supplied natural-language proof

- Parent DAG node: `root.bv_results-a1.mollifier_gradient-a1`
- Child DAG node: `root.bv_results-a1.mollifier_gradient-a1.dual_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 1 (T4, duality bound for one test field), i.e. Simon's computation ∫ g·∇u_σ = −∫ u div(φ_σ * g) in Lemma 2.5. Here the kernel is only assumed continuous, since this step never differentiates ρ. The conclusion is kept in [0,∞], so no case split on finiteness of |Du|(W) is needed. Steps 1(a) and 1(b) of the parent are the sibling theorems Submission.bv_integral_convolution_mul_reflect and Submission.bv_euclideanDivergence_convolution.

Notation. E := ℝⁿ and μ := volume, invariant under translations and negation. All convolutions are convolution … (lsmul ℝ ℝ) μ, so (a * b)(x) = ∫ a(t) b(x − t) dt for a scalar kernel a and a scalar- or E-valued b. div := Chapter02.euclideanDivergence, the trace of fderiv.

0. Preliminaries.
 (a) F := W.indicator u. W is open, hence measurable, and u is integrable on W, so F is integrable on E (integrable_indicator_iff). Then w = ρ * F.
 (b) ρ has compact support. support ρ ⊆ B(0,σ) ⊆ closedBall(0,σ), the closed ball is compact (E is proper), and ρ vanishes outside it (HasCompactSupport.intro). Being continuous, ρ is bounded and integrable.
 (c) ρ̌(t) := ρ(−t) is continuous and ρ̌ ≥ 0. Its support is −support ρ ⊆ −B(0,σ) = B(0,σ), so ρ̌ has compact support and is integrable and locally integrable. Also ∫ρ̌ = ∫ρ = 1, since μ is invariant under negation (integral_neg_eq_self).
 (d) h := div g. Since g is C¹, x ↦ Dg(x) is continuous, and A ↦ trace(A) is a continuous linear functional on the finite-dimensional space E →L[ℝ] E; so h is continuous. Also support h ⊆ tsupport g (Chapter02.support_euclideanDivergence_subset) and tsupport g is compact, so h has compact support.
1. Fubini (sibling). Submission.bv_integral_convolution_mul_reflect, applied to F, ρ, h, gives ∫ w(x) h(x) dx = ∫ F(s) (ρ̌ * h)(s) ds.
2. The comparison field. Let G := ρ̌ * g (E-valued), G(s) = ∫ ρ(−t) g(s − t) dt.
 - Submission.bv_euclideanDivergence_convolution with κ := ρ̌ (locally integrable by 0(c)) gives div G(s) = (ρ̌ * h)(s) for every s. Hence ∫ w h = ∫ F(s) div G(s) ds.
 - For every s, F(s) div G(s) = W.indicator (fun x ↦ u x * div G x) s.
 - W is measurable, so ∫ F div G = ∫_W u div G (integral_indicator). Therefore ∫ w h = ∫_W u(s) div G(s) ds.
3. Smoothness. G is C¹ by HasCompactSupport.contDiff_convolution_right (g C¹ with compact support, ρ̌ locally integrable); in particular G is continuous.
4. Support.
 - support_convolution_subset gives support G ⊆ support ρ̌ + support g ⊆ closedBall(0,σ) + tsupport g =: S.
 - S is compact (IsCompact.add of the compact sets closedBall(0,σ) and tsupport g), hence closed, so tsupport G = closure(support G) ⊆ S.
 - Let t ∈ closedBall(0,σ) and y ∈ tsupport g. Then dist(t + y, y) = ‖t‖ ≤ σ, so t + y ∈ closedBall(y,σ) ⊆ W by hypothesis.
 - Hence tsupport G ⊆ S ⊆ W. G has compact support, since tsupport G is a closed subset of the compact S.
5. Lipschitz. G is C¹ with compact support, so LipschitzWith K G for some K ≥ 0 (ContDiff.lipschitzWith_of_hasCompactSupport).
6. Sup norm. For every s,
   ‖G(s)‖ ≤ ∫ ‖ρ̌(t) • g(s − t)‖ dt = ∫ ρ̌(t)‖g(s − t)‖ dt ≤ ∫ ρ̌(t) dt = 1.
 The steps use norm_integral_le_integral_norm, ρ̌ ≥ 0, ‖g‖ ≤ 1 and integral_mono. Integral_mono applies because t ↦ ρ̌(t)‖g(s − t)‖ is continuous with compact support, hence integrable, and ρ̌ is integrable.
7. Admissibility. Let Gc ∈ C_c(E, E) be the compactly supported continuous map with underlying function G (CompactlySupportedContinuousMap.mk, using steps 3 and 4). Then:
 - Chapter02.IsLipschitzTestField Gc holds by step 5;
 - tsupport Gc = tsupport G ⊆ W by step 4;
 - Chapter02.compactlySupportedSupNorm Gc = sSup (range (s ↦ ‖G(s)‖)) ≤ 1 by csSup_le, because the range is nonempty (E is nonempty) and each element is ≤ 1 by step 6.
8. Conclusion. Chapter02.ofReal_integral_le_bvVariationOn u W Gc gives ofReal(∫_W u(x) div G(x) dx) ≤ bvVariationOn u W. By steps 1–2, ∫ w(x) div g(x) dx = ∫_W u div G. Hence ofReal(∫ w div g) ≤ bvVariationOn u W. ∎

## Key steps

1. F = 1_W u is integrable; ρ and ρ̌(t) = ρ(−t) are continuous and compactly supported with ∫ρ̌ = 1; h = div g is continuous with compact support.
2. Siblings bv_integral_convolution_mul_reflect and bv_euclideanDivergence_convolution give ∫ w h = ∫ F(ρ̌*h) = ∫ F div G = ∫_W u div G, where G = ρ̌*g.
3. G is C¹ and Lipschitz, tsupport G ⊆ closedBall(0,σ) + tsupport g ⊆ W (compact), and ‖G‖ ≤ ∫ρ̌ = 1.
4. Package G as an admissible C_c field and apply Chapter02.ofReal_integral_le_bvVariationOn.

## Reference use

### local-project

Queries:
- `rg -n "hasFDerivAt_convolution_right|contDiff_convolution_left|contDiff_convolution_right" mathlib/Mathlib | grep -E "theorem|lemma"`
- `rg -n "(theorem|lemma) (HasCompactSupport\.convolutionExists_right|HasCompactSupport\.convolution |_root_\.HasCompactSupport\.convolution)" mathlib/Mathlib; rg -n "theorem (support_convolution_subset|HasCompactSupport\.convolution|HasCompactSupport\.convolutionExists_right|HasCompactSupport\.convolutionExists_left)\b" mathlib/Mathlib`
- `rg -n "convolution.*\(fun .* (-|neg)|convolution_neg|integral_mul_convolution|integral_convolution_mul" mathlib/Mathlib`
- `rg -n "theorem (Integrable\.convolution_integrand|integral_convolution)\b" mathlib/Mathlib; rg -n "theorem (integral_neg_eq_self|integral_add_right_eq_self|integral_integral_swap)\b" mathlib/Mathlib; rg -n "integral_neg_eq_self|integral_add_right_eq_self" mathlib/Mathlib`
- `rg -n "theorem integral_comp_comm" mathlib/Mathlib; rg -n "lipschitzWith_of_hasCompactSupport" mathlib/Mathlib`
- `rg -n "theorem (exists_smooth_tsupport_subset|exists_contDiff_tsupport_subset|exists_smooth_zero_one_of_isClosed|exists_smooth_zero_one_nhds_of_isClosed|exists_contMDiffMap_one_nhds_of_subset_interior)" mathlib/Mathlib`
- `rg -n "def normed|theorem integral_normed|theorem contDiff_normed" mathlib/Mathlib/Analysis/Calculus/BumpFunction/`
- `rg -n "theorem (IsOpen\.exists_iUnion_isClosed|lintegral_iSup|lintegral_indicator|lintegral_mono_set)\b" mathlib/Mathlib; rg -n "lintegral_iUnion_mono|Monotone\.lintegral_iUnion" mathlib/Mathlib; rg -n "exists_cthickening_subset_open|exists_iUnion_isClosed" mathlib/Mathlib | grep -E "theorem|lemma"`
- `rg -n "theorem integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable|theorem integral_bilinear_fderiv_right_eq_neg_left_of_integrable" mathlib/Mathlib`
- `rg -n "theorem (IsCompact\.exists_cthickening_subset_open|IsCompact\.cthickening|closure_thickening_subset_cthickening|mem_cthickening_of_dist_le)\b" mathlib/Mathlib; rg -n "theorem Continuous\.integral_pos_of_hasCompactSupport_nonneg_nonzero" mathlib/Mathlib`
- `rg -iln "mollif" mathlib/Mathlib`
- `cmp project/GMT/Ch02/Contract.lean <workspace>/GMT/Ch02/Contract.lean; rg -n "Submission\." project --glob '*.lean'; rg -n "BV|2\.5|mollif" project/GMT/Ch02/README.md`
- `rg -n "theorem ofReal_integral_le_bvVariationOn|theorem support_euclideanDivergence_subset|def bvVariationOn|def compactlySupportedSupNorm|def IsLipschitzTestField" simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `lean checks/Avail.lean, Avail2.lean, Avail3.lean, Avail4.lean (#check/#synth of every cited lemma after import GMT.Ch02.Submission in the contract scope)`
- `python3 -I scripts/gen_checks.py children.json checks/gen (verifier gmt-compare.py child_modules + lean_contract.validate_lean_statement); lean checks/gen/NodeChallenge_00..05.lean, checks/Assembly.lean, checks/TryA2.lean, checks/TryB0.lean, checks/TryB2.lean with #print axioms`
- `grep -rl <each of the 6 lean_names> in the run directory; lean_name of every dag.json node and nodes/*/decomposition-v*.json subproblem; git grep of the 6 names over all 84 refs (*.lean)`
- `grep check_source_delta / check_parent_git_delta / _overlay_accepted_children / _node_worktree in /runtime/flows/gmt-claude-4f40c99d0e11/_recursive_lean/{leaf_verification,parent_verification,runtime}.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-4f40c99d0e11/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-4f40c99d0e11/_recursive_lean/parent_verification.py`
- `/runtime/flows/gmt-claude-4f40c99d0e11/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1-mollifier-gradient-a1/parent-child-handoff.json`
- `/tmp/mgdecomp-Y3Fa6F/checks/gen/NodeChallenge_00.lean`
- `/tmp/mgdecomp-Y3Fa6F/checks/gen/NodeChallenge_05.lean`
- `/tmp/mgdecomp-Y3Fa6F/checks/Assembly.lean`
- `/tmp/mgdecomp-Y3Fa6F/checks/TryA2.lean`
- `/tmp/mgdecomp-Y3Fa6F/checks/TryB0.lean`
- `/tmp/mgdecomp-Y3Fa6F/checks/TryB2.lean`
- `/tmp/mgdecomp-Y3Fa6F/checks/Avail.lean`
- `/tmp/mgdecomp-Y3Fa6F/checks/Avail4.lean`

The pinned Mathlib (25730c7c) supplies every analytic tool the children cite, and all of them are inside the frozen import closure of GMT.Ch02.Submission:
- convolution derivative and smoothness: HasCompactSupport.hasFDerivAt_convolution_right, contDiff_convolution_left and contDiff_convolution_right (Analysis/Calculus/ContDiff/Convolution.lean:61,420,427);
- convolution support and existence: support_convolution_subset, HasCompactSupport.convolution, convolutionExists_right/left and Integrable.convolution_integrand (Analysis/Convolution.lean);
- integration: integral_integral_swap (MeasureTheory/Integral/Prod.lean:478), integral_neg_eq_self, integral_add_right_eq_self and ContinuousLinearMap.integral_comp_comm;
- smoothness and thickenings: ContDiff.lipschitzWith_of_hasCompactSupport, IsCompact.exists_cthickening_subset_open (Thickening.lean:426), closure_thickening_subset_cthickening and mem_cthickening_of_dist_le;
- measure theory: IsOpen.exists_iUnion_isClosed (HausdorffDistance.lean:207), lintegral_iSup, lintegral_indicator, lintegral_mono_set and Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero;
- bumps and cut-offs: ContDiffBump with its HasContDiffBump instance on Rn n, and exists_contMDiffMap_one_nhds_of_subset_interior (PartitionOfUnity.lean:526).
Mathlib has no transposition identity ∫(ρ*F)h = ∫F(ρ̌*h): only convolution_neg_of_neg_eq, for even kernels. It also has no divergence-of-convolution lemma, no mollifier or BV material ('mollif' has no match) and no lintegral_iUnion_mono or Monotone.lintegral_iUnion. Those are genuine obligations.
ContDiffBump.normed (BumpFunction/Normed.lean:32), exists_smooth_tsupport_subset, gradient and the C¹ IBP integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (LineDeriv/IntegrationByParts.lean:226) are in the snapshot but are unknown constants after import GMT.Ch02.Submission. Leaf children cannot add imports, so the children avoid them. IBP stays with the parent's sibling dependency, which children do not inherit.
The pinned SimonGMT BV.lean provides bvVariationOn, IsLipschitzTestField, compactlySupportedSupNorm, ofReal_integral_le_bvVariationOn and support_euclideanDivergence_subset, all used by dual_bound.
The snapshot Contract.lean is byte-identical to the workspace contract, and the project defines no Submission.* declarations.
All 6 statements elaborate in the comparator's own contract scope. The selected type is assembled from them plus the IBP stub. div_conv, smooth_cutoff and compact_exhaustion were proved outright in scratch Lean using only standard axioms. No name collides with a DAG node, a decomposition subproblem or any git ref.
