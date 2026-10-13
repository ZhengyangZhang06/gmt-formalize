# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1`
- Child DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.integer_median-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the parent proof ((31) and (35) of the proof of Simon 5.1), stated for an arbitrary measure space. The parent applies it with μ = volume on ℝ^n, F = latticeFace ρ F (a cube of volume ρ^n) and a = ρ^n.

Notation.
- For k ∈ ℤ put A_k := F ∩ {x : u(x) ≤ k}, which is measurable because F and u are, and m_k := μ(A_k) ∈ [0, ofReal a].
- Every measurable subset of F has finite measure (≤ μ(F) = ofReal a). So complements within F may be subtracted: μ(F ∩ B) + μ(F ∖ B) = ofReal a for measurable B.
- Below, measures of subsets of F are also compared as real numbers via toReal when convenient.

1. (Limits.) k ↦ A_k is monotone.
   - ⋃_{k ∈ ℤ} A_k = F, because every real u(x) satisfies u(x) ≤ k for k ≥ ⌈u(x)⌉.
   - ⋂_{k ∈ ℤ} A_k = ∅, because u(x) > k for k = ⌊u(x)⌋ − 1.
   By continuity from below (tendsto_measure_iUnion_atTop), m_k → μ(F) = ofReal a as k → +∞. By continuity from above for sets of finite measure (tendsto_measure_iInter_atTop applied to the antitone family j ↦ A_{−j}, j ∈ ℕ, whose members have finite measure), m_{−j} → μ(∅) = 0 as j → ∞.

2. (Choice of β.) Let K := {k ∈ ℤ : ofReal(a/2) ≤ m_k}.
   - K ≠ ∅: since ofReal(a/2) < ofReal a, step 1 gives some k with m_k > ofReal(a/2).
   - K is bounded below: since ofReal(a/2) > 0, step 1 gives j₀ ∈ ℕ with m_{−j₀} < ofReal(a/2). By monotonicity every k ∈ K satisfies k > −j₀.
   Let β be the least element of K (Int.exists_least_of_bdd). Then:
   (i) μ(F ∩ {u ≤ β}) ≥ a/2, since β ∈ K;
   (ii) μ(F ∩ {u ≤ β − 1}) < a/2, since β − 1 ∉ K.
   Because u is integer-valued, u(x) < β ⟺ u(x) ≤ β − 1, and u(x) > β ⟺ u(x) ≥ β + 1. So F is the disjoint union of F ∩ {u ≤ β − 1} and F ∩ {u ≥ β}, and also of F ∩ {u ≤ β} and F ∩ {u > β}. Therefore:
   (iii) μ(F ∩ {u ≥ β}) = a − μ(F ∩ {u ≤ β − 1}) > a/2, and μ(F ∩ {u < β}) = μ(F ∩ {u ≤ β − 1}) < a/2;
   (iv) μ(F ∩ {u > β}) = a − μ(F ∩ {u ≤ β}) ≤ a/2.

3. (M1.) If β = 0, the left side is ofReal 0 = 0.
   - If β ≥ 1: for x ∈ F ∩ {u ≥ β}, |u(x)| ≥ u(x) ≥ β = |β|. Hence ∫⁻_F ofReal|u| dμ ≥ ∫⁻_{F ∩ {u ≥ β}} ofReal|u| dμ ≥ ofReal|β| · μ(F ∩ {u ≥ β}) ≥ ofReal|β| · ofReal(a/2), by monotonicity in the set, the constant lower bound on the set, and (iii).
   - If β ≤ −1: for x ∈ F ∩ {u ≤ β}, |u(x)| ≥ −u(x) ≥ −β = |β|. Hence ∫⁻_F ofReal|u| dμ ≥ ofReal|β| · μ(F ∩ {u ≤ β}) ≥ ofReal|β| · ofReal(a/2), by (i).
   In both cases 2 ∫⁻_F ofReal|u| dμ ≥ 2 · ofReal|β| · ofReal(a/2) = ofReal(|β| a).

4. (M2.) Suppose μ(F ∩ {u ≠ 0}) = 0.
   - Since u ≤ −1 implies u ≠ 0, m_{−1} ≤ μ(F ∩ {u ≠ 0}) = 0 < ofReal(a/2).
   - Since F ⊆ A_0 ∪ (F ∩ {u ≠ 0}), ofReal a ≤ m_0. So 0 ∈ K and β ≤ 0.
   - If β ≤ −1, monotonicity gives m_{−1} ≥ m_β ≥ ofReal(a/2) (β ∈ K), contradicting m_{−1} = 0.
   Hence β = 0. By contraposition, β ≠ 0 implies μ(F ∩ {u ≠ 0}) ≠ 0.

5. (M3: β minimizes c ↦ ∫_F |u − c| dμ.) The functions |u − c|, c ∈ ℝ, are integrable on F, since u is and constants are (μ(F) < ∞). Claim: ∫_F |u − β| dμ ≤ ∫_F |u − c| dμ for every c ∈ ℝ.
   Case c ≥ β, with d := c − β ≥ 0.
   - If u(x) ≤ β, then |u(x) − c| = c − u(x) = (β − u(x)) + d = |u(x) − β| + d.
   - If u(x) > β, then |u(x) − c| ≥ |u(x) − β| − d by the triangle inequality.
   So on F, |u − c| ≥ |u − β| + d·(1_{u ≤ β} − 1_{u > β}). Integrating over F:
   ∫_F |u − c| ≥ ∫_F |u − β| + d·(μ(F ∩ {u ≤ β}) − μ(F ∩ {u > β})) ≥ ∫_F |u − β|,
   because μ(F ∩ {u ≤ β}) ≥ a/2 ≥ μ(F ∩ {u > β}) by (i) and (iv).
   Case c < β, with d := β − c > 0.
   - If u(x) ≥ β, then |u(x) − c| = u(x) − c = |u(x) − β| + d.
   - If u(x) < β, then |u(x) − c| ≥ |u(x) − β| − d.
   Integrating over F:
   ∫_F |u − c| ≥ ∫_F |u − β| + d·(μ(F ∩ {u ≥ β}) − μ(F ∩ {u < β})) ≥ ∫_F |u − β|,
   because μ(F ∩ {u ≥ β}) > a/2 > μ(F ∩ {u < β}) by (iii).

6. (M4.) Let ū := a⁻¹ ∫_F u dμ, and fix x.
   - Since ∫_F u(x) dμ(y) = a·u(x) ((μ(F)).toReal = a), u(x) − ū = a⁻¹ ∫_F (u(x) − u(y)) dμ(y).
   - Hence |u(x) − ū| ≤ a⁻¹ ∫_F |u(x) − u(y)| dμ(y) (norm_integral_le_integral_norm).
   - Since y ↦ |u(x) − u(y)| is nonnegative and integrable on F, ENNReal.ofReal_mul and ofReal_integral_eq_lintegral_ofReal give
     ofReal|u(x) − ū| ≤ ofReal(a⁻¹) · ofReal(∫_F |u(x) − u(y)| dμ(y)) = ofReal(a⁻¹) · ∫⁻_F ofReal|u(x) − u(y)| dμ(y).
   Therefore
   ∫⁻_F ofReal|u − β| dμ
   = ofReal(∫_F |u − β| dμ)
   ≤ ofReal(∫_F |u − ū| dμ)
   = ∫⁻_F ofReal|u − ū| dμ
   ≤ ∫⁻_F ofReal(a⁻¹) ∫⁻_F ofReal|u(x) − u(y)| dμ(y) dμ(x)
   = ofReal(a⁻¹) ∫⁻_F ∫⁻_F ofReal|u(x) − u(y)| dμ(y) dμ(x).
   This uses ofReal_integral_eq_lintegral_ofReal twice, step 5 with c := ū and monotonicity of ofReal, lintegral_mono with the pointwise bound above, and lintegral_const_mul' (ofReal(a⁻¹) ≠ ∞).

7. The integer β satisfies (M1), (M2) and (M4). ∎

## Key steps

1. a_k := μ(F ∩ {u ≤ k}) is monotone with limits μ(F) at +∞ and 0 at −∞, so β := least k with a_k ≥ a/2 exists.
2. Integer values give μ(F ∩ {u ≤ β}) ≥ a/2, μ(F ∩ {u ≥ β}) > a/2, μ(F ∩ {u < β}) < a/2 and μ(F ∩ {u > β}) ≤ a/2.
3. (M1) |β|a ≤ 2∫_F|u| from |u| ≥ |β| on a set of measure ≥ a/2; (M2) if u = 0 a.e. on F then β = 0.
4. (M3) β minimizes c ↦ ∫_F|u − c| by the pointwise splitting and the median measure inequalities.
5. (M4) take c = mean of u on F; |u(x) − ū| ≤ a⁻¹∫_F|u(x) − u(y)|dy; convert to lintegrals.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (local-project; project d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/.../project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean; cmp Contract.lean Submission.lean; git show 48003458:GMT/Ch06/Submission.lean | cmp (all identical: the node base holds only the frozen contract)`
- `sed -n 120,364p GMT/Ch06/Submission.lean (LatticeFaceIndex, latticeFace, latticeFaceAction, IsLatticeChain, IsIntegerMultiplicity, IsRectifiableTriple, tauAction)`
- `grep -n 'def covectorEuclideanNorm|def massAdmissibleOn|def GeometricCurrentOn.massOn|def GeometricCurrentOn.mass|structure GeometricCurrentOn|def TestFormOnConverges|def GeometricCurrentOn.support|def simpleNVector|def wedgeCovectors|abbrev SimonMultiIndex|instance.*GeometricCurrentOn' simongmt/Poincare/SimonGMT (GeometricCurrentOn has only a Zero instance, no Sub)`
- `grep -n 'def blowUpMap|def HasWeightedApproximateTangentSpaceAt|def CountablyRectifiable|countablyRectifiable_range|CountablyRectifiable.mono' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -rn in local-references mathlib: EuclideanSpace.euclideanHausdorffMeasure_eq_volume, AlternatingMap.eq_smul_basis_det, OrthonormalBasis.det_to_matrix_orthonormalBasis_real, aestronglyMeasurable_iUnion_iff, lintegral_iUnion₀, integral_iUnion_ae, setIntegral_eq_integral_of_forall_compl_eq_zero, lintegral_mul_left_eq_self (to_additive lintegral_add_left_eq_self), lintegral_lintegral_swap, PiLp.volume_preserving_ofLp, volume_Icc_pi, exists_least_of_bdd, tendsto_measure_iUnion_atTop, tendsto_measure_iInter_atTop, ofReal_integral_eq_lintegral_ofReal, setLIntegral_mono', mem_cthickening_of_dist_le, EuclideanSpace.dist_eq, StrictMono.eq_id, Integrable.mul_bdd, lintegral_const_mul', Int.measurable_floor, lintegral_indicator₀ (all found)`
- `python3 scan of dag.json (360 nodes): statuses, frozen lean_statement of siblings fiw_tb_rectifiable_support_null and fiw_tb_translation_estimate, accepted declarations and candidate commits; no lean_name containing 'tda'; git log --all --oneline -S fiw_tb_tda_ (no match)`
- `git cat-file -t 52afef6d 5c248501 eefd7c3e c90a4050 e8e708e4 49ba437c 3d98b187 0561b355 d57bd370 635e85e5 (all present)`
- `git show 635e85e5 -- GMT/Ch06/Submission.lean; tail speculative-process-v3.log of root-boundary-rectifiability-a1-top-dim-lattice-approx-a1 (1060-line single theorem, 178,656 of 200,000 heartbeats)`
- `sed parent-supplied-natural-proof.md of root-boundary-rectifiability-a1-top-dim-lattice-approx-a1 and root-integrality-weak-limits-a1-top-dim-a1 (related top-dimensional arguments; not duplicated)`
- `grep -n in /runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean: def _decompose, def _solve_children, def _existing_lean_name_problem, def _install_parent_supplied_child_handoff, def _overlay prerequisites (runtime.py), def check_source_delta (leaf_verification.py), def ensure (store.py)`
- `verifier/gmt-compare.py contract_scope/child_modules; python3 -I /tmp/tda-tools/check.py (validate_lean_statement on all 8 child types: pass)`
- `lean /tmp/tda-decomp/{Stmts,Comparator,Assembly2,Assembly3,Proto,Proto2}.lean with LEAN_PATH = lake-packages-25730c7c builds + workspace .lake build of d8d46c9 (0 errors; Assembly3 #count_heartbeats 10,901)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1/decomposition-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-top-dim-lattice-approx-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-top-dim-lattice-approx-a1/speculative-process-v3.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-top-dim-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/math-wiki/submission-fiw-ims-sc-continuous-of-bound.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Group/LIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Int/LeastGreatest.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Preorder/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Floor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/tda-decomp/Stmts.lean`
- `/tmp/tda-decomp/Comparator.lean`
- `/tmp/tda-decomp/Assembly2.lean`
- `/tmp/tda-decomp/Assembly3.lean`
- `/tmp/tda-decomp/Proto.lean`
- `/tmp/tda-decomp/Proto2.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) has the frozen Ch06 contract, and this node's base commit 48003458 adds no accepted declarations. Neither the project nor SimonGMT contains any of the following, so they become the 8 children:
- the top-dimensional density lemma;
- integer medians;
- the lattice-cube toolkit;
- the chain current;
- the difference-current mass bound;
- the summed Poincaré bound.

API the child proofs use:
- SimonGMT: GeometricCurrentOn (Zero instance only, so S = X − Pc is built from toCurrent subtraction), massOn/mass via massAdmissibleOn and covectorEuclideanNorm, simpleNVector_apply, wedgeCovectors_apply_det, blowUpMap, HasWeightedApproximateTangentSpaceAt, countablyRectifiable_range and CountablyRectifiable.mono.
- Mathlib: every lemma cited in the child proofs was found at the pinned revision.

Accepted declarations, cited only as adaptation pointers (all commits present locally): lpf_pic_current_of_dominated_density (52afef6d), fiw_ims_sc_continuous_of_bound (5c248501), isoperimetric_coord_box_measure (eefd7c3e), fiw_ims_frame_sign (c90a4050).

Scratch checks:
- all 8 child types elaborate in the comparator scope and pass validate_lean_statement;
- the frozen parent type is proved from them plus the two frozen sibling types (10,901 heartbeats; axioms propext, Classical.choice and Quot.sound, plus sorryAx from the stubs only);
- the riskiest child steps compile as prototypes.
