# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.c1_cover-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.c1_cover-a1.ball_chart-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 3, proof of Lemma 1.2, chapter-03.txt lines 61–64: 'G_ij(B_σ(x)) is an n-dimensional C¹ submanifold … (with G_ij providing a local representation in a neighborhood of the point y = G_ij(x))'. The printed 'submanifold of ℝ^n' is a misprint for ℝ^{n+ℓ}. This child is the chart half of step 5 of the parent proof, with V = B_ρ(x) and ψ = G. The parent takes W = ℝ^P ∖ G(B̄_{2ρ}(x) ∖ B_ρ(x)). Its properness argument uses only the sphere ∂B_ρ(x) inside that annulus. So here W := ℝ^P ∖ G(∂B_r(x)), and injectivity is needed only on B̄_r(x).

Notation:
- S := {z ∈ ℝ^m : |z − x| = r}, the sphere; S ⊆ B̄_r(x) and S ∩ B_r(x) = ∅.
- V := B_r(x), W := ℝ^P ∖ G(S), ψ := G, N := G(V).

1. W and V are open. S is closed and bounded in ℝ^m, hence compact (Mathlib isCompact_sphere). G is continuous because it is C¹, so G(S) is compact and hence closed in the Hausdorff space ℝ^P. So W is open. V is an open ball, so V is open.

2. N ⊆ W. Let y ∈ N, say y = G(v) with v ∈ V. Suppose y ∈ G(S), say y = G(s) with s ∈ S. Both v ∈ B_r(x) ⊆ B̄_r(x) and s ∈ S ⊆ B̄_r(x), and G is injective on B̄_r(x), so s = v. But |v − x| < r = |s − x|, a contradiction. Hence y ∉ G(S), that is, y ∈ W.

3. Fix y ∈ N. We check the defining conditions of IsEmbeddedSubmanifold 1 m N at y with the data (V, W, ψ), which are the same for every y.
   (a) V and W are open by step 1, and y ∈ W by step 2.
   (b) ψ = G is C¹ on V: G is C¹ on ℝ^m, so ContDiffOn ℝ 1 G V (ContDiff.contDiffOn; the contract's order is the natural number 1 cast to WithTop ℕ∞).
   (c) ψ is injective on V, because V ⊆ B̄_r(x) and G is injective on B̄_r(x).
   (d) ψ(V) = W ∩ N. Indeed ψ(V) = N by definition, and N ⊆ W by step 2, so W ∩ N = N = ψ(V).
   (e) Properness. Let K ⊆ W be compact. We claim V ∩ G⁻¹(K) = B̄_r(x) ∩ G⁻¹(K).
       - The inclusion ⊆ holds because V ⊆ B̄_r(x).
       - Conversely, let z ∈ B̄_r(x) with G(z) ∈ K. If |z − x| = r, then z ∈ S, so G(z) ∈ G(S) and G(z) ∉ W. This contradicts G(z) ∈ K ⊆ W. Hence |z − x| < r, that is, z ∈ V.
       Now B̄_r(x) is compact (closed balls of ℝ^m are compact; isCompact_closedBall). K is compact, hence closed in ℝ^P, and G is continuous, so G⁻¹(K) is closed. A compact set intersected with a closed set is compact (IsCompact.inter_right). Therefore V ∩ ψ⁻¹(K) = B̄_r(x) ∩ G⁻¹(K) is compact.
   (f) For z ∈ V, Dψ(z) = DG(z) is injective by hypothesis.

4. Conclusion. Conditions (a)–(f) hold at every y ∈ N, so IsEmbeddedSubmanifold 1 m N holds. When r ≤ 0, V = ∅ and N = ∅, so there is nothing to check; the argument above does not use r > 0 anyway. ∎

Lean notes (checked in a scratch file):
- Step 1: `((isCompact_sphere x r).image hG.continuous).isClosed.isOpen_compl`.
- Step 3(b): `exact_mod_cast hG.contDiffOn`.
- Step 3(e): `Metric.mem_closedBall`, `lt_or_eq`, `Metric.mem_sphere`, `(isCompact_closedBall x r).inter_right (hK.isClosed.preimage hG.continuous)`.

## Key steps

1. W := ℝ^P ∖ G(∂B_r(x)) is open, because the sphere is compact and G is continuous.
2. Injectivity of G on B̄_r(x) gives G(B_r(x)) ⊆ W. So with V = B_r(x) and ψ = G, ψ(V) = W ∩ N.
3. C¹ regularity on V, injectivity on V and injective derivatives follow from the hypotheses.
4. Properness: for compact K ⊆ W, B_r(x) ∩ G⁻¹(K) = B̄_r(x) ∩ G⁻¹(K), because sphere points map outside W. This is a closed subset of a compact ball, hence compact.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); manifest.json: project b4d606db, mathlib 25730c7c; simongmt package HEAD 2b366308`
- `cat simongmt Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean (only the cover ⇒ rectifiable direction; its docstring says the converse is a separate, unformalized theorem)`
- `grep -n '^theorem' simongmt Chapter02/AreaCritical.lean (area_image_criticalSet_eq_zero, area_image_eq_zero_of_critical)`
- `grep -rn euclideanHausdorffMeasure_image_le_of_lipschitzOn simongmt (Chapter02/Lipschitz.lean:216)`
- `grep -n 'def IsSimonSubmanifold|IsProperOnInto' simongmt Chapter02/Submanifold.lean; sed Chapter03/Rectifiable.lean (CountablyRectifiable definition)`
- `rg -n "theorem LinearMap.exists_antilipschitzWith|theorem norm_image_sub_le_of_norm_fderiv_le'|theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume|theorem isOpen_iUnion_countable|theorem IsLindelof.indexed_countable_subcover|theorem contDiff_piLp|theorem measure_iUnion_fintype_le" mathlib/Mathlib`
- `rg -n -i 'immersion|injOn_of_injective_fderiv|eventually_injOn|injective_of_injective_fderiv' mathlib/Mathlib/Analysis/Calculus (no match)`
- `#check probe after import GMT.Ch07.Submission: Poincare.SimonGMT.Chapter02.area_image_criticalSet_eq_zero -> unknown identifier (import needed)`
- `python3 -I dag.json scan: lean_name containing 'dor_lmbsf_c1c_' (none) and 'c1cov' (codim1_rdo_c1cov_* accepted, different types); duplicate lean_names (none); git grep of the 4 names over all local branches (0 hits)`
- `python3 -I verifier lean_contract.validate_lean_statement and gmt-compare contract_scope/child_modules on the 4 statements; lake env lean on the generated NodeChallenge files and on /tmp/c1c-decomp/All.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-1351bbab52/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/Lindelof.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/WithLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/c1c-decomp/All.lean`

Snapshot: project b4d606d, mathlib 25730c7c, simongmt 2b36630. The snapshot Contract.lean is byte-identical to the workspace contract.

No declaration in the snapshot states the 'only if' direction of Simon Ch. 3 Lemma 1.2:
- SimonGMT Chapter03/SubmanifoldCover.lean proves only the converse.
- Mathlib has no lemma that a C¹ immersion is locally injective (rg found no match).

The reusable library facts are verified:
- SimonGMT Chapter02.area_image_criticalSet_eq_zero (critical images are H^m-null). It needs the extra import Poincare.SimonGMT.Chapter02.AreaCritical.
- SimonGMT Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn.
- Mathlib: EuclideanSpace.euclideanHausdorffMeasure_eq_volume, LinearMap.exists_antilipschitzWith, Convex.norm_image_sub_le_of_norm_fderiv_le', ContDiff.continuous_fderiv, IsLindelof.indexed_countable_subcover / HereditarilyLindelofSpace.isLindelof, contDiff_piLp, PiLp.norm_apply_le, measure_iUnion_fintype_le, ENNReal.tendsto_inv_nat_nhds_zero, finrank_euclideanSpace_fin.

The accepted codim1_rdo_c1cov_* nodes in the codimension-one branch prove a different ball-parametrisation statement, so their types differ. Reuse is not possible; the children get fresh dor_lmbsf_c1c_ names, and none collides.

Lean checks:
- All four child types elaborate in the exact comparator scope.
- Their scratch proofs and the assembly of the exact frozen parent type compile. The only non-standard axiom is the sorry stand-in for the resolved sibling c1_approx.
