# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.c1_cover-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.c1_cover-a1.immersion_injective-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 3, proof of Lemma 1.2, 'only if' part (chapter-03.txt lines 61–65): 'if the Jacobian of G_ij is non-zero at a point x, then there is a σ > 0 such that G_ij(B_σ(x)) is an n-dimensional C¹ submanifold'. This child is the analytic first half of step 5 of the parent proof: the choice of c and ρ, the mean value inequality and injectivity. Notation: L := DG(x); ‖A‖ denotes the operator norm of a linear map A.

1. Lower bound for L. L is an injective linear map on the finite-dimensional space ℝ^m, so ker L = 0 and L is anti-Lipschitz: there is K > 0 with |v| ≤ K|Lv| for all v ∈ ℝ^m. (Mathlib LinearMap.exists_antilipschitzWith, applied to L as a linear map with ker = ⊥ from LinearMap.ker_eq_bot, gives AntilipschitzWith K L. Applying it to v and 0 gives |v| ≤ K|Lv|.) For m ≥ 1, 1/K plays the role of c = min_{|v|=1}|Lv| > 0 in the parent proof. For m = 0 every vector is 0 and the bound is trivial. Put c := 1/K > 0. Then c|v| ≤ |Lv| for every v ∈ ℝ^m.

2. Choice of r. Since G is C¹, z ↦ DG(z) is continuous into the space of linear maps with the operator norm (ContDiff.continuous_fderiv, using 1 ≠ 0). So there is δ > 0 with ‖DG(z) − L‖ < c/2 whenever |z − x| < δ. Put r := δ/2 > 0. Every z ∈ B̄_r(x) has |z − x| ≤ δ/2 < δ. Hence ‖DG(z) − L‖ ≤ c/2 for every z ∈ B̄_r(x).

3. Injective derivatives on B̄_r(x). Let z ∈ B̄_r(x) and v, w ∈ ℝ^m with DG(z)v = DG(z)w. Put u := v − w. By linearity DG(z)u = 0, so Lu = Lu − DG(z)u = −(DG(z) − L)u. By steps 1 and 2,
   c|u| ≤ |Lu| = |(DG(z) − L)u| ≤ ‖DG(z) − L‖·|u| ≤ (c/2)|u|.
   Since c > 0, this gives |u| ≤ 0, so u = 0 and v = w. Hence DG(z) is injective.

4. Mean value inequality. The closed ball B̄_r(x) is convex, G is differentiable at each of its points (G is C¹), and ‖DG(z) − L‖ ≤ c/2 for z ∈ B̄_r(x) by step 2. Apply the mean value inequality to G − L on B̄_r(x) (Mathlib Convex.norm_image_sub_le_of_norm_fderiv_le' with φ = L and C = c/2). For all a, b ∈ B̄_r(x):
   |G(a) − G(b) − L(a − b)| ≤ (c/2)|a − b|.

5. G is injective on B̄_r(x). Let a, b ∈ B̄_r(x) with G(a) = G(b). Then G(a) − G(b) = 0 and |−L(a − b)| = |L(a − b)|, so step 4 reads |L(a − b)| ≤ (c/2)|a − b|. Step 1 gives c|a − b| ≤ |L(a − b)|. Hence c|a − b| ≤ (c/2)|a − b|. As c > 0, |a − b| = 0 and a = b.

6. Conclusion. r = δ/2 > 0, G is injective on B̄_r(x) by step 5, and DG(z) is injective for every z ∈ B̄_r(x) by step 3. ∎

Lean notes (checked in a scratch file):
- Steps 1–2: `(fderiv ℝ G x : Euclid m →ₗ[ℝ] Euclid P).exists_antilipschitzWith (LinearMap.ker_eq_bot.2 hx)`, then `hK.le_mul_dist v 0`, `inv_mul_le_iff₀`, `hG.continuous_fderiv (by norm_num)` and `Metric.continuous_iff`.
- Step 4: `(convex_closedBall x r).norm_image_sub_le_of_norm_fderiv_le'`.
- Steps 3 and 5: `ContinuousLinearMap.le_opNorm`; conclude with nlinarith from c‖u‖ ≤ (c/2)‖u‖.

## Key steps

1. DG(x) is injective on the finite-dimensional ℝ^m, hence anti-Lipschitz: c|v| ≤ |DG(x)v| for some c > 0.
2. Continuity of DG gives r > 0 with ‖DG(z) − DG(x)‖ ≤ c/2 on B̄_r(x).
3. Then c|u| ≤ |DG(x)u| = |(DG(z) − DG(x))u| ≤ (c/2)|u| whenever DG(z)u = 0, so DG(z) is injective on B̄_r(x).
4. Mean value inequality on the convex ball: |G(a) − G(b) − DG(x)(a − b)| ≤ (c/2)|a − b|.
5. If G(a) = G(b), then c|a − b| ≤ (c/2)|a − b|, so a = b: G is injective on B̄_r(x).

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
