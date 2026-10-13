# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.c1_cover-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.c1_cover-a1.c1_range_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 3, proof of Lemma 1.2, 'only if' part, last paragraph (chapter-03.txt lines 61–65). This is steps 4 and 6 of the parent proof for a single C¹ map.

Printed errata, applied here:
- Line 61, 'by the area formula L^n({x : JG_ij = 0}', is garbled; it means H^n(G_ij({x : JG_ij = 0})) = 0.
- Line 63, 'submanifold of ℝ^n', should read ℝ^{n+ℓ}.
- Simon leaves the countable selection of balls (Lindelöf) implicit.

Uses siblings:
- immersion_injective (Lean dor_lmbsf_c1c_immersion_local_injOn);
- ball_chart (Lean dor_lmbsf_c1c_injOn_closedBall_chart).
Required import: Poincare.SimonGMT.Chapter02.AreaCritical. It is not in the contract's import closure, so add it to Submission.lean.

1. G is differentiable everywhere. G is C¹, so it is differentiable at every x ∈ ℝ^m (ContDiff.differentiable, 1 ≠ 0).

2. The critical image is null. Let Crit := {x ∈ ℝ^m : G is differentiable at x and DG(x) is not injective}. By step 1, Crit = {x : DG(x) not injective}.
   - Mathematically: by the area formula of Simon Ch. 2 §3, H^m(G(A)) ≤ ∫_A J_G dL^m with J_G = 0 exactly where DG is not injective, so H^m(G(Crit)) = 0.
   - In SimonGMT this is Chapter02.area_image_criticalSet_eq_zero G, with E = ℝ^m = Euclid m and F = ℝ^P. It states μHE[finrank ℝ E](G '' {x | DifferentiableAt ℝ G x ∧ ¬ Injective (fderiv ℝ G x)}) = 0, and finrank ℝ (Euclid m) = m (finrank_euclideanSpace_fin).
   Put N₀ := G(Crit). Then μHE[m] N₀ = 0.

3. Local charts at regular points. Let R := {x ∈ ℝ^m : DG(x) is injective}. Fix x ∈ R.
   - Sibling immersion_injective, applied to G and x, gives r_x > 0 such that G is injective on B̄_{r_x}(x) and DG(z) is injective for all z ∈ B̄_{r_x}(x).
   - Apply sibling ball_chart to G, x and r = r_x. Its hypotheses hold: G is C¹; G is injective on B̄_{r_x}(x); and DG(z) is injective for z ∈ B_{r_x}(x), since B_{r_x}(x) ⊆ B̄_{r_x}(x).
   Hence G(B_{r_x}(x)) satisfies IsEmbeddedSubmanifold 1 m.

4. Countable subcover (Lindelöf).
   - If R = ∅, put N_l := ∅ for every l. The empty set satisfies IsEmbeddedSubmanifold 1 m vacuously, because the definition quantifies over the points of the set.
   - If R ≠ ∅, the open balls B_{r_x}(x), x ∈ R, cover R, since x ∈ B_{r_x}(x) as r_x > 0. ℝ^m is second countable, hence hereditarily Lindelöf, so R is Lindelöf. So there is a sequence (x_l)_{l∈ℕ} in R with R ⊆ ⋃_l B_{r_{x_l}}(x_l) (Mathlib HereditarilyLindelofSpace.isLindelof R and IsLindelof.indexed_countable_subcover, with the nonempty index type R). Put N_l := G(B_{r_{x_l}}(x_l)). By step 3, each N_l satisfies IsEmbeddedSubmanifold 1 m.

5. Covering. Let y ∈ G(ℝ^m), say y = G(x).
   - If DG(x) is injective, then x ∈ R (so R ≠ ∅). By step 4, x ∈ B_{r_{x_l}}(x_l) for some l, so y ∈ N_l.
   - Otherwise G is differentiable at x (step 1) and DG(x) is not injective, so x ∈ Crit and y ∈ N₀.
   Hence G(ℝ^m) ⊆ N₀ ∪ ⋃_l N_l.

6. Conclusion. N₀ and the sets N_l have all the required properties by steps 2, 4 and 5. ∎

Lean notes (checked in a scratch file):
- Step 2: `have h := Poincare.SimonGMT.Chapter02.area_image_criticalSet_eq_zero (E := Euclid m) (F := Euclid P) G`, then `rw [finrank_euclideanSpace_fin] at h`.
- Step 3: choose `r hr hinj hder` from the sibling over x : R.
- Step 4: `rcases isEmpty_or_nonempty R`; `(HereditarilyLindelofSpace.isLindelof R).indexed_countable_subcover (fun x : R => Metric.ball (x : Euclid m) (r x)) (fun _ => Metric.isOpen_ball) …`.
- Step 5: `by_cases hx : Function.Injective (fderiv ℝ G x)`.

## Key steps

1. A C¹ map is differentiable everywhere, so the critical set is {x : DG(x) not injective}.
2. SimonGMT area_image_criticalSet_eq_zero with finrank_euclideanSpace_fin gives H^m(G(Crit)) = 0; set N₀ := G(Crit).
3. For a regular x, immersion_injective gives r_x, and ball_chart makes G(B_{r_x}(x)) an embedded C¹ m-submanifold.
4. Lindelöf: countably many balls B_{r_{x_l}}(x_l) cover the regular set; set N_l := ∅ if the regular set is empty.
5. Every G(x) lies in N₀ (x critical) or in some N_l (x regular).

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
