# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.c1_cover-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.c1_cover-a1.lipschitz_c1_pieces-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 3, proof of Lemma 1.2, 'only if' part, chapter-03.txt lines 39–59. This is steps 2–3 of the parent proof for one Lipschitz map F = F_j.

Printed errata, applied here:
- Lines 41–42: 'G_ij : ℝ^n → ℝ^ℓ' should read ℝ^{n+ℓ}.
- Line 49: 'graph F_j ⊆ E_j ∪ ⋃_i G_ij(ℝ^n)' should read F_j(ℝ^n) ⊆ ….
- Ch. 2 Theorem 1.5 is scalar, so it is applied coordinatewise.

The constants differ harmlessly from the parent's step 2: each coordinate uses ε = 1/i instead of 1/(iP). The resulting bound P/i → 0 replaces 1/i and removes the separate case P = 0.

1. Coordinates are Lipschitz. For p ∈ Fin P let F^p(y) := (F(y))_p. For a ∈ ℝ^P we have |a_p| ≤ |a| (Mathlib PiLp.norm_apply_le). Hence
   |F^p(a) − F^p(b)| = |(F(a) − F(b))_p| ≤ |F(a) − F(b)| ≤ K|a − b|,
   so F^p is K-Lipschitz.

2. Coordinatewise C¹ approximation. Fix i ∈ ℕ and put ε_i := 1/i ∈ (0, ∞]. In [0, ∞] we have 1/0 = ∞, and ε_i > 0 because i < ∞. For each p, apply (H) to u = F^p, L = K and ε = ε_i. This gives a C¹ function g_{ip} : ℝ^m → ℝ with L^m({F^p ≠ g_{ip}}) < 1/i. Define G_i : ℝ^m → ℝ^P by (G_i(y))_p := g_{ip}(y). Each coordinate of G_i is C¹, so G_i is C¹ (Mathlib contDiff_piLp).

3. Disagreement sets are small. If F(y) ≠ G_i(y), then F^p(y) ≠ g_{ip}(y) for some p, since two vectors of ℝ^P with equal coordinates are equal. So {F ≠ G_i} ⊆ ⋃_p {F^p ≠ g_{ip}}. By monotonicity and finite subadditivity of the outer measure L^m (no measurability needed; measure_iUnion_fintype_le):
   L^m({F ≠ G_i}) ≤ Σ_p L^m({F^p ≠ g_{ip}}) ≤ P · (1/i).

4. The bad set is null. Let Z := ⋂_{i∈ℕ} {F ≠ G_i}. For each i, Z ⊆ {F ≠ G_i}, so L^m(Z) ≤ P · (1/i). In [0, ∞], 1/i → 0 as i → ∞, and P < ∞, so P · (1/i) → 0 (ENNReal.tendsto_inv_nat_nhds_zero, ENNReal.Tendsto.const_mul). Hence L^m(Z) ≤ 0, that is, L^m(Z) = 0.

5. The image of the bad set is null. Put E := F(Z). F is K-Lipschitz on Z, so H^m(F(Z)) ≤ K^m H^m(Z) (SimonGMT Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn with n = m, applied to LipschitzOnWith K F Z). On ℝ^m = Euclid m, H^m = L^m (Mathlib EuclideanSpace.euclideanHausdorffMeasure_eq_volume m). So H^m(E) ≤ K^m · L^m(Z) = 0.

6. Covering. Let y ∈ F(ℝ^m), say y = F(z).
   - If z ∈ Z, then y ∈ F(Z) = E.
   - Otherwise z ∉ {F ≠ G_i} for some i, that is, F(z) = G_i(z), so y = G_i(z) ∈ G_i(ℝ^m).
   Hence F(ℝ^m) ⊆ E ∪ ⋃_i G_i(ℝ^m).

7. Conclusion. E and the maps (G_i) have the required properties by steps 2, 5 and 6. ∎

Lean notes (checked in a scratch file):
- Coordinates are `(F y).ofLp p`; use `PiLp.sub_apply` and `PiLp.norm_apply_le`.
- `ε := ((i : ℝ≥0∞))⁻¹`, positive by `ENNReal.inv_pos.2 (ENNReal.natCast_ne_top i)`.
- `G i y := WithLp.toLp 2 (fun p => g i p y)` with `(contDiff_piLp 2).2`.
- Step 3: `measure_iUnion_fintype_le`; the sum of constants simplifies to `(P : ℝ≥0∞) * (i)⁻¹`.
- Step 4: `ge_of_tendsto'` with `ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr (ENNReal.natCast_ne_top P))`.
- Step 5: `Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn m (hF.lipschitzOnWith (s := Z))`, then rewrite with `EuclideanSpace.euclideanHausdorffMeasure_eq_volume`.

## Key steps

1. The coordinates F^p of F are K-Lipschitz.
2. Apply (H) to each coordinate with ε = 1/i and assemble the C¹ maps G_i coordinatewise.
3. Subadditivity over the P coordinates gives L^m({F ≠ G_i}) ≤ P/i.
4. Z = ⋂_i {F ≠ G_i} is L^m-null, and E = F(Z) is H^m-null by the Lipschitz image bound and H^m = L^m on ℝ^m.
5. Points off Z satisfy F = G_i for some i, so F(ℝ^m) ⊆ E ∪ ⋃_i G_i(ℝ^m).

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
