# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.c1_approx-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 2, proof of Theorem 1.5 (chapter-02.txt lines 246–262), with Rademacher's theorem 1.4 and Whitney's extension theorem 1.6 (lines 59–64, 170–185). Notation: L^m = volume on Euclid m, |·| the Euclidean norm, Du(x) = fderiv ℝ u x.

1. Reductions. If m = 0, Euclid 0 is a single point, so u is constant and G := u (ContDiff ℝ 1 of a constant map) gives {u ≠ G} = ∅. Assume m ≥ 1. If ε = ∞, run the argument below with ε replaced by 1; the resulting set has measure < 1 < ∞. So assume 0 < ε < ∞.
 [Imports: SimonGMT Chapter02.WhitneyExtension (Whitney; it builds from source, as there is no prebuilt .olean) and Chapter01.Lusin, or Mathlib's Lusin and Egorov (MeasureTheory.Function.Egorov).]

2. Rademacher (Ch. 2, 1.4; Mathlib LipschitzWith.ae_differentiableAt, or SimonGMT Chapter02.rademacher_ae_differentiableAt). The set B := {x : u is differentiable at x} is Borel (measurableSet_of_differentiableAt) and L^m(ℝ^m ∖ B) = 0. The map x ↦ Du(x) is Borel (measurable_fderiv), and ‖Du(x)‖ ≤ K on B.

3. Lusin. Let S_j := {x : j ≤ |x| < j+1} (j ∈ ℕ), Borel shells of finite measure. For each j and each coordinate l = 1, …, m, apply Lusin's theorem for real-valued measurable maps on a finite-measure set (SimonGMT Chapter01.exists_isClosed_continuousOn_of_measurable, or Mathlib's Lusin) to x ↦ Du(x)e_l on S_j ∩ B. This gives a closed C_{j,l} ⊆ S_j ∩ B with L^m((S_j ∩ B) ∖ C_{j,l}) < ε·2^{-j-3}/m and Du(·)e_l continuous on C_{j,l}. Put C_j := ⋂_l C_{j,l} and C := ⋃_j C_j. The family (C_j) is locally finite, since a bounded set meets finitely many shells, so C is closed, C ⊆ B, and L^m(ℝ^m ∖ C) ≤ Σ_j L^m(S_j ∖ C_j) < ε/2. Du|_C is continuous: it is continuous on each closed C_j, and near any point of C only finitely many C_j occur.

4. Remainders. For x, y ∈ C with y ≠ x put R(x, y) := (u(y) − u(x) − Du(x)(y − x))/|y − x|. For k ≥ 1 let
   η_k(x) := sup{|R(x, y)| : y ∈ C, 0 < |y − x| < 1/k}   (sup ∅ := 0) for x ∈ C, and η_k(x) := 0 for x ∉ C.
   Then 0 ≤ η_k ≤ 2K, η_k(x) is non-increasing in k, and η_k(x) → 0 for every x ∈ C because u is differentiable at x ∈ C ⊆ B. Each η_k is Borel on ℝ^m. R is continuous on {(x, y) ∈ C × C : x ≠ y}, because u is continuous and Du|_C is continuous. So η_k|_C is a supremum of continuous functions over relatively open conditions, hence lower semicontinuous on C. Thus {η_k > t} = (O_t ∩ C) ∪ (ℝ^m ∖ C if t < 0) with O_t open, and C is closed.

5. Egorov. For each j apply Egorov's theorem (Mathlib tendstoUniformlyOn_of_ae_tendsto) to (η_k) on the finite-measure set C_j ⊆ S_j, with tolerance ε·2^{-j-5}. This gives a measurable A₀^j ⊆ C_j with L^m(C_j ∖ A₀^j) < ε·2^{-j-5} and η_k → 0 uniformly on A₀^j. By inner regularity of L^m on the finite-measure set A₀^j, choose a closed A^j ⊆ A₀^j with L^m(A₀^j ∖ A^j) < ε·2^{-j-5}. Put A := ⋃_j A^j. It is closed (a locally finite union of closed sets), A ⊆ C, and L^m(C ∖ A) < ε/4, so L^m(ℝ^m ∖ A) < ε/2 + ε/4 < ε. Moreover η_k → 0 uniformly on A ∩ B_R(0) for every R > 0, since this set lies in finitely many A^j.

6. Whitney's condition (Ch. 2, 1.6 (*); in SimonGMT this is the structure HasWhitneyC1Compatibility A u Du). (i) u is continuous on A. (ii) Du is continuous on A ⊆ C. (iii) Let K' ⊆ A be compact and ε' > 0. K' is bounded, so η_k → 0 uniformly on K'; choose k with η_k ≤ ε' on K' and put δ := 1/k. Then for x ∈ K', y ∈ A with |x − y| < δ: |u(y) − u(x) − Du(x)(y − x)| ≤ ε'|y − x| (trivial if y = x, and |R(x, y)| ≤ η_k(x) ≤ ε' otherwise).

7. Whitney extension (Ch. 2, Theorem 1.6; SimonGMT Chapter02.exists_contDiff_one_extension_of_whitney, applied to the closed set A, h := u, D := Du): there is G : ℝ^m → ℝ with ContDiff ℝ 1 G and G = u on A. (If A = ∅ any constant G works.)

8. Conclusion. {y : u(y) ≠ G(y)} ⊆ ℝ^m ∖ A, so L^m({u ≠ G}) ≤ L^m(ℝ^m ∖ A) < ε. ∎

## Key steps

1. Reduce to 0 < ε < ∞.
2. Rademacher: u is differentiable off an L^m-null Borel set B^c; Du is Borel.
3. Lusin, coordinatewise on bounded shells: a closed C ⊆ B with L^m(ℝ^m ∖ C) < ε/2 and Du|_C continuous.
4. Define the Whitney remainders η_k on C; η_k ↓ 0 pointwise.
5. Egorov plus inner regularity: closed A ⊆ C, L^m(ℝ^m ∖ A) < ε, with η_k → 0 uniformly on bounded parts of A.
6. This is Whitney's C¹ compatibility condition for (u|_A, Du|_A).
7. Whitney extension gives a C¹ G with G = u on A, so L^m({u ≠ G}) < ε.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `python3 -I transitive import scan of the Contract's Poincare.SimonGMT imports (public import ...)`
- `grep -n '^theorem |^def ' simongmt Chapter03/Rectifiable.lean, Chapter02/{AreaFormula,WeightedArea,AreaCritical,AreaLipschitz,AreaDomain,CoareaProjection,CoareaLinear,WhitneyExtension,WhitneyJet,Lipschitz}.lean, Chapter03/{SubmanifoldCover,DisjointCover,Differential}.lean, Chapter06/{Forms,Currents}.lean`
- `grep -rn 'HasApproximateTangentSpaceAt.unique|exists_contDiff_one_extension_of_whitney|HasWhitneyC1Compatibility|area_image_criticalSet_eq_zero|integral_area_formula_of_injective_derivative|weighted_area_formula_of_injective_derivative|map_withDensity_areaJacobian_eq|integrableOn_image_iff_integrableOn_areaJacobian_smul|exists_isClosed_continuousOn_of_measurable|countablyRectifiable_iUnion' simongmt`
- `grep -rn 'ae_tendsto_measure_inter_div_of_measurableSet|LipschitzWith.integral_lineDeriv_mul_eq|Lp.dense_hasCompactSupport_contDiff|tendsto_tsum_of_dominated_convergence|alternatizeUncurryFin_apply|AlternatingMap.eq_smul_basis_det|det_to_matrix_orthonormalBasis_real|volume_preserving_piFinSuccAbove|PiLp.volume_preserving_ofLp|Measurable.lintegral_prod_right|exists_cthickening_subset_open|tendstoUniformlyOn_of_ae_tendsto|euclideanHausdorffMeasure_eq_volume|norm_alternatizeUncurryFin_le' mathlib`
- `#check probes in contract scope: ContinuousAlternatingMap.alternatizeUncurryFin, innerSL, ContinuousLinearMap.smulRight, (ℝ ∙ v)ᗮ, ‖v‖ₑ, GeometricCurrentOn.boundary, exists_measurable_superset_of_null`
- `dag.json scans: regex 'co-?area|area formula|Rademacher|tangential gradient|C¹ approx|Lusin|Jacobian|implicit function' over node statements; lean_name collision check for dor_lmbsf_* (1022 nodes, none)`
- `git grep dor_lmbsf_ over all local branches (no match)`
- `python3 -I verifier lean_contract.validate_lean_statement and gmt-compare.child_modules on the 12 statements; lake env lean /tmp/dor-sf-decomp/v2/All.lean (#print axioms DorSf.parent_from_children)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-e999363692/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaFormula.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/dor-sf-decomp/v2/All.lean`

Snapshot: project b4d606d, mathlib 25730c7c, simongmt 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, and the snapshot mathlib matches the package tree.

No existing declaration states a rectifiable co-area formula, a tangential gradient of a Lipschitz function, a slice family or the Lipschitz-cut-off Leibniz limit. Related nodes in other branches are unaccepted, reserved and have different types:
- codim1_rdo_c1_approximation;
- codim1_rdo_c1_piece_approxTangent;
- codim1_lur_rectifiable_area_formula;
- dimred_cs_sos_spine_coarea.
So all 12 children get fresh dor_lmbsf_ names.

Reusable library facts for the child proofs:
- SimonGMT Chapter02: injective area formulas in lintegral, Bochner and measure form (WeightedArea, AreaFormula); critical images null (AreaCritical); Whitney C¹ extension (WhitneyExtension/WhitneyJet); Rademacher and Lipschitz images (Lipschitz).
- SimonGMT Chapter01.Lusin.
- SimonGMT Chapter03: HasApproximateTangentSpaceAt.unique, countablyRectifiable_iUnion.
- Mathlib: Besicovitch density theorem, LipschitzWith.integral_lineDeriv_mul_eq, Lp.dense_hasCompactSupport_contDiff, Tannery's theorem, alternatizeUncurryFin_apply, volume-preserving coordinate splits.
- Some of these need extra imports, which are listed in the child proofs.

Lean checks:
- All 12 child types pass validate_lean_statement and elaborate in the exact comparator scope.
- The Lean assembly of the exact frozen parent type from tangential_gradient, slice_imreps and lipschitz_leibniz compiles with only propext, Classical.choice and Quot.sound.
- Interface checks (chart_pieces → piece lemmas; Besicovitch → density_directions) compile.
- MultiVector lacks SecondCountable/FiniteDimensional instance synthesis, so the child proofs use StronglyMeasurable compositions.
