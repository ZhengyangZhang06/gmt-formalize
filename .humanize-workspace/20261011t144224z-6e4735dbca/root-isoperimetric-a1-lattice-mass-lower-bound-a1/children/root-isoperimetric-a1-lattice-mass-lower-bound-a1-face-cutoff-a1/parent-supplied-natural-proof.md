# Parent-supplied natural-language proof

- Parent DAG node: `root.isoperimetric-a1.lattice_mass_lower_bound-a1`
- Child DAG node: `root.isoperimetric-a1.lattice_mass_lower_bound-a1.face_cutoff-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2, 3 and 4 of the parent proof (the boxes K_δ ⊆ int L_δ, the separation of L_δ from every other lattice face of direction α, and the smooth Urysohn cut-off). The bound δ < 1/4 used in the parent is not needed for these steps. Notation: A := range α; x_i is the i-th coordinate of x ∈ ℝ^N, and each coordinate map x ↦ x_i is continuous.

1. The sets. Let L := {x : ρ(z_i + δ/2) ≤ x_i ≤ ρ(z_i + 1 − δ/2) for i ∈ A, |x_i − ρ z_i| ≤ ρ/2 for i ∉ A} and O := {x : ρ(z_i + δ/2) < x_i < ρ(z_i + 1 − δ/2) for i ∈ A, |x_i − ρ z_i| < ρ/2 for i ∉ A}. Each of K, L, O is the intersection over i ∈ Fin N of the set defined by its condition at the coordinate i. If i ∈ A, that set is the intersection of the two half-spaces {x : t ≤ x_i} and {x : x_i ≤ t'} (closed for K and L) or {x : t < x_i} and {x : x_i < t'} (open for O). If i ∉ A, it is the hyperplane {x : x_i = ρ z_i} (closed, for K), the slab {x : |x_i − ρ z_i| ≤ ρ/2} (closed, for L), or the slab {x : |x_i − ρ z_i| < ρ/2} (open, for O). Hence K and L are closed (`isClosed_iInter`) and O, a finite intersection of open sets, is open (`isOpen_iInter_of_finite`).
2. K ⊆ interior L. Clearly O ⊆ L. Let x ∈ K. For i ∈ A, using ρ > 0 and δ > 0: ρ(z_i + δ/2) < ρ(z_i + δ) ≤ x_i ≤ ρ(z_i + 1 − δ) < ρ(z_i + 1 − δ/2). For i ∉ A: |x_i − ρ z_i| = 0 < ρ/2. So K ⊆ O. As O is open and O ⊆ L, O ⊆ interior L (`interior_maximal`); hence K ⊆ interior L.
3. L is compact. Let x ∈ L. For i ∈ A, ρ z_i − ρ ≤ ρ z_i ≤ ρ(z_i + δ/2) ≤ x_i ≤ ρ(z_i + 1 − δ/2) ≤ ρ z_i + ρ; for i ∉ A, |x_i − ρ z_i| ≤ ρ/2 ≤ ρ. Hence L ⊆ toLp(Π_{i ∈ Fin N} [ρ z_i − ρ, ρ z_i + ρ]), the image of a compact product of closed intervals (`isCompact_univ_pi`, `isCompact_Icc`) under the continuous map WithLp.toLp 2 : (Fin N → ℝ) → ℝ^N (`PiLp.continuous_toLp`); this image is compact. A closed subset of a compact set is compact (`IsCompact.of_isClosed_subset`), so L is compact.
4. Smooth Urysohn function. The space ℝ^N, as a smooth manifold modelled on itself (model 𝓘(ℝ, ℝ^N)), is finite-dimensional, Hausdorff, normal and σ-compact. Apply Mathlib's `exists_contMDiffMap_one_nhds_of_subset_interior` with smoothness exponent ⊤ : ℕ∞, s := K (closed by step 1) and t := L, using K ⊆ interior L (step 2). It gives a map f : ℝ^N → ℝ, C^∞ in the manifold sense, such that f = 1 on a neighbourhood of K (in particular f(x) = 1 for every x ∈ K, `Filter.Eventually.self_of_nhdsSet`), f(x) = 0 for every x ∉ L, and f(x) ∈ [0, 1] for every x. Let φ := f. By `contMDiff_iff_contDiff`, φ is ContDiff ℝ (⊤ : ℕ∞); also 0 ≤ φ ≤ 1 everywhere and φ = 1 on K.
5. Compact support. φ vanishes outside the compact set L (steps 3 and 4), so HasCompactSupport φ (`HasCompactSupport.intro`).
6. Vanishing on the other faces of direction α. Let z' ∈ ℤ^N with z' ≠ z and x ∈ latticeFace ρ (z', α); by definition ρ z'_i ≤ x_i ≤ ρ(z'_i + 1) for i ∈ A and x_i = ρ z'_i for i ∉ A. We show x ∉ L, whence φ(x) = 0 by step 4. Choose i with z'_i ≠ z_i (`Function.ne_iff`). Since z'_i and z_i are distinct integers, z'_i + 1 ≤ z_i or z_i + 1 ≤ z'_i. (a) If i ∈ A and z'_i + 1 ≤ z_i, then x_i ≤ ρ(z'_i + 1) ≤ ρ z_i < ρ(z_i + δ/2), violating the lower bound in the definition of L at i. (b) If i ∈ A and z_i + 1 ≤ z'_i, then x_i ≥ ρ z'_i ≥ ρ(z_i + 1) > ρ(z_i + 1 − δ/2), violating the upper bound of L at i. (c) If i ∉ A, then x_i = ρ z'_i and |x_i − ρ z_i| = ρ |z'_i − z_i| ≥ ρ > ρ/2, because |z'_i − z_i| ≥ 1 for distinct integers (`Int.one_le_abs`); this violates the condition of L at i. In all cases x ∉ L, so φ(x) = 0.
7. Steps 4, 5 and 6 give a function φ with all the required properties.

## Key steps

1. Enlarged box L (margins δ/2 along range α, transversal slab of half-width ρ/2) and open box O; K and L are closed, O is open.
2. K ⊆ O ⊆ L, hence K ⊆ interior L.
3. L lies in a compact product box (via WithLp.toLp) and is closed, hence compact.
4. Smooth Urysohn (exists_contMDiffMap_one_nhds_of_subset_interior with exponent ⊤ : ℕ∞, then contMDiff_iff_contDiff): 0 ≤ φ ≤ 1, φ = 1 on K, φ = 0 off L, so φ has compact support.
5. Every point of latticeFace ρ (z', α), z' ≠ z, violates the L-condition at a coordinate where z' and z differ, so φ vanishes there.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (project_commit d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp of snapshot Mathlib files against lake-packages-25730c7c (identical)`
- `sed -n 140,364p GMT/Ch06/Contract.lean (latticeFace, latticeFaceAction, IsLatticeChain, DeformationTheorem, IsoperimetricTheorem)`
- `cat SimonGMT Chapter06/Forms.lean Mass.lean FormsDuality.lean; sed -n 1,200p Chapter06/Currents.lean`
- `grep -n theorem Mathlib/Geometry/Euclidean/Volume/Measure.lean (Isometry.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, euclideanHausdorffMeasure_zero)`
- `grep -n 'exists_contMDiffMap_one_nhds_of_subset_interior|exists_contMDiffMap_zero_one_of_isClosed' Mathlib/Geometry/Manifold/PartitionOfUnity.lean; grep contMDiff_iff_contDiff Mathlib/Geometry/Manifold/ContMDiff/NormedSpace.lean`
- `grep -rn 'volume_preserving_ofLp|volume_Icc_pi|range_inj_of_wellFoundedLT|eq_of_subset_of_ncard_le|ncard_range_of_injective|det_eq_zero_of_row_eq_zero' Mathlib`
- `grep -rn 'integrableOn_of_bounded|setIntegral_mono_set|setIntegral_eq_zero_of_forall_eq_zero|setIntegral_congr_fun' Mathlib/MeasureTheory/Integral`
- `grep -n 'single_apply|EuclideanSpace.proj|coe_proj|basisFun_apply' Mathlib/Analysis/InnerProductSpace/PiL2.lean Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `grep -rn isometryOfOrthonormal Mathlib (exists; not needed, explicit coordinate isometry used instead)`
- `sed -n 1925,2000p book/chapter-06.txt (printed proof of 6.1, eq. (1))`
- `python3 -I: gmt-compare.py contract_scope(Contract.lean, GMT.Ch06.main_theorem); lean_contract.validate_lean_statement on the 4 child statements and the parent type`
- `python3 -I: dag.json lean_name collision check (162 nodes); grep -r of the four names over .humanize, GMT and simongmt (no match)`
- `lake build GMT.Ch06.Submission in /tmp/lmlb_decomp_check (git archive d8d46c9, pinned packages)`
- `lake env lean Scratch/Stmts.lean Scratch/Glue.lean Scratch/C1.lean Scratch/C2.lean Scratch/C3.lean (#print axioms)`
- `lake build GMT.LmlbFakeSub; lake env lean Scratch/NodeChallenges.lean Scratch/NodeSolutions.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/ContMDiff/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/WellFounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Set/Card.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-isoperimetric-a1-lattice-mass-lower-bound-a1/parent-child-handoff.json`
- `/tmp/lmlb_decomp_check/Scratch/Stmts.lean`
- `/tmp/lmlb_decomp_check/Scratch/Glue.lean`
- `/tmp/lmlb_decomp_check/Scratch/C1.lean`
- `/tmp/lmlb_decomp_check/Scratch/C2.lean`
- `/tmp/lmlb_decomp_check/Scratch/C3.lean`
- `/tmp/lmlb_decomp_check/GMT/LmlbFakeSub.lean`
- `/tmp/lmlb_decomp_check/Scratch/NodeChallenges.lean`
- `/tmp/lmlb_decomp_check/Scratch/NodeSolutions.lean`

Snapshot: project d8d46c95 and Mathlib 25730c7c; the snapshot Mathlib files are byte-identical to the pinned packages. Contract: the frozen Contract defines latticeFace, latticeFaceAction and IsLatticeChain as used. SimonGMT provides: covectorEuclideanNorm (sum over strictly increasing I of squared values on basisFun frames), covectorEuclideanNorm_neg, massAdmissibleOn, massOn/mass and le_massOn (Mass.lean); TestFormOn and GeometricCurrentOn (Currents.lean); IsSmoothForm = ContDiff ℝ ∞ with ∞ = (⊤ : ℕ∞) (Forms.lean); SimonMultiIndex, wedgeCovectors and wedgeCovectors_apply_det (FormsDuality.lean). Mathlib provides: Isometry.euclideanHausdorffMeasure_image and EuclideanSpace.euclideanHausdorffMeasure_eq_volume (μHE[n] is isometry-invariant and equals Lebesgue measure on EuclideanSpace ℝ (Fin n)); PiLp.volume_preserving_ofLp and Real.volume_Icc_pi; exists_contMDiffMap_one_nhds_of_subset_interior (n : ℕ∞) with contMDiff_iff_contDiff; StrictMono.range_inj_of_wellFoundedLT, Set.eq_of_subset_of_ncard_le, Set.ncard_range_of_injective and Matrix.det_eq_zero_of_row_eq_zero; Measure.integrableOn_of_bounded and the setIntegral_* lemmas. μHE[n] is not finite on compact subsets of ℝ^N when n < N, so integrability on a face must use the explicit finite face measure from box_measure. No Mathlib or SimonGMT lemma covers the measure of a lattice face or a face-separating cut-off, so these are genuine new obligations. Kernel checks in the scratch copy of the frozen project: all four child statements elaborate in the comparator child scope and pass validation; C1–C3 are proved directly, C4 from C1–C3, and the exact frozen parent type from C4; the comparator-style exact Submission.<name> checks pass; the only axioms are propext, Classical.choice and Quot.sound. No lean_name collides with the 162-node dag.json or the project and SimonGMT sources.
