# Parent-supplied natural-language proof

- Parent DAG node: `root.isoperimetric-a1.lattice_mass_lower_bound-a1`
- Child DAG node: `root.isoperimetric-a1.lattice_mass_lower_bound-a1.box_measure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 7 of the parent proof ("Measures of faces"), stated for an arbitrary base point c and bounds a ≤ b. With c_i = ρ z_i it gives μHE[n](latticeFace ρ (z, α)) = ρ^n for (a, b) = (0, ρ) (valid as ρ ≥ 0) and μHE[n](K_δ) = (ρ(1 − 2δ))^n for (a, b) = (ρδ, ρ(1 − δ)). Notation: A := range α, B := the set in the statement, x_i := the i-th coordinate of x ∈ ℝ^N.

1. Parametrization. Define ι : EuclideanSpace ℝ (Fin n) → ℝ^N by ι(y) := WithLp.toLp 2 (i ↦ c_i + Σ_{j ∈ Fin n} [α(j) = i] · y_j), where [α(j) = i] is 1 if α(j) = i and 0 otherwise. Because α is injective, for j ∈ Fin n exactly one summand of ι(y)_{α(j)} survives, so ι(y)_{α(j)} = c_{α(j)} + y_j; for i ∉ A every summand vanishes, so ι(y)_i = c_i.
2. ι is an isometry. Let y, y' ∈ EuclideanSpace ℝ (Fin n). By `EuclideanSpace.dist_eq`, dist(ι y, ι y') = sqrt(Σ_{i ∈ Fin N} dist(ι(y)_i, ι(y')_i)²) and dist(y, y') = sqrt(Σ_{j ∈ Fin n} dist(y_j, y'_j)²). In the first sum each term with i ∉ A vanishes (both coordinates equal c_i), so the sum equals the sum over the image α(Fin n) (`Finset.sum_subset`); reindexing along the injective α (`Finset.sum_image`) it becomes Σ_j dist(c_{α(j)} + y_j, c_{α(j)} + y'_j)² = Σ_j dist(y_j, y'_j)² (`dist_add_left`). Hence dist(ι y, ι y') = dist(y, y') for all y, y', i.e. ι is an isometry (`Isometry.of_dist_eq`).
3. ι maps the cube onto B. Let Q := {y ∈ EuclideanSpace ℝ (Fin n) : a ≤ y_j ≤ b for all j}. (⊆) Let y ∈ Q. For i = α(j) ∈ A, ι(y)_i = c_i + y_j ∈ [c_i + a, c_i + b]; for i ∉ A, ι(y)_i = c_i. So ι(y) ∈ B. (⊇) Let x ∈ B and define y ∈ EuclideanSpace ℝ (Fin n) by y_j := x_{α(j)} − c_{α(j)}. The condition of B at the coordinate α(j) ∈ A gives c_{α(j)} + a ≤ x_{α(j)} ≤ c_{α(j)} + b, i.e. a ≤ y_j ≤ b, so y ∈ Q. Moreover ι(y) = x coordinatewise: for i = α(j), ι(y)_i = c_i + (x_i − c_i) = x_i; for i ∉ A, ι(y)_i = c_i = x_i by the condition of B. Hence ι(Q) = B.
4. Transfer to Lebesgue measure. The measure μHE[n] is invariant under isometries (`Isometry.euclideanHausdorffMeasure_image`), so μHE[n](B) = μHE[n](ι(Q)) = μHE[n](Q), where on the right μHE[n] is the measure on EuclideanSpace ℝ (Fin n). On EuclideanSpace ℝ (Fin n), μHE[n] = volume (`EuclideanSpace.euclideanHausdorffMeasure_eq_volume`).
5. Volume of the cube. Q is the preimage of the closed box Icc (fun _ ↦ a) (fun _ ↦ b) ⊆ (Fin n → ℝ) under WithLp.ofLp, and WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ) is volume preserving (`PiLp.volume_preserving_ofLp`). The box is measurable, so volume(Q) = volume(Icc (fun _ ↦ a) (fun _ ↦ b)) (`MeasurePreserving.measure_preimage`) = Π_{j ∈ Fin n} ENNReal.ofReal(b − a) (`Real.volume_Icc_pi`) = ENNReal.ofReal(b − a)^n (`Finset.prod_const`, card (Fin n) = n) = ENNReal.ofReal((b − a)^n) (`ENNReal.ofReal_pow`, using b − a ≥ 0, which is where a ≤ b is needed).
6. By steps 4 and 5, μHE[n](B) = ENNReal.ofReal((b − a)^n). (No case split on n is needed; for n = 0, B = {WithLp.toLp 2 c} and Q is the one-point space, both of measure 1.)

## Key steps

1. Parametrize B by ι(y)_i = c_i + Σ_j [α(j) = i] y_j on EuclideanSpace ℝ (Fin n).
2. ι is an isometry: coordinates off range α cancel and the rest reindex along the injective α.
3. ι maps the cube Q = [a, b]^n onto B, with explicit preimage y_j = x_{α(j)} − c_{α(j)}.
4. Isometry invariance of μHE[n] and μHE[n] = volume on EuclideanSpace ℝ (Fin n) give μHE[n](B) = volume(Q).
5. volume(Q) = Π_j ofReal(b − a) = ofReal((b − a)^n) via PiLp.volume_preserving_ofLp and Real.volume_Icc_pi.

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
