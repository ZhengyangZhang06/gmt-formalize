# Parent-supplied natural-language proof

- Parent DAG node: `root.isoperimetric-a1.lattice_mass_lower_bound-a1`
- Child DAG node: `root.isoperimetric-a1.lattice_mass_lower_bound-a1.isolating_form-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 5, 6 (the vanishing of each [[F]](ω) for F ≠ F₀; the lattice sum itself is left to the parent) and 8 of the parent proof, together with the F₀-specific parts of steps 2 and 7, taken with the sign s := 1; the parent's assembly recovers the sign by using ω or −ω. Parent step 1 is supplied by the sibling coord_covector, steps 2–4 by face_cutoff and step 7 by box_measure. Notation: write F₀ = (z, α) with z ∈ ℤ^N and α : Fin n ↪o Fin N; A := range α; e_a := EuclideanSpace.single a (1 : ℝ); for a face index F = (z', α'), latticeFaceAction ρ F ω = ∫_{latticeFace ρ F} ω(x)(e_{α'(1)}, …, e_{α'(n)}) dμHE[n](x).

1. Ingredients. Let η := wedgeCovectors n (fun i ↦ EuclideanSpace.proj (α i)). By coord_covector: η(e_{α(1)}, …, e_{α(n)}) = 1; η(e_{α'(1)}, …, e_{α'(n)}) = 0 for every α' : Fin n ↪o Fin N with α' ≠ α; and covectorEuclideanNorm(c • η) = |c| for every real c. By face_cutoff, applied to n, N, ρ, δ, z, α (it uses only ρ > 0 and δ > 0), there is φ : ℝ^N → ℝ with ContDiff ℝ (⊤ : ℕ∞) φ, HasCompactSupport φ, 0 ≤ φ(x) ≤ 1 for all x, φ(x) = 1 for all x ∈ K := {x : ρ(z_i + δ) ≤ x_i ≤ ρ(z_i + 1 − δ) for i ∈ A, x_i = ρ z_i for i ∉ A}, and φ(x) = 0 for all x ∈ latticeFace ρ (z', α) whenever z' ≠ z.
2. The test form. Let ω₀(x) := φ(x) • η. It is C^∞ of order (⊤ : ℕ∞), as the product of the smooth scalar function φ with a constant covector (`ContDiff.smul` with `contDiff_const`), so ω₀ is a smooth form (IsSmoothForm means ContDiff ℝ ∞ with ∞ = (⊤ : ℕ∞)); its support lies in the support of φ, so it has compact support (`HasCompactSupport.smul_right`); and tsupport ω₀ ⊆ univ trivially. Hence ω₀ ∈ TestFormOn univ n; let ω be this element. For all x and all v : Fin n → ℝ^N, ω(x)(v) = φ(x) · η(v).
3. Admissibility. tsupport ω ⊆ univ, and for every x, covectorEuclideanNorm(ω(x)) = covectorEuclideanNorm(φ(x) • η) = |φ(x)| = φ(x) ≤ 1 by step 1 and 0 ≤ φ(x) ≤ 1. Hence ω ∈ massAdmissibleOn univ n univ.
4. Faces F ≠ F₀ contribute 0. Let F = (z', α') with F ≠ F₀. Case α' ≠ α: for every x the integrand is ω(x)(e_{α'(1)}, …, e_{α'(n)}) = φ(x) · 0 = 0 (step 1), so latticeFaceAction ρ F ω = ∫ 0 = 0 (`integral_zero`). Case α' = α: then z' ≠ z (otherwise F = (z, α) = F₀), and for every x ∈ latticeFace ρ (z', α) the integrand is φ(x) · η(e_{α(1)}, …, e_{α(n)}) = 0 · 1 = 0 by step 1; a set integral of a function vanishing on the set is 0 (`setIntegral_eq_zero_of_forall_eq_zero`). In both cases latticeFaceAction ρ F ω = 0.
5. The F₀ term. For every x, ω(x)(e_{α(1)}, …, e_{α(n)}) = φ(x) · 1 = φ(x), so latticeFaceAction ρ F₀ ω = ∫_{latticeFace ρ F₀} φ dμHE[n].
6. Two measures, from box_measure with c_i := ρ z_i. For i ∈ A, the condition ρ z_i ≤ x_i ≤ ρ(z_i + 1) is equivalent to c_i + 0 ≤ x_i ≤ c_i + ρ, and for i ∉ A both sets require x_i = c_i; so latticeFace ρ F₀ is the box of box_measure with (a, b) = (0, ρ), 0 ≤ ρ, and μHE[n](latticeFace ρ F₀) = ENNReal.ofReal(ρ^n) < ∞. Similarly ρ(z_i + δ) ≤ x_i ≤ ρ(z_i + 1 − δ) is equivalent to c_i + ρδ ≤ x_i ≤ c_i + ρ(1 − δ), and ρδ ≤ ρ(1 − δ) because δ < 1/4 < 1/2 and ρ > 0; so box_measure gives μHE[n](K) = ENNReal.ofReal((ρ(1 − δ) − ρδ)^n) = ENNReal.ofReal((ρ(1 − 2δ))^n).
7. Inclusion, measurability, integrability. K ⊆ latticeFace ρ F₀: for i ∈ A, ρ z_i ≤ ρ(z_i + δ) ≤ x_i ≤ ρ(z_i + 1 − δ) ≤ ρ(z_i + 1) (ρ > 0, δ > 0), and for i ∉ A the conditions coincide. K is closed, being the intersection over i of closed half-spaces (i ∈ A) or closed hyperplanes (i ∉ A) in the continuous coordinates x ↦ x_i; hence K is measurable. φ is continuous (it is C^∞), hence a.e. strongly measurable, and |φ| ≤ 1; since μHE[n](latticeFace ρ F₀) < ∞ (step 6), φ is integrable on latticeFace ρ F₀ (`Measure.integrableOn_of_bounded`).
8. Lower bound. Since ρ > 0 and 1 − 2δ > 0, the real number (ρ(1 − 2δ))^n is ≥ 0, so (ρ(1 − 2δ))^n = μHE[n](K).toReal (step 6, `ENNReal.toReal_ofReal`) = ∫_K 1 dμHE[n] (`setIntegral_const`) = ∫_K φ dμHE[n] (φ = 1 on the measurable set K, `setIntegral_congr_fun`) ≤ ∫_{latticeFace ρ F₀} φ dμHE[n] (`setIntegral_mono_set`: φ is integrable on latticeFace ρ F₀, φ ≥ 0 there, and K ⊆ latticeFace ρ F₀) = latticeFaceAction ρ F₀ ω (step 5).
9. Steps 2, 3, 4 and 8 show that ω has all the required properties.

## Key steps

1. Take η = dx^α (coord_covector) and the cut-off φ for (z, α, δ) (face_cutoff), where F₀ = (z, α).
2. ω := φ • η is a C^∞ compactly supported form, and covectorEuclideanNorm(φ(x) • η) = φ(x) ≤ 1 makes it mass-admissible.
3. Faces with α' ≠ α see η(e_{α'}) = 0; faces (z', α) with z' ≠ z see φ = 0; so [[F]](ω) = 0 for every F ≠ F₀.
4. [[F₀]](ω) = ∫_{F₀} φ dμHE[n]; box_measure gives μHE[n](F₀) = ρ^n < ∞ and μHE[n](K) = (ρ(1 − 2δ))^n.
5. φ is integrable on F₀, φ ≥ 0, φ = 1 on the closed set K ⊆ F₀, hence [[F₀]](ω) ≥ μHE[n](K) = (ρ(1 − 2δ))^n.

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
