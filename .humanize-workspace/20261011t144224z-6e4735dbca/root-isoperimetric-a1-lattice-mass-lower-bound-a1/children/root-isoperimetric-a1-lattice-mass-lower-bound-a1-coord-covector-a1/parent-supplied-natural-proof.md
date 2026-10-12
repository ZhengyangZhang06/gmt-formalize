# Parent-supplied natural-language proof

- Parent DAG node: `root.isoperimetric-a1.lattice_mass_lower_bound-a1`
- Child DAG node: `root.isoperimetric-a1.lattice_mass_lower_bound-a1.coord_covector-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1 and 5 of the parent proof (the covector dx^α, its Kronecker evaluation on coordinate frames, and the coefficient-norm computation covectorEuclideanNorm(λ • dx^α) = |λ|), stated for a general degree n. Notation: η := dx^α = wedgeCovectors n (fun i ↦ EuclideanSpace.proj (α i)); e_a := EuclideanSpace.single a (1 : ℝ) ∈ ℝ^N; for I : Fin n → Fin N write e_I := (e_{I(1)}, …, e_{I(n)}).

1. Evaluation formula. Let I : Fin n → Fin N be arbitrary. By `wedgeCovectors_apply_det` (SimonGMT, Chapter06/FormsDuality.lean), η(e_I) = det M_I, where M_I is the n × n real matrix with entries (M_I)_{ij} = proj_{α(i)}(e_{I(j)}) = (e_{I(j)})_{α(i)}. The a-th coordinate of e_b is 1 if a = b and 0 otherwise (`EuclideanSpace.coe_proj`, `PiLp.single_apply`), so (M_I)_{ij} = 1 if α(i) = I(j) and (M_I)_{ij} = 0 otherwise.
2. Proof of the first conjunct. Take I = α (the underlying function of α). Because α is injective, α(i) = α(j) iff i = j (`α.injective.eq_iff`), so (M_α)_{ij} = 1 if i = j and 0 otherwise; that is, M_α is the identity matrix (`Matrix.one_apply`). Hence η(e_{α(1)}, …, e_{α(n)}) = det 1 = 1 (`Matrix.det_one`).
3. Vanishing on the other strictly increasing frames. Let I : Fin n → Fin N be strictly increasing with I ≠ α as functions. Claim: some α(i) ∉ range I. Suppose instead that α(i) ∈ range I for every i, i.e. range α ⊆ range I. Since α and I are injective maps out of Fin n, both ranges are finite sets with exactly n elements (`Set.ncard_range_of_injective`: ncard(range α) = Nat.card (Fin n) = n, and likewise for I); a subset of a finite set having at least as many elements is the whole set (`Set.eq_of_subset_of_ncard_le`), so range α = range I. Two strictly increasing maps out of the well-ordered set Fin n with the same range are equal (`StrictMono.range_inj_of_wellFoundedLT`), so I = α, a contradiction. Fix such an i. For every j, α(i) ≠ I(j) (otherwise α(i) = I(j) ∈ range I), so the whole row i of M_I is zero and det M_I = 0 (`Matrix.det_eq_zero_of_row_eq_zero`). Thus η(e_I) = 0.
4. Proof of the second conjunct. Let α' : Fin n ↪o Fin N with α' ≠ α. Its underlying function I := α' is strictly increasing (`α'.strictMono`), and I ≠ α as functions, because an order embedding is determined by its underlying function (`DFunLike.coe_injective`). By step 3, η(e_{α'(1)}, …, e_{α'(n)}) = η(e_I) = 0.
5. Proof of the third conjunct. Fix c ∈ ℝ. By the definition of covectorEuclideanNorm, covectorEuclideanNorm(c • η) = sqrt(Σ_{I : Fin n → Fin N} s_I), where s_I := ((c • η)(basisFun(I(1)), …, basisFun(I(n))))² if I is strictly increasing and s_I := 0 otherwise. Here basisFun(a) = e_a (`EuclideanSpace.basisFun_apply`) and (c • η)(v) = c · η(v) (`ContinuousAlternatingMap.smul_apply`). We show s_I = (c² if I = α else 0) for every I: (a) if I = α, which is strictly increasing, s_I = (c · 1)² = c² by step 2; (b) if I is strictly increasing and I ≠ α, s_I = (c · 0)² = 0 by step 3; (c) if I is not strictly increasing, then I ≠ α (α is strictly increasing) and s_I = 0 by definition. Hence Σ_I s_I = Σ_I (c² if I = α else 0) = c² (`Finset.sum_ite_eq'`, as α ∈ Finset.univ), and covectorEuclideanNorm(c • η) = sqrt(c²) = |c| (`Real.sqrt_sq_eq_abs`).
6. Steps 2, 4 and 5 are exactly the three conjuncts of the statement. (The argument needs no case split on n: for n = 0, M_I is the empty matrix with determinant 1, Fin 0 → Fin N has the single element α, and step 3 is vacuous.)

## Key steps

1. wedgeCovectors_apply_det: dx^α(e_I) = det M_I with (M_I)_{ij} = 1 if α(i) = I(j), else 0.
2. I = α: M_α is the identity matrix (α injective), so dx^α(e_α) = 1.
3. Strictly increasing I ≠ α: equal-size ranges and StrictMono.range_inj_of_wellFoundedLT give some α(i) ∉ range I; that row of M_I is zero, so dx^α(e_I) = 0.
4. An order embedding α' ≠ α has underlying function ≠ α, so dx^α(e_{α'}) = 0.
5. In covectorEuclideanNorm(c • dx^α) only the summand I = α survives and contributes c²; sqrt(c²) = |c|.

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
