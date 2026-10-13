# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_critical-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. n := m+1; ℝ^k = Eucl k with norm |·|; Lⁿ = volume on ℝⁿ, which equals μHE[n] there (`EuclideanSpace.euclideanHausdorffMeasure_eq_volume`); Hᵏ := μHE[k] on ℝ^P (outer-measure values on arbitrary sets); Dh(w) := fderiv ℝ h w with operator norm ‖·‖. B(w, r) is the open ball. E₀ := Ω ∩ Φ⁻¹(W), which is Borel (Φ continuous, Ω open, W Borel). By hypothesis f(Φ w) = h(w) and Dh(w) = 0 for every w ∈ E₀.
Source. Simon Ch. 2, consequence of 6.3 stated after it (“if C = {J f = 0} then H^k(C ∩ f⁻¹(y)) = 0 for Lᵐ-a.e. y”) and the C¹ Sard-type Theorem 6.4, for the critical set of the C¹ function F := h∘(Φ|Ω)⁻¹ on the C¹ chart image Φ(Ω). It is proved from Eilenberg's inequality, Federer 2.10.25, i.e. the sibling lemma eilenberg: for every m there is C ≥ 0 such that, whenever f is L-Lipschitz on A ⊆ ℝ^P, some Borel φ satisfies H^m(A ∩ f⁻¹{t}) ≤ φ(t) for all t and ∫φ ≤ C·L·H^{m+1}(A). Let C be this constant for m. Let K and c > 0 be the constants from the hypotheses: Φ is K-Lipschitz on Ω and c|w − w′| ≤ |Φ w − Φ w′| for w, w′ ∈ Ω.

1. (Basic facts.) Φ is injective on Ω. Since W ⊆ Φ(Ω), every x ∈ W equals Φ(w) for some w ∈ E₀, so W = Φ(E₀).

2. (Localization.) Fix R ∈ ℕ and ε > 0, and put E^R := E₀ ∩ B(0, R) (Borel, Lⁿ(E^R) ≤ Lⁿ(B(0, R)) < ∞).
 - For w₀ ∈ E^R, Dh(w₀) = 0 and Dh is continuous (h is C¹). So there is r(w₀) > 0 with ‖Dh(z)‖ ≤ ε for all z ∈ B(w₀, r(w₀)).
 - ℝⁿ is second countable, so countably many of these balls, B_k := B(w_k, r(w_k)) (k ∈ ℕ), cover E^R (Lindelöf, `TopologicalSpace.isOpen_iUnion_countable`). If E^R = ∅ the claim of step 6 below is trivial.
 - Put D_k := (E^R ∩ B_k) ∖ ⋃_{l<k} B_l. These are Borel, pairwise disjoint, and ⋃_k D_k = E^R.

3. (Small Lipschitz constant.) For w, w′ ∈ D_k ⊆ B_k, the ball B_k is convex and ‖Dh‖ ≤ ε on it. The mean value inequality (`Convex.norm_image_sub_le_of_norm_fderiv_le`) gives |h(w) − h(w′)| ≤ ε|w − w′|.
 For x = Φ(w) and x′ = Φ(w′) in Φ(D_k) (w, w′ ∈ D_k ⊆ E₀):
 |f(x) − f(x′)| = |h(w) − h(w′)| ≤ ε|w − w′| ≤ (ε/c)|x − x′|.
 So f is (ε/c)-Lipschitz on Φ(D_k).

4. (Eilenberg on each piece.) By eilenberg (with m, P, f, L := ε/c ∈ ℝ≥0, A := Φ(D_k)) there is a Borel φ_k with H^m(Φ(D_k) ∩ f⁻¹{t}) ≤ φ_k(t) for every t and ∫φ_k ≤ C(ε/c)·Hⁿ(Φ(D_k)).
 Since Φ is K-Lipschitz on D_k ⊆ Ω, Hⁿ(Φ(D_k)) ≤ Kⁿ·μHE[n](D_k) = Kⁿ Lⁿ(D_k) (SimonGMT `Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn`).

5. (Summation.) Put ψ_ε := Σ_k φ_k (Borel).
 - Φ(E^R) ∩ f⁻¹{t} = ⋃_k (Φ(D_k) ∩ f⁻¹{t}), so countable subadditivity gives H^m(Φ(E^R) ∩ f⁻¹{t}) ≤ ψ_ε(t) for every t.
 - By `lintegral_tsum` and additivity of Lⁿ on the disjoint Borel D_k:
 ∫ψ_ε = Σ_k ∫φ_k ≤ C(ε/c)Kⁿ Σ_k Lⁿ(D_k) = C(ε/c)Kⁿ Lⁿ(E^R) ≤ ε · C Kⁿ Lⁿ(B(0,R))/c.

6. (ε ↓ 0.) Take ε := 1/j (j ≥ 1) and let ψ := inf_j ψ_{1/j}, which is Borel.
 - H^m(Φ(E^R) ∩ f⁻¹{t}) ≤ ψ(t) for every t.
 - ∫ψ ≤ ∫ψ_{1/j} ≤ (1/j)·C Kⁿ Lⁿ(B(0,R))/c for every j, so ∫ψ = 0.
 Hence ψ = 0 Lebesgue-a.e. (`lintegral_eq_zero_iff`), i.e. H^m(Φ(E^R) ∩ f⁻¹{t}) = 0 for a.e. t.

7. (Union over R.) W = Φ(E₀) = ⋃_{R∈ℕ} Φ(E^R), so W ∩ f⁻¹{t} = ⋃_R (Φ(E^R) ∩ f⁻¹{t}). For t outside the countable union of the exceptional null sets of step 6 (`ae_all_iff`), every term is H^m-null, hence H^m(W ∩ f⁻¹{t}) = 0 (`measure_iUnion_null`). Thus H^m(W ∩ f⁻¹{t}) = 0 for Lebesgue-a.e. t. ∎

## Key steps

1. W = Φ(E₀) with E₀ := Ω ∩ Φ⁻¹(W) Borel; localize to E^R := E₀ ∩ B(0,R).
2. By continuity of Dh (= 0 on E₀), countably many balls with ‖Dh‖ ≤ ε cover E^R; disjointify to Borel D_k.
3. On Φ(D_k), f is (ε/c)-Lipschitz (mean value inequality and the antilipschitz bound).
4. eilenberg on each Φ(D_k) and Hⁿ(Φ(D_k)) ≤ Kⁿ Lⁿ(D_k): the slices of Φ(E^R) are dominated by ψ_ε with ∫ψ_ε ≤ ε·C Kⁿ Lⁿ(B(0,R))/c.
5. ε = 1/j → 0 gives null slices a.e.; take the union over R.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean (byte-identical); read Contract.lean (IsRectifiableTriple, Eucl, scope commands)`
- `grep -rn 'slicing_im_coarea_' local-references/197bdd4b88278494/project (no match)`
- `python3 scan of dag.json: statuses and lean_statement of all lipschitz_pushforward nodes; byte comparison of candidate child types with lpf_c1_approximation_real, lpf_countably_rectifiable_c1_cover, lpf_weighted_tangent_on_c1_chart (identical, all speculative-ready) and lpf_ccr_hasDerivAt_line_of_comp (accepted 18:04Z, Eucl Q-valued); collision check of the nine names against all 369 DAG lean_name values (none)`
- `read nodes/root-lipschitz-pushforward-im-a1-{countably-rectifiable-c1-cover-a1,weighted-tangent-on-c1-chart-a1,lipschitz-c1-immersion-pieces-a1-c1-b45cce92e1,chart-chain-rule-a1-line-deriv-comp-a1}/parent-supplied-natural-proof.md and nodes/root-slicing-a1-slice-integer-multiplicity-a1/{parent-supplied-natural-proof.md,decomposition-v1.json}`
- `grep -n '^theorem|^def' SimonGMT Chapter03/{Rectifiable,Differential,DisjointCover,SubmanifoldCover}.lean and Chapter02/{AreaLipschitz,AreaDomain,AreaCritical,Area,Lipschitz,CoareaLinear,CoareaProjection,WhitneyExtension}.lean`
- `grep for SimonGMT names weighted_area_formula_lipschitzOn_fiberSum, weighted_area_formula_lipschitz_injOn, injective_area_formula_lipschitzOn, area_image_criticalSet_eq_zero, euclideanHausdorffMeasure_image_le_of_lipschitzOn, exists_contDiff_one_extension_of_whitney, exists_isClosed_continuousOn_of_measurable, simon_theorem_3_6, coarea_projection_lintegral (all present)`
- `grep in pinned Mathlib for hausdorffMeasure_apply, hausdorffMeasure_le_liminf_tsum, euclideanHausdorffMeasure_def, addHaarScalarFactor_volume_hausdorffMeasure_ne_zero, normDet_comp_of_finrank_eq, normDet_eq_abs_det, normDet_codRestrict, lintegral_image_eq_lintegral_abs_det_fderiv_mul, OpenPartialHomeomorph.contDiffAt_symm, measurePreserving_piFinSuccAbove, PiLp.volume_preserving_ofLp, Measurable.lintegral_prod_right', MeasurableSet.image_of_continuousOn_injOn, NullMeasurableSet.exists_measurable_subset_ae_eq, Measure.restrict_apply₀', restrict_congr_set, lintegral_iUnion, lintegral_tsum, lintegral_inter_add_sdiff, LipschitzOnWith.extend_real, isOpen_iUnion_countable (all present)`
- `sed book/chapter-02.txt §6 (6.1–6.7) and book/chapter-03.txt §1–2 (1.1–1.9, 2.1–2.10)`
- `lake build GMT.Ch06.Submission in scratch /tmp/coarea-decomp-47PgtZ/proj (frozen d8d46c9 contract, shared lake-packages-25730c7c)`
- `lake env lean Scratch/Stmts.lean and Scratch/FinalCheck.lean (nine child types and the parent type in the exact comparator scope; 0 errors)`
- `lake env lean Scratch/Assembly.lean (parent type from eilenberg, glue, pieces, chart_critical, chart_regular; #print axioms: propext, Classical.choice, Quot.sound)`
- `lake env lean Scratch/Pieces.lean (pieces from c1_approx, chart_cover, chart_tangent, line_deriv; standard axioms) and Scratch/GradId.lean`
- `lake env lean Scratch/Glue.lean (glue proved outright; standard axioms); lake env lean Scratch/Review_C1.lean (c1_approx from the accepted lpf_c1r_lusin_closed, lpf_c1r_uniform_remainder, lpf_c1r_whitney_extension types; standard axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Disjointed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaProjection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-countably-rectifiable-c1-cover-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-b45cce92e1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1-line-deriv-comp-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/coarea-decomp-47PgtZ/proj/Scratch/Stmts.lean`
- `/tmp/coarea-decomp-47PgtZ/proj/Scratch/FinalCheck.lean`
- `/tmp/coarea-decomp-47PgtZ/proj/Scratch/Assembly.lean`
- `/tmp/coarea-decomp-47PgtZ/proj/Scratch/Pieces.lean`
- `/tmp/coarea-decomp-47PgtZ/proj/Scratch/Glue.lean`
- `/tmp/coarea-decomp-47PgtZ/proj/Scratch/GradId.lean`
- `/tmp/coarea-decomp-47PgtZ/proj/Scratch/Review_C1.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 contract. Submission is byte-identical to it, and no `slicing_im_coarea_*` name exists in the project or in the 369 DAG nodes. SimonGMT supplies the needed area-formula library: weighted_area_formula_lipschitzOn_fiberSum, injective_area_formula_lipschitzOn, area_image_criticalSet_eq_zero, euclideanHausdorffMeasure_image_le_of_lipschitzOn, a Whitney extension (source only, no .olean), Lusin, the upper density theorem, the linear co-area formula and HasWeightedApproximateTangentSpaceAt with uniqueness. It has no nonlinear co-area formula and no Eilenberg inequality. Mathlib supplies the Hausdorff measure covering lemmas, the μHE normalization, normDet, the inverse function theorem, change of variables, Fubini/Tonelli and Lusin–Souslin. The lipschitz-pushforward branch has speculative-ready nodes byte-identical to three proposed children (c1_approx, chart_cover, chart_tangent); because they are not accepted, they get new names here, and their accepted sub-lemmas (lpf_c1r_*, lpf_wtc_*, lpf_c1_local_antilipschitz, lpf_raf_chart_change_of_variables) are cited for reuse at the next level. lpf_ccr_hasDerivAt_line_of_comp was accepted during this session and is cited as an alternative route for line_deriv. Lean checks in the exact comparator scope: all nine child types elaborate; the parent type follows from five children; pieces follows from four; glue is proved outright; c1_approx follows from three accepted types. All of these use only propext, Classical.choice and Quot.sound. These checks do not certify the remaining analytic proofs.
