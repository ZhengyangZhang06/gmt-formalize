# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.c1_approx-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 2, Theorem 1.5 (C¹ Approximation Theorem) and its printed proof (chapter-02.txt lines 165–268, printed pp. 42–44). Whitney's extension theorem 1.6 is available as SimonGMT `exists_contDiff_one_extension_of_whitney`; its hypothesis 1.6(*) is the structure `HasWhitneyC1Compatibility A h D` (h and D continuous on A, and for every compact K' ⊆ A and η > 0 there is δ > 0 with |h(y) − h(x) − D(x)(y − x)| ≤ η|y − x| for x ∈ K', y ∈ A, |x − y| < δ). The printed proof is copied. The details it leaves implicit are written out: Lusin's and Egorov's theorems for the infinite measure Lⁿ (via bounded shells), measurability of the remainder suprema, and closedness of the final set. This theorem is used by the sibling chart_pieces, as Simon uses it in Ch. 3, Lemma 1.2 and in the proof of 2.4.

Notation. Lⁿ := volume on ℝⁿ. Df(x) := fderiv ℝ f x. |·| is the Euclidean norm and ‖λ‖ the operator norm of a linear functional λ. For j ≥ 1 let S_j := {x : j − 1 ≤ |x| < j}. The S_j are bounded Borel sets partitioning ℝⁿ, and a bounded set meets only finitely many of the closed shells S̄_j ⊆ {j − 1 ≤ |x| ≤ j}.

1. Reductions. It suffices to treat ε < ∞: a g that works for min{ε, 1} works for ε. If n = 0, then ℝⁿ is a point and g := f works (a constant function is C¹ and the set in question is empty). Fix n ≥ 1 and ε ∈ (0, ∞).

2. Rademacher (Simon 1.4; SimonGMT `rademacher_ae_differentiableAt`, Mathlib `LipschitzWith.ae_differentiableAt`). The set B of points where f is differentiable is Borel (Mathlib `measurableSet_of_differentiableAt`) and Lⁿ(ℝⁿ ∖ B) = 0. The map x ↦ Df(x) is Borel (Mathlib `measurable_fderiv`), and ‖Df(x)‖ ≤ K for every x.

3. Lusin (Simon 1.17; SimonGMT `IsBorelRegularOuterMeasure.exists_isClosed_continuousOn`). Its hypotheses hold for the Lebesgue outer measure (volume.toOuterMeasure), which is Borel regular (every set has a measurable superset of equal measure, Mathlib `MeasureTheory.exists_measurable_superset`), and in ℝⁿ closed sets are G_δ (ClosedSetsAreGDelta). Fix j. Apply it, on the finite-measure Borel set S_j ∩ B, to each of the n real coordinate functions x ↦ Df(x)(e_i), with tolerance ε2^{−j−2}/n each, and intersect the n closed sets obtained. This gives a closed C_j ⊆ S_j ∩ B with Lⁿ((S_j ∩ B) ∖ C_j) < ε2^{−j−2} and Df|_{C_j} continuous (all coordinates are continuous on C_j). Put C := ⋃_j C_j.
 - C is closed and Df|_C is continuous. Since C_j ⊆ S̄_j, every point has a neighbourhood meeting only finitely many C_j. A union of a locally finite family of closed sets is closed, and a map that is continuous on each of finitely many closed sets is continuous on their union.
 - C ⊆ B, and Lⁿ(ℝⁿ ∖ C) ≤ Lⁿ(ℝⁿ ∖ B) + Σ_j Lⁿ((S_j ∩ B) ∖ C_j) < ε/4.

4. Remainders (the function R of 1.6(*)). For x, y ∈ C with x ≠ y put R(x, y) := (f(y) − f(x) − Df(x)(y − x))/|y − x|. Then |R(x, y)| ≤ 2K. For k ≥ 1 and x ∈ C put ρ_k(x) := sup{|R(x, y)| : y ∈ C, 0 < |y − x| < 1/k}, with sup ∅ := 0.
 - Since f is differentiable at every x ∈ C ⊆ B, ρ_k(x) decreases to 0 as k → ∞, for every x ∈ C. This is Simon's "lim_{y→x, y∈C} R(x, y) = 0 for all x ∈ C".
 - Each ρ_k is Borel on C. Let D ⊆ C be countable and dense in C. For fixed x, y ↦ R(x, y) is continuous on C ∖ {x}. Every y ∈ C with 0 < |y − x| < 1/k is a limit of points of D with the same property, because that condition is open in y. Hence ρ_k(x) = sup_{y∈D} |R(x, y)|·1_{0<|y−x|<1/k}. Each term is Borel in x ∈ C, because f is continuous and Df|_C is continuous; a countable supremum of Borel functions is Borel.

5. Egorov (Mathlib `MeasureTheory.tendstoUniformlyOn_of_ae_tendsto`, applied on the finite-measure sets C ∩ S_j).
 - For each j there is a measurable A_j ⊆ C ∩ S_j with Lⁿ((C ∩ S_j) ∖ A_j) < ε2^{−j−2} such that ρ_k → 0 uniformly on A_j. Put A₀ := ⋃_j A_j. Then Lⁿ(C ∖ A₀) < ε/4, and ρ_k → 0 uniformly on A₀ ∩ {|x| ≤ R} for every R, since this set meets only finitely many A_j.
 - By inner regularity of Lⁿ choose closed F_j ⊆ A_j with Lⁿ(A_j ∖ F_j) < ε2^{−j−2}, and put A := ⋃_j F_j. A is closed, since the F_j ⊆ S̄_j form a locally finite family. Moreover A ⊆ A₀ ⊆ C, and Lⁿ(ℝⁿ ∖ A) ≤ Lⁿ(ℝⁿ ∖ C) + Lⁿ(C ∖ A₀) + Lⁿ(A₀ ∖ A) < 3ε/4 < ε. This is Simon's closed set A with Lⁿ(ℝⁿ ∖ A) < ε.

6. Whitney's hypothesis 1.6(*). Put h := f and D(x) := Df(x).
 - h is continuous, and D is continuous on A ⊆ C (step 3).
 - Let K' ⊆ A be compact and η > 0. Then K' ⊆ {|x| ≤ R} for some R, so by step 5 there is k with ρ_k ≤ η on K'. Put δ := 1/k. For x ∈ K' and y ∈ A with 0 < |x − y| < δ: |h(y) − h(x) − D(x)(y − x)| = |R(x, y)|·|y − x| ≤ ρ_k(x)|y − x| ≤ η|y − x|. The case y = x is trivial.
 Hence HasWhitneyC1Compatibility A h D holds.

7. Whitney's theorem (Simon 1.6; SimonGMT `exists_contDiff_one_extension_of_whitney`, A closed). There is g : ℝⁿ → ℝ with ContDiff ℝ 1 g, g = f on A, and HasFDerivAt g (Df(a)) a for every a ∈ A, so Dg(a) = Df(a) on A.

8. Conclusion. If x ∈ A, then f(x) = g(x) and Df(x) = Dg(x). So {x : f(x) ≠ g(x) ∨ Df(x) ≠ Dg(x)} ⊆ ℝⁿ ∖ A, which has Lebesgue measure < ε by step 5. ∎

## Key steps

1. Rademacher: f is differentiable off an Lⁿ-null Borel set B, and Df is Borel.
2. Lusin on bounded shells: a closed C ⊆ B with Lⁿ(ℝⁿ∖C) < ε/4 and Df|_C continuous.
3. The Taylor remainder suprema ρ_k(x) on C are Borel and decrease to 0.
4. Egorov on bounded shells and inner regularity: a closed A ⊆ C with Lⁿ(ℝⁿ∖A) < ε and ρ_k → 0 uniformly on bounded subsets of A, i.e. Whitney's condition 1.6(*).
5. Whitney's C¹ extension (SimonGMT exists_contDiff_one_extension_of_whitney) gives g ∈ C¹ with g = f and Dg = Df on A.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD in the snapshot project (b4d606db1) and mathlib (25730c7c); diff snapshot GMT/Ch07/Contract.lean against the workspace Contract.lean and Submission.lean (identical; Submission is a byte copy)`
- `grep -rn 'coarea\|co_area\|CoArea\|Coarea' Poincare/SimonGMT (only Chapter02/CoareaLinear*.lean, CoareaProjection.lean: linear co-area 6.1–6.2)`
- `grep -n '^theorem\|^def' on SimonGMT Chapter02/{AreaFormula,AreaLipschitz,AreaCritical,AreaNoninjective,WeightedArea,AreaLinearWeighted,WhitneyExtension,WhitneyJet,Lipschitz,LipschitzMeasurability,UpperIntegral,Submanifold,SubmanifoldCalculus}.lean, Chapter01/Lusin.lean, Chapter03/{Rectifiable,Differential,SubmanifoldCover,DisjointCover,CoordinateProjection}.lean`
- `grep 'Eilenberg\|1\.9' and 'theorem.*[Ll]usin' in SimonGMT and Mathlib (no Eilenberg inequality; Lusin only as SimonGMT IsBorelRegularOuterMeasure.exists_isClosed_continuousOn)`
- `grep in snapshot mathlib for tendstoUniformlyOn_of_ae_tendsto, exists_measurable_superset_of_null, measurable_fderiv, integral_lineDeriv_mul_eq, LocallyIntegrable.ae_hasDerivAt_integral, lintegral_image_eq_lintegral_abs_det_fderiv_mul, Real.volume_le_diam, hausdorffMeasure_apply, ae_tendsto_measure_inter_div, LipschitzOnWith.extend_real, Integrable.exists_hasCompactSupport_integral_sub_le, ContDiffAt.toOpenPartialHomeomorph, OpenPartialHomeomorph.contDiffAt_symm, AlternatingMap.eq_smul_basis_det, EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp, measurePreserving_piFinSuccAbove; sed Mathlib/Geometry/Euclidean/Volume/Measure.lean (μHE[d] = addHaarScalarFactor • μH[d])`
- `python3 -I scans of dag.json (995 nodes) for slic|coarea|Lusin|C¹ approximation|approximate tangent|tangential gradient: dor_lmb_slicing_lipschitz and its children (speculative/decomposing), cmc_slice_mass_bounds (speculative-ready) with accepted cmcs_* children, codim1_rdo_c1_approximation (waiting-children), codim1_rdo_c1_piece_approxTangent (speculative-lean), codim1_rdo_rectifiable_ae_approxTangent (speculative-ready), codim1_rdo_c1cov_lipschitz_range_c1_cover (rlcr-lean), dimred_cs_sos_spine_coarea, idtp_carrier_area_formula, dpf_area_formula_bilipschitz_rectifiable (none accepted)`
- `git show <accepted candidate commit>:GMT/Ch07/Submission.lean and whitespace-normalised comparison for cmc_imRep_locality_restrict_sub (2af75d6), cmcs_cd_defect_identity (e32f0ad), cmcs_lipschitz_smoothing (00c458d): all IDENTICAL`
- `grep -c dtc_bc_lc_sl_ dag.json (0); git log --all -S 'dtc_bc_lc_sl_' over 4526 refs (no match)`
- `lake env lean /tmp/dtcslice/Types.lean, /tmp/dtcslice/Check1.lean, /tmp/dtcslice/challenges/Challenge_<key>.lean (12 modules generated by verifier gmt-compare.py child_modules, contract mode, after lean_contract.validate_lean_statement) and /tmp/dtcslice/AssemblyFinal.lean with #print axioms`
- `sed book/chapter-06.txt lines 1140–1370 (Ch. 6 §4: 4.1–4.9); book/chapter-03.txt lines 1–170 and 320–460 (1.1–1.6, 2.1–2.10); book/chapter-02.txt lines 160–430 (1.5–1.10) and 1360–1640 (6.1–6.7)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-09907e06c7/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-comparison-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaFormula.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLinearWeighted.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/UpperIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/LebesgueDifferentiationThm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/dtcslice/Types.lean`
- `/tmp/dtcslice/AssemblyFinal.lean`
- `/tmp/dtcslice/challenges`

The pinned SimonGMT library has the linear co-area formula, the injective, weighted and noninjective Lipschitz area formulas, null critical images, Rademacher, Lusin, the C¹ Whitney extension and the upper integral. It has no nonlinear co-area formula, no C¹ approximation theorem (Simon 2.1.5), no Eilenberg inequality (2.1.9), no Lemma 1.2 'only if', no tangential gradient of Lipschitz functions on rectifiable sets and no slicing. Mathlib supplies Egorov, Lebesgue differentiation, integration by parts for Lipschitz functions, change of variables, the inverse function theorem and the μHE normalisation. No DAG node proving the co-area formula or slicing is accepted. The closest node, dor_lmb_slicing_lipschitz, is the same theorem for open U; it is speculative, and its decomposition was reviewed and accepted with three children. So the needed results become nine new children, with the unique prefix dtc_bc_lc_sl_. Three accepted declarations are reused with identical frozen types: cmc_imRep_locality_restrict_sub, cmcs_cd_defect_identity and cmcs_lipschitz_smoothing. All 12 types pass validate_lean_statement and elaborate in the comparator's contract-mode challenge modules. A Lean assembly derives the exact frozen type of dtc_bc_lc_slice from slice_family, slice_identity, im_calculus and dtc_mass_eq_measure, with axioms propext, Classical.choice and Quot.sound only.
