# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_regularity-a1.tangent_ae-a1`
- Child DAG node: `root.density_one_regularity-a1.tangent_ae-a1.lusin_pieces-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 3 ('Lusin decomposition (Remark 1.8(1)), localized to U') and its measurability convention. H^n = muHE[n]; mu := V.weight = theta H^n restricted to M (density ENNReal.ofReal theta).
1. (Compact exhaustion.) U is an open subset of R^(n+l), hence sigma-compact: there are compact sets K_m (m in N) contained in U with U_m K_m = U (if U = R^(n+l) take K_m := B_m(0); otherwise K_m := {y in B_m(0) : dist(y, R^(n+l) \ U) >= 1/(m+1)}, which is closed, bounded and contained in U).
2. (Borel versions of M and theta.) Since theta is a.e.-measurable for H^n restricted to M, there is a Borel function g : R^(n+l) -> R with theta = g at H^n-a.e. point of M, i.e. H^n(M cap {theta != g}) = 0; choose a Borel H^n-null set Z' containing M cap {theta != g} (Mathlib exists_measurable_superset_of_null). Since M is H^n-null-measurable, choose a Borel set M' contained in M with H^n(M \ M') = 0 (Mathlib NullMeasurableSet.exists_measurable_subset_ae_eq). For m in N put A_m := (M' cap K_m) \ Z': a Borel subset of M on which theta = g.
3. (Finite measures.) nu_m := mu restricted to K_m is a finite Borel measure: nu_m(R^(n+l)) = int_{M cap K_m} theta dH^n < infinity because theta is integrable on M cap K_m (contract field integrableOn_mult, K_m compact and contained in U). A finite Borel measure on R^(n+l) is weakly regular (closed inner regular on Borel sets; Mathlib Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure).
4. (Lusin.) Fix m and i >= 1. By Lusin's theorem (Simon Ch. 1, 1.17; SimonGMT Chapter01.exists_isClosed_continuousOn_of_measurable) for nu_m, the Borel set A_m and the Borel function g, there is a closed set C_{m,i} contained in A_m with nu_m(A_m \ C_{m,i}) < 1/i and g restricted to C_{m,i} continuous. C_{m,i} is closed and contained in the compact set K_m, so it is compact; it is contained in A_m, hence in M; and theta = g on C_{m,i} (it avoids Z'), so theta restricted to C_{m,i} is continuous (ContinuousOn.congr).
5. (Null remainder on each K_m.) S_m := A_m \ U_i C_{m,i} is Borel and nu_m(S_m) <= nu_m(A_m \ C_{m,i}) < 1/i for all i, so 0 = nu_m(S_m) = mu(S_m) = int_{S_m} theta dH^n (S_m is contained in K_m and in M). As theta > 0 on S_m (S_m contained in M), this forces H^n(S_m) = 0: otherwise, with S_m^q := S_m cap {g > 1/q} (Borel, as theta = g on S_m), countable additivity gives some q with H^n(S_m^q) > 0, and then int_{S_m} theta dH^n >= H^n(S_m^q)/q > 0, a contradiction.
6. (Conclusion.) M is contained in U = U_m K_m, and M cap K_m is contained in (M \ M') union Z' union A_m, which is contained in (M \ M') union Z' union S_m union U_i C_{m,i}. Hence M \ U_{m,i} C_{m,i} is contained in (M \ M') union Z' union U_m S_m, a countable union of H^n-null sets, so it is H^n-null. Finally enumerate the pairs (m, i) by k in N (k -> Nat.unpair k, using C_{m,0} := C_{m,1} for i = 0) to obtain the family (C_k) of the statement.

## Key steps

1. Exhaust the open set U by compact sets K_m
2. Replace M and theta by Borel versions M' and g off an H^n-null set
3. mu restricted to K_m is a finite, weakly regular Borel measure (local integrability of theta)
4. Lusin: closed, hence compact, C_{m,i} contained in M with theta continuous on C_{m,i} and small leftover mass
5. The leftover S_m is mu-null; since theta > 0 on M it is H^n-null
6. Collect the countably many pieces C_{m,i}; the uncovered part of M is H^n-null

## Reference use

### local-project

Queries:
- `grep -n '^def \|^theorem \|^noncomputable def ' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean; sed -n 1,365p (CountablyRectifiable, blowUpMap, HasApproximateTangentSpaceAt, HasWeightedApproximateTangentSpaceAt, .unique)`
- `cat .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/{SubmanifoldCover,Differential,DisjointCover,CoordinateProjection}.lean`
- `grep -rn -i 'approximation theorem\|theorem_1_5\|C¹ approximation\|c1_approximation\|contDiff_approx' .lake/packages/simongmt/Poincare/SimonGMT`
- `grep -n '^theorem \|^def ' .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/*.lean; sed -n on Chapter02/{AreaCritical,AreaFormula,WeightedArea,Area,AreaLinearWeighted,Lipschitz,WhitneyExtension,WhitneyJet}.lean`
- `sed -n on .lake/packages/simongmt/Poincare/SimonGMT/Chapter01/{Lusin,DensityComparison,Densities,Hausdorff,Basic}.lean (simon_theorem_3_6, simonHausdorffOuterMeasureReal_eq_scaled_hausdorffMeasure, measure_toOuterMeasure_isBorelRegular)`
- `sed -n on .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/{TangentDensity,WeightedBlowUp,WeightedDensity,ClassicalTangent,LowerDensityTangents,MultiplicityBridge}.lean`
- `rg -n -i 'lusin' <snapshot>/mathlib/Mathlib`
- `rg -n 'aestronglyMeasurable_iUnion_iff|ae_restrict_iUnion_iff|ae_restrict_union_iff|ContinuousOn.aestronglyMeasurable|aestronglyMeasurable_zero_measure|restrict_eq_zero|ae_restrict_mem' <snapshot>/mathlib/Mathlib/MeasureTheory`
- `rg -n 'WeaklyRegular.of_pseudoMetrizableSpace|exists_isClosed_sdiff_lt|exists_isClosed_diff_lt' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `rg -n 'measurableSet_of_differentiableAt|measurable_fderiv|isOpen_iUnion_countable|integral_withDensity_eq_integral_toReal_smul₀|tendsto_integral_filter_of_dominated_convergence|exists_measurable_superset_of_null|exists_measurable_subset_ae_eq|euclideanHausdorffMeasure_eq_volume|LipschitzWith.ae_differentiableAt|tendstoUniformlyOn_of_ae_tendsto' <snapshot>/mathlib/Mathlib`
- `sed -n 150,300p book/chapter-02.txt (Thm 1.5 and its printed proof, Whitney 1.6); sed -n 1,360p book/chapter-03.txt (1.1-1.9)`
- `cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean`
- `python3 scan of all lean_name fields in dag.json and nodes/**/*.json; grep -rl <six proposed names> .humanize GMT .lake/packages/simongmt`
- `lake env lean /tmp/tae-dec-k7q2/Check7.lean (contract lines 1-460 + six children as sorry + full parent assembly + #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaFormula.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLinearWeighted.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/WeightedBlowUp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1-tangent-ae-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1-tangent-ae-a1/parent-supplied-natural-proof.md`
- `/tmp/tae-dec-k7q2/Check7.lean`

Snapshot pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The snapshot Contract.lean is byte-identical to the workspace copy (cmp).

What SimonGMT already has:
- the definitions CountablyRectifiable, blowUpMap, HasApproximateTangentSpaceAt and HasWeightedApproximateTangentSpaceAt, with uniqueness;
- Whitney C^1 extension (exists_contDiff_one_extension_of_whitney);
- the critical-image theorem (area_image_criticalSet_eq_zero);
- Bochner and linear area formulas (integral_area_formula_of_injective_derivative, measurePreserving_linearMap_normDet_smul);
- the Lipschitz image bound;
- Lusin for weakly regular finite measures;
- the Upper Density Theorem (simon_theorem_3_6) with the Hausdorff normalization bridge and measure_toOuterMeasure_isBorelRegular;
- generic blow-up scaling lemmas (hausdorff_blowUp_image, map_inverse_blowUp_carrier, planeMeasure_unit_closedBall, tangentDensityCutoff).

What no searched source has (grep/rg no-match):
- no a.e.-existence result for (weighted) approximate tangents (Simon 1.6/1.9);
- no Lemma 1.2 'only if' (SubmanifoldCover.lean says it 'remains a separate theorem');
- no C^1 approximation theorem (Simon 2.1.5);
- Mathlib has no Lusin continuity theorem (only Lusin separation / Lusin-Souslin).

Mathlib gluing and regularity lemmas used by the assembly and the child proofs exist: aestronglyMeasurable_iUnion_iff, ae_restrict_iUnion_iff, ContinuousOn.aestronglyMeasurable, MeasurableSet.exists_isClosed_sdiff_lt, Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure, and others.

Lean check:
- All six child types elaborate in the contract scope.
- The parent assembly compiles to the exact frozen type, with axioms propext, Classical.choice, Quot.sound plus sorryAx from the six children only.

The six tae_ names have no match in .humanize, GMT or simongmt.
