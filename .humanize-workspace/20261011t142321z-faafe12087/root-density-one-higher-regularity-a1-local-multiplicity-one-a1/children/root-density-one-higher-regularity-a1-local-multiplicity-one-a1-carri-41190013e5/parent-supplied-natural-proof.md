# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.local_multiplicity_one-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.local_multiplicity_one-a1.carrier_support_null-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 of the parent-supplied proof ((a) H^n((M cap B1) minus Sigma) = 0 via mu(complement of spt mu) = 0 and (F2); (b) H^n((Sigma cap B1) minus M) = 0 because density 0 a.e. there contradicts the lower bound Theta >= 1), for a general measurable O contained in U.
1. (M cap O) symmetric-difference (Sigma cap O) = ((M cap O) minus Sigma) union ((Sigma cap O) minus M) (definition of symmDiff; points of M cap O outside Sigma cap O are outside Sigma, and points of Sigma cap O outside M cap O are outside M). By subadditivity it suffices to show that both sets are H^n-null.
2. (M cap O) minus Sigma. If x in M cap O and x not in Sigma = U cap spt mu, then x not in spt mu, because x in O, which is contained in U. Hence (M cap O) minus Sigma is contained in (spt mu)^c and mu((M cap O) minus Sigma) <= mu((spt mu)^c) = 0 (Measure.measure_compl_support). Since (M cap O) minus Sigma is contained in M, the sibling lemma dohr_lmo_hausdorff_null_of_weight_null gives H^n((M cap O) minus Sigma) = 0.
3. (Sigma cap O) minus M. Let nu := H^n restricted to Sigma cap O. Since O is contained in U, Sigma cap O = spt mu cap O, which is measurable (closed set intersected with a measurable set), so nu-a.e. y lies in Sigma cap O (ae_restrict_mem). For nu-a.e. y we therefore have y in Sigma cap O and, by (b), [y not in M implies V.HasDensity y 0]. Suppose such a y is not in M. Then V.HasDensity y 0, and by (c) V.HasDensity y Theta for some Theta >= 1. Limits in [0, inf] along the nontrivial filter nhdsWithin 0 (Ioi 0) are unique (tendsto_nhds_unique), so ofReal(0) = ofReal(Theta); but ofReal(Theta) >= ofReal(1) = 1 > 0 = ofReal(0), a contradiction. Hence nu-a.e. y lies in M, i.e. nu(M^c) = 0. Finally H^n((Sigma cap O) minus M) = H^n(M^c cap (Sigma cap O)) <= nu(M^c) = 0 (Measure.le_restrict_apply).
4. By steps 1-3, H^n((M cap O) symmetric-difference (Sigma cap O)) <= 0 + 0 = 0.

## Key steps

1. split the symmetric difference into (M cap O) minus Sigma and (Sigma cap O) minus M
2. (M cap O) minus Sigma lies outside spt mu, so it is mu-null and, being inside M, H^n-null by the sibling lemma
3. nu-a.e. point of (Sigma cap O) minus M would have density 0 and density >= 1: impossible by uniqueness of limits
4. hence H^n((Sigma cap O) minus M) <= nu(M^c) = 0

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean; diff <snapshot>/project/GMT/Ch05/Submission.lean GMT/Ch05/Submission.lean; rg -c sorry <snapshot>/project/GMT/Ch05/Submission.lean`
- `rg -l 'dohr_lmo|lmo_' <snapshot>/project .lake/packages/simongmt/Poincare GMT; grep -n 'dohr_lmo|lmo_' .humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `python3 -I extraction of lean_name/lean_statement/depends_on from dag.json for dohr_c1_graph_density_one, dohr_graph_tangent_planes, dohr_local_monotonicity, dohr_allard_graph_at_density_one and the cousins hausdorff_carrier_symmDiff_support_null, aal_tangent_structure, one_le_density_on_support_of_locallyLp, ae_weightedApproximateTangent_density_eq_mult, rsod_hasDensity_of_approxTangent`
- `rg -n 'theorem ae_tendsto_rnDeriv \(' <snapshot>/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `rg -n 'theorem rnDeriv_withDensity₀' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean`
- `rg -n 'lemma measure_compl_support :|lemma mem_support_iff_forall' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `rg -n 'theorem exists_mem_of_measure_ne_zero_of_ae|theorem le_restrict_apply' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `rg -n 'theorem Isometry.euclideanHausdorffMeasure_image|theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume' <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n 'theorem hausdorffMeasure_image_le \(h : LipschitzOnWith' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'lipschitzOnWith_of_nnnorm_fderiv_le' <snapshot>/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `rg -n 'finrank_range_of_inj|finrank_map_eq' <snapshot>/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `rg -n 'theorem lintegral_indicator₀|theorem lintegral_eq_zero_iff' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean; rg -n 'aemeasurable_indicator_iff₀' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/AEMeasurable.lean`
- `rg -n 'instHasBesicovitchCovering' <snapshot>/mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean; rg -n 'theorem continuousAt_rpow_const ' <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Continuity.lean; rg -n 'theorem withDensity_absolutelyContinuous ' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `rg -n 'ae_tendsto_rnDeriv|rnDeriv_withDensity|ae_tendsto_measure_inter_div' .lake/packages/simongmt/Poincare; rg -n 'upperSemicontinuous' .lake/packages/simongmt/Poincare`
- `sed -n 500,600p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py (child_modules / contract_scope: child comparator scope)`
- `lake env lean -o /tmp/lmo-check-7f3a/build/GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean`
- `lake env bash -c 'LEAN_PATH=$LEAN_PATH:/tmp/lmo-check-7f3a/build lean /tmp/lmo-check-7f3a/src/T0.lean' (lemma signatures; HasBesicovitchCovering/SecondCountableTopology/BorelSpace instances on Amb n ℓ)`
- `lake env bash -c 'LEAN_PATH=$LEAN_PATH:/tmp/lmo-check-7f3a/build lean /tmp/lmo-check-7f3a/src/Stmts.lean' (9 child types + 3 frozen sibling types)`
- `lake env bash -c 'LEAN_PATH=$LEAN_PATH:/tmp/lmo-check-7f3a/build lean /tmp/lmo-check-7f3a/src/Assembly.lean' (parent assembly; #print axioms GMT.Ch05.parent_assembly)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/AEMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-local-multiplicity-one-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/Density.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/MeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/lmo-check-7f3a/src/T0.lean`
- `/tmp/lmo-check-7f3a/src/Stmts.lean`
- `/tmp/lmo-check-7f3a/src/Assembly.lean`

Pinned snapshot (manifest.json): project ea5607598f3133b40a13241f2e51517a8c6423cd, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d.

The snapshot Contract.lean is byte-identical to the workspace contract. The snapshot Submission.lean equals the contract, with only main_theorem sorry, so it holds no prior proofs to reuse. 'dohr_lmo' matches nothing in the snapshot, simongmt, GMT/ or dag.json, so all nine proposed names are free.

Mathlib support for the child proofs, all available after import GMT.Ch05.Submission (checked in T0.lean):
- Besicovitch.ae_tendsto_rnDeriv (Besicovitch.lean:1078); the instHasBesicovitchCovering instance for finite-dimensional spaces (BesicovitchVectorSpace.lean:499) applies to Amb n ℓ.
- Measure.rnDeriv_withDensity₀ (Lebesgue.lean:584); withDensity_absolutelyContinuous (WithDensity.lean:146).
- measure_compl_support and mem_support_iff_forall (Support.lean:202, 75).
- exists_mem_of_measure_ne_zero_of_ae and le_restrict_apply (Restrict.lean:426, 171).
- Isometry.euclideanHausdorffMeasure_image and EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Volume/Measure.lean:131, 187).
- LipschitzOnWith.hausdorffMeasure_image_le (Hausdorff.lean:733); Convex.lipschitzOnWith_of_nnnorm_fderiv_le (MeanValue.lean:507).
- LinearMap.finrank_range_of_inj and LinearEquiv.finrank_map_eq (Finrank.lean:127, 120).
- lintegral_indicator₀ and lintegral_eq_zero_iff' (Lebesgue/Basic.lean:518, 322); aemeasurable_indicator_iff₀ (AEMeasurable.lean:323); Real.continuousAt_rpow_const (Pow/Continuity.lean:220).

simongmt has Besicovitch-density and upper-semicontinuity arguments (Chapter01/Densities.lean:493; Chapter04/Density.lean:415-450; Chapter04/MeanCurvature.lean:550-600). They are stated for its own Chapter04 varifold structures, so they serve only as proof templates, not reusable lemmas.

The frozen sibling types were read from dag.json. Cousin nodes with related topics (hausdorff_carrier_symmDiff_support_null, aal_tangent_structure, one_le_density_on_support_of_locallyLp) are global statements with different hypotheses in other branches, so none is duplicated.

verifier/gmt-compare.py elaborates child types after import GMT.Ch05.Submission in the contract scope at main_theorem (opens plus namespace GMT.Ch05). Stmts.lean reproduces that scope, and all nine child types and the three sibling types elaborate there.

Assembly.lean proves the exact frozen type of dohr_local_multiplicity_one from the nine children and the three siblings as sorry stubs, with no other sorry. Its axioms are propext, sorryAx (stubs only), Classical.choice and Quot.sound. The one checking fix was ContDiffOn.differentiableOn taking one_ne_zero, which is recorded in the rationale.
