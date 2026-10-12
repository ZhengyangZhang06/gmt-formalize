# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.local_multiplicity_one-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.local_multiplicity_one-a1.density_eq_mult_ae-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3-4 of the parent-supplied proof and the differentiation part of step 6(b) (Besicovitch differentiation of lambda := mu restricted to O with respect to nu := H^n restricted to Sigma cap O, combined with the unit density of nu).
1. Measurability and finiteness. spt mu is closed, O is open and O is contained in B_{r0}(y0), contained in U; hence Sigma cap O = spt mu cap O is a Borel set. nu := H^n restricted to Sigma cap O is a finite Borel measure (total mass H^n(Sigma cap O) < inf). lambda := mu restricted to O is finite: mu(O) <= mu(B_{r0}(y0)) = lintegral over B_{r0}(y0) of ofReal(theta) d(H^n restricted to M) = lintegral over M cap B_{r0}(y0) of ofReal(theta) dH^n <= lintegral over M cap B_{r0}(y0) of |theta| dH^n < inf, because B_{r0}(y0) is a compact subset of U and theta is H^n-integrable on M cap K for every compact K contained in U (structure field integrableOn_mult). Finite measures are locally finite and sigma-finite.
2. mu((spt mu)^c) = 0 (Measure.measure_compl_support), so mu(S cap O) = mu(S cap O cap spt mu) for every set S, and S cap O cap spt mu = S cap (Sigma cap O).
3. lambda = nu.withDensity f, where f(x) := ofReal(M.indicator theta x) = 1_M(x) ofReal(theta(x)). f is AEMeasurable for H^n (M is H^n-null-measurable and theta is AEMeasurable for H^n restricted to M, so M.indicator theta is AEMeasurable for H^n by aemeasurable_indicator_iff_0), hence for nu. For a Borel set S: lambda(S) = mu(S cap O) = mu(S cap O cap spt mu) (step 2) = lintegral over S cap O cap spt mu of ofReal(theta) d(H^n restricted to M) (withDensity_apply) = lintegral over S cap O cap spt mu of 1_M ofReal(theta) dH^n (restriction to the null-measurable set M equals integration of the M-indicator, lintegral_indicator_0) = lintegral over S of f dnu = (nu.withDensity f)(S). Two measures agreeing on all Borel sets are equal.
4. Besicovitch. R^(n+l) is a finite-dimensional normed space: second countable, Borel, with the Besicovitch covering property. By Besicovitch.ae_tendsto_rnDeriv (lambda, nu locally finite), for nu-a.e. y, lambda(B_r(y)) / nu(B_r(y)) -> (lambda.rnDeriv nu)(y) as r -> 0+. By step 3 and Measure.rnDeriv_withDensity_0 (nu sigma-finite, f AEMeasurable), lambda.rnDeriv nu = f nu-a.e. Also nu-a.e. y lies in the Borel set Sigma cap O (ae_restrict_mem). Hence for nu-a.e. y: y in Sigma cap O and lambda(B_r(y)) / nu(B_r(y)) -> f(y).
5. Fix such a y and let delta := r0 - |y - y0| > 0. For 0 < r < delta, B_r(y) is contained in O, so nu(B_r(y)) = H^n(B_r(y) cap Sigma cap O) = H^n(Sigma cap B_r(y)) and lambda(B_r(y)) = mu(B_r(y) cap O) = mu(B_r(y)). By hypothesis q(r) := nu(B_r(y)) / ofReal(omega_n r^n) -> 1; hence q(r) > 1/2 for small r, so nu(B_r(y)) is nonzero, and nu(B_r(y)) <= nu(R^(n+l)) < inf. For such r, mu(B_r(y)) / ofReal(omega_n r^n) = [lambda(B_r(y)) / nu(B_r(y))] * q(r) (cancel the nonzero finite factor nu(B_r(y)) in [0, inf]). The limits are f(y) (finite) and 1, so by ENNReal.Tendsto.mul the product tends to f(y) * 1 = ofReal(M.indicator theta y). Thus V.HasDensity y (M.indicator theta y) for nu-a.e. y.
6. Conclusion (b): for nu-a.e. y with y not in M, M.indicator theta y = 0, so V.HasDensity y 0.
7. Conclusion (a): lambda = nu.withDensity f is absolutely continuous with respect to nu (withDensity_absolutelyContinuous), so the conclusion of step 5 holds lambda-a.e., i.e. for mu-a.e. y, y in O implies V.HasDensity y (M.indicator theta y) (ae_restrict_iff' for the Borel set O). Moreover mu(M^c) = 0, because mu is absolutely continuous with respect to H^n restricted to M, which is concentrated on the null-measurable set M (ae_restrict_mem_0). On M, M.indicator theta = theta. Hence for mu-a.e. y, y in O implies V.HasDensity y theta(y).

## Key steps

1. nu := H^n on Sigma cap O and lambda := mu on O are finite Borel measures
2. lambda = nu.withDensity (1_M theta), using mu(O minus spt mu) = 0
3. Besicovitch: lambda(B_r(y))/nu(B_r(y)) -> 1_M theta (y) for nu-a.e. y (rnDeriv of a withDensity)
4. multiply by nu(B_r(y))/(omega_n r^n) -> 1 to get Theta(y) = 1_M theta (y) nu-a.e.
5. transfer to mu-a.e. on O via lambda << nu and mu(M^c) = 0

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
