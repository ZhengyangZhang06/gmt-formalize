# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.local_multiplicity_one-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.local_multiplicity_one-a1.density_usc-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the core of step 5 of the parent-supplied proof ('Theta(z) <= c < 1 for every z with |z - y| <= eps t', obtained from monotonicity at z, the inclusion B_r(z) in B_{r+d}(y) and the density at y) and of step 7 ('Theta < 2 near xi'), written for an arbitrary level c > Theta_y; the limit r -> t- of the parent is replaced by the fixed radius r = t/2.
1. omega := omega_n = pi^(n/2)/Gamma(n/2 + 1) > 0, because pi > 0 (so pi^(n/2) > 0) and Gamma > 0 on (0, inf).
2. Put b := Theta_y + (c - Theta_y)/3 and a' := Theta_y + 2(c - Theta_y)/3, so 0 <= Theta_y < b < a' < c and b > 0. Since (1 + 2 eps)^n -> 1 as eps -> 0, choose eps in (0, 1/2] with (1 + 2 eps)^n b <= a', and put a := (1 + 2 eps)^n b; then a <= a' < c.
3. Mass bound at y. By V.HasDensity y Theta_y, mu(B_s(y)) / ofReal(omega s^n) -> ofReal(Theta_y) in [0, inf] as s -> 0+, and ofReal(Theta_y) < ofReal(b) because Theta_y < b and b > 0. Hence there is sigma1 > 0 such that for every s in (0, sigma1), mu(B_s(y)) / ofReal(omega s^n) < ofReal(b); since 0 < ofReal(omega s^n) < inf, this gives (ENNReal.div_lt_iff) V.weight(B_s(y)) < ofReal(b) * ofReal(omega s^n) = ofReal(b omega s^n).
4. Choice of t. As t -> 0+, exp(Lambda(t)) a + Lambda(t)/omega -> exp(0) a + 0 = a < c (continuity of exp and Lambda(t) -> 0). The three conditions 0 < t <= t1, t < sigma1, exp(Lambda(t)) a + Lambda(t)/omega < c each hold eventually in the nontrivial filter nhdsWithin 0 (Ioi 0), so some t satisfies all of them. Put d := eps t > 0.
5. Let z in B_d(y). Since d = eps t <= t/2 < t, z in B_t(y) and t in (0, t1], so (hmon) gives a real Theta >= 0 with V.HasDensity z Theta and omega Theta <= exp(Lambda(t)) r^(-n) mu(B_r(z)) + Lambda(t) for r in (0, t). Use r := t/2.
6. Let s := t/2 + d = (t/2)(1 + 2 eps). Then 0 < s <= t/2 + t/2 = t < sigma1, and B_{t/2}(z) is contained in B_s(y) (|w - y| <= |w - z| + |z - y| <= t/2 + d). By monotonicity and step 3, V.weight(B_{t/2}(z)) <= V.weight(B_s(y)) <= ofReal(b omega s^n), so the real number mu(B_{t/2}(z)) satisfies mu(B_{t/2}(z)) <= b omega s^n = b omega (t/2)^n (1 + 2 eps)^n = omega a (t/2)^n (ENNReal.toReal_le_of_le_ofReal). Therefore (t/2)^(-n) mu(B_{t/2}(z)) <= omega a.
7. Since exp(Lambda(t)) > 0, steps 5-6 give omega Theta <= exp(Lambda(t)) omega a + Lambda(t); dividing by omega > 0, Theta <= exp(Lambda(t)) a + Lambda(t)/omega < c by step 4. Thus z has the real Theta < c with V.HasDensity z Theta. As z in B_d(y) was arbitrary, d works.

## Key steps

1. choose b in (Theta_y, c) and eps with a := (1 + 2 eps)^n b < c
2. density at y gives mu(B_s(y)) <= b omega s^n for s < sigma1
3. choose t <= t1, t < sigma1 with exp(Lambda(t)) a + Lambda(t)/omega < c, and d := eps t
4. for z in B_d(y): monotonicity bound at r = t/2 and B_{t/2}(z) in B_{t/2 + d}(y) give Theta(z) <= exp(Lambda(t)) a + Lambda(t)/omega < c

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
