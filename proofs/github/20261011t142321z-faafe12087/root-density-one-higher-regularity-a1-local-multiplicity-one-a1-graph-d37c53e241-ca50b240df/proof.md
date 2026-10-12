# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.local_multiplicity_one-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.local_multiplicity_one-a1.graph_support_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1-2 of the parent-supplied proof (finite graph piece; density of nu at its points), generalized from Bo_{R/2}(xi) to every Bo_rho(xi) with rho < R and to every point of S cap Bo_R(xi), with the sibling C^1-graph density theorem entering only through hypothesis (C4).
0. Preliminaries. (i) graphPoint is linear in the pair: graphPoint (a + a') (b + b') = graphPoint a b + graphPoint a' b' and graphPoint (c a) (c b) = c graphPoint a b (coordinatewise identities of Fin.append); in particular graphPoint a b - graphPoint a' b' = graphPoint (a - a') (b - b'). (ii) Norm identity: ||graphPoint a b||^2 = sum over i < n+l of (Fin.append a b)_i^2 = sum_{i<n} a_i^2 + sum_{j<l} b_j^2 = ||a||^2 + ||b||^2 (split the sum over Fin (n+l) into the first n and the last l indices, Fin.sum_univ_add, Fin.append_left, Fin.append_right). Hence ||a|| <= ||graphPoint a b|| <= ||a|| + ||b||. (iii) Let T(z) := Q(z - xi). T is an isometric bijection of R^(n+l) (translation followed by the linear isometry equivalence Q), ||T z|| = ||z - xi||, ||T z - T z'|| = ||z - z'||, and T(X) = Q '' ((fun x => x - xi) '' X) for every X. Since T is an isometry, H^n(T(X)) = H^n(X) for every X (Mathlib Isometry.euclideanHausdorffMeasure_image). The hypothesis (graph) reads T(S) cap Bo_R(0) = Gamma cap Bo_R(0).
1. Proof of (a). Let rho < R. If rho <= 0 then Bo_rho(xi) is empty and H^n(empty) = 0 < inf. Assume 0 < rho < R and let K := B^n_rho(0), the closed ball of R^n.
1a. T(S cap Bo_rho(xi)) is contained in G(K): if z in S and ||z - xi|| < rho, then T z in T(S) and ||T z|| = ||z - xi|| < rho < R, so T z in T(S) cap Bo_R(0) = Gamma cap Bo_R(0); write T z = G(x) with x in Bo^n_R(0). By (ii), ||x|| <= ||G(x)|| = ||T z|| < rho, so x in K.
1b. G is Lipschitz on K. K is compact, convex and contained in the open ball Bo^n_R(0) because rho < R. Since u is C^1 on the open set Bo^n_R(0), u is differentiable at every point of it and x -> Du(x) is continuous there (ContDiffOn.continuousOn_fderiv_of_isOpen); hence ||Du|| is bounded on the compact set K by some C >= 0, and by the mean value inequality on the convex set K (Convex.lipschitzOnWith_of_nnnorm_fderiv_le), ||u(a) - u(b)|| <= C ||a - b|| for a, b in K. By (i) and (ii), ||G(a) - G(b)|| = ||graphPoint (a - b) (u a - u b)|| <= ||a - b|| + ||u(a) - u(b)|| <= (1 + C) ||a - b|| for a, b in K.
1c. muHE[n] = c_n muH[n] with the constant c_n = addHaarScalarFactor volume muH[n] (on EuclideanSpace R (Fin n)) independent of the ambient space (euclideanHausdorffMeasure_def). For a (1 + C)-Lipschitz map on K, muH[n](G(K)) <= (1 + C)^n muH[n](K) (LipschitzOnWith.hausdorffMeasure_image_le with d = n >= 0), hence H^n(G(K)) <= (1 + C)^n H^n(K). On R^n, H^n = muHE[n] equals Lebesgue measure (EuclideanSpace.euclideanHausdorffMeasure_eq_volume) and the closed ball K has finite Lebesgue measure, so H^n(G(K)) < inf.
1d. By (iii), 1a, monotonicity and 1c: H^n(S cap Bo_rho(xi)) = H^n(T(S cap Bo_rho(xi))) <= H^n(G(K)) < inf.
2. Proof of (b). Let y in S cap Bo_R(xi) and delta := R - ||y - xi|| > 0.
2a. T y in T(S) and ||T y|| = ||y - xi|| < R, so T y in T(S) cap Bo_R(0) = Gamma cap Bo_R(0) and T y = G(x) for some x in Bo^n_R(0).
2b. Claim: T(S cap B_r(y)) = Gamma cap B_r(G(x)) for 0 < r < delta. (Inclusion one) If z in S with ||z - y|| <= r, then ||T z - G(x)|| = ||T z - T y|| = ||z - y|| <= r and ||T z|| = ||z - xi|| <= ||z - y|| + ||y - xi|| <= r + ||y - xi|| < R; so T z in T(S) cap Bo_R(0) = Gamma cap Bo_R(0), hence T z in Gamma cap B_r(G(x)). (Inclusion two) If w in Gamma with ||w - G(x)|| <= r, then ||w|| <= ||G(x)|| + r = ||y - xi|| + r < R, so w in Gamma cap Bo_R(0) = T(S) cap Bo_R(0); write w = T z with z in S; then ||z - y|| = ||T z - T y|| = ||w - G(x)|| <= r, so z in S cap B_r(y) and w in T(S cap B_r(y)).
2c. By (iii) and 2b, H^n(S cap B_r(y)) = H^n(Gamma cap B_r(G(x))) for every r in (0, delta). The interval (0, delta) belongs to the filter nhdsWithin 0 (Ioi 0), so the functions r -> H^n(S cap B_r(y)) / ofReal(omega_n r^n) and r -> H^n(Gamma cap B_r(G(x))) / ofReal(omega_n r^n) are eventually equal along r -> 0+ (Tendsto.congr'). By (C4) at x in Bo^n_R(0) the second tends to 1; hence so does the first. This proves (b).

## Key steps

1. isometry T(z) = Q(z - xi) preserves H^n; graphPoint is linear with ||graphPoint a b||^2 = ||a||^2 + ||b||^2
2. T(S cap Bo_rho(xi)) lies in G(closed ball of radius rho), on which G is (1 + sup|Du|)-Lipschitz, so H^n is finite (Lipschitz image bound, H^n = Lebesgue on R^n)
3. for small r, T(S cap B_r(y)) = Gamma cap B_r(G(x)) with T y = G(x)
4. transfer the C^1-graph density limit (C4) at x by eventual equality

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
