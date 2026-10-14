# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.minimality_localizes-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 8 of the parent proof, which supplies the details behind Simon's remark after (8) (chapter-07.txt lines 226–229: “In view of the arbitrariness of K, X this will evidently establish the fact that T is minimizing in U”).
1. Let R_S, R_T be IM representations of S and T and μ_S := R_S.measure, μ_T := R_T.measure. By the sibling lemma mass_equals_rep_measure, M_G(S) = μ_S(G) and M_G(T) = μ_T(G) for every open G ⊆ ℝ^P. Both measures vanish outside U and are finite on compact subsets of U (local integrability of the multiplicities).
2. O := U ∖ K is open (K is compact, hence closed). Let ω ∈ 𝒟ⁿ(U) with tsupport ω ⊆ O. Then tsupport ω ∩ spt(S − T) ⊆ O ∩ K = ∅, so (S − T)(ω) = 0 by the sibling lemma vanish_off_support; that is, S(ω) = T(ω).
3. Hence, for every open G ⊆ O, the admissible forms for M_G(S) and for M_G(T) are the same test forms (in 𝒟ⁿ(U), supported in G, of norm ≤ 1) and give the same values, so M_G(S) = M_G(T), i.e. μ_S(G) = μ_T(G) by step 1.
4. Let O_i := {x ∈ O : |x| < i, dist(x, ℝ^P ∖ O) > 1/i} (O_i := {|x| < i} if O = ℝ^P); these are open, increase to O, and have compact closures contained in O ⊆ U, so μ_S(O_i), μ_T(O_i) < ∞. For each i, the finite Borel measures μ_S⌞O_i and μ_T⌞O_i agree on every open set G ⊆ ℝ^P (G ∩ O_i is an open subset of O; step 3), in particular on ℝ^P; the open sets form a π-system generating the Borel σ-algebra, so μ_S⌞O_i = μ_T⌞O_i (uniqueness of finite measures, e.g. Mathlib ext_of_generate_finite). For a Borel set A ⊆ O, continuity from below along O_i ↑ O gives μ_S(A) = lim_i μ_S(A ∩ O_i) = lim_i μ_T(A ∩ O_i) = μ_T(A).
5. W' ∖ W is a Borel set contained in O (W' ⊆ closure(W') ⊆ U and K ⊆ W), so μ_S(W' ∖ W) = μ_T(W' ∖ W).
6. Since W ⊆ W', μ_T(W') = μ_T(W) + μ_T(W' ∖ W) ≤ μ_S(W) + μ_S(W' ∖ W) = μ_S(W'), using μ_T(W) = M_W(T) ≤ M_W(S) = μ_S(W). By step 1, M_{W'}(T) = μ_T(W') ≤ μ_S(W') = M_{W'}(S). ∎

## Key steps

1. By mass_equals_rep_measure, masses on open sets are the representation measures μ_S, μ_T.
2. By vanish_off_support, S and T agree on test forms supported in O = U ∖ K, so μ_S = μ_T on open subsets of O and hence (finite-measure uniqueness along an exhaustion of O) on all Borel subsets of O.
3. μ_T(W') = μ_T(W) + μ_T(W' ∖ W) ≤ μ_S(W) + μ_S(W' ∖ W) = μ_S(W').

## Reference use

### local-project

Queries:
- `cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; cmp GMT/Ch07/Contract.lean .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `rg -n 'cmc_|dtc_vanish_off_support' local-references/123e8435b4a2469b/project (no match); rg -c sorry local-references/123e8435b4a2469b/project/GMT -g '*.lean'`
- `rg -n -i 'federer.?fleming|deformation theorem|flat norm' local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean' (no match); rg -n 'theorem eLpNorm_le_eLpNorm_fderiv_one|theorem tendsto_measure_thickening_of_isClosed' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n -i 'federer|deformation|flat (norm|metric|convergence)|slice|slicing|closure theorem|boundary rectifiab' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06`
- `python3 scan of dag.json: lean_name, lean_statement, status and children of all 451 nodes; collisions of the twelve proposed names; accepted nodes with matching types (dtc_vanish_off_support, dor_ims_massOn_le_measure, dor_ims_measure_le_massOn, regcomp_approx_tangent_locality, regcomp_covector_eval_orthonormal_le, rsdic_unitOrientation_eq_or_eq_neg, dtc_isIntegerMultiplicity_sub); cross-branch reuse edges`
- `grep compactness_of_minimizing cluster-state/logs/gmt-ch07/*.log; comparison of swarm-configs/3cda86c657b24789a5e2370499838a03.json and e19a0116cbcc4eccb5496520b27c492f.json (max_nodes 200 vs 1000); node-directory timestamps at the v3 and v4 audit times`
- `sed -n 1300,1700p and 1801,2000p /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py; grep -n 'def _existing_lean_name_problem' -A 40 runtime.py; grep -n 'def ensure' -A 35 store.py`
- `grep for declarations simon_theorem_4_14_caratheodory, simon_theorem_4_14_positive_envelope, vectorFunctionalEnvelopeMeasure_isRadon, radonCaratheodoryMeasure_apply, integral_radonCaratheodoryMeasure, IsLocallyBoundedCcFunctional, simon_theorem_4_16_compact_metrizable, simon_theorem_3_6, simon_remark_3_7_hausdorff, simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure, simonHausdorffMeasureReal_toOuterMeasure, simon_theorem_3_3, simon_theorem_3_26_i, exists_isClosed_continuousOn_of_measurable, area_image_criticalSet_eq_zero, injective_area_formula_lipschitzOn, weighted_area_formula_lipschitzOn_fiberSum, exteriorDerivativeOn_pullbackFormWithin, countablyRectifiable_of_measure_zero, HasApproximateTangentSpaceAt.unique, WeaklyConvergesOn.boundary, WeaklyConvergesOn.massOn_le_liminf, affinePushforward in lake-packages-25730c7c/simongmt/Poincare`
- `grep for declarations Monotone.ae_differentiableAt, measurable_deriv, MonotoneOn.intervalIntegrable_deriv, MonotoneOn.intervalIntegral_deriv_mem_uIcc, LipschitzWith.ae_differentiableAt, LipschitzOnWith.hausdorffMeasure_image_le, exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, LinearMap.exists_antilipschitzWith, MeasurableSet.image_of_continuousOn_injOn, LipschitzOnWith.extend_real, LipschitzOnWith.extend_pi, Besicovitch.exists_disjoint_closedBall_covering_ae, VitaliFamily.ae_tendsto_average_norm_sub, isMulLeftInvariant_eq_smul, tendstoUniformlyOn_of_ae_tendsto, LipschitzWith.integral_lineDeriv_mul_eq, eLpNorm_le_eLpNorm_fderiv_one, euclideanHausdorffMeasure_zero, hausdorffMeasure_smul₀, tendsto_measure_thickening_of_isClosed, countable_meas_level_set_pos, Integrable.integral_eq_integral_meas_lt, SmoothPartitionOfUnity.exists_isSubordinate, exists_contDiff_tsupport_subset, ContDiffBump.normed, AlternatingMap.map_linearDependent, Vitali.exists_disjoint_subfamily_covering_enlargement, RealRMK.rieszMeasure, ext_of_generate_finite, ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable, hausdorffMeasure_zero_singleton, Besicovitch.tendsto_filterAt in lake-packages-25730c7c/mathlib/Mathlib`
- `lake env lean /tmp/cmc-a5/lean/TypesFinal.lean; lake env lean /tmp/cmc-a5/lean/AssemblyFinal.lean; lake env lean /tmp/cmc-a5/lean/Inst.lean; lake env lean /tmp/cmc-a5/lean/Names.lean; lake env lean /tmp/cmc-a5/lean/Names2.lean`
- `git -C lake-packages-25730c7c/simongmt rev-parse HEAD; git -C lake-packages-25730c7c/mathlib rev-parse HEAD`
- `sed -n 176,260p book/chapter-07.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1/decomposition-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1/decomposition-audit-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1/decomposition-audit-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1/decomposition-review-receipt-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/3cda86c657b24789a5e2370499838a03.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/e19a0116cbcc4eccb5496520b27c492f.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/cluster-state/logs/gmt-ch07/3cda86c657b24789a5e2370499838a03.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/cluster-state/logs/gmt-ch07/e19a0116cbcc4eccb5496520b27c492f.log`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/GeometricPointProduct.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonPolarRepresentation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/VectorFunctionalEnvelope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonCaratheodoryIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/CompactMetrizableCompactness.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/HausdorffDensityBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Measure/Haar/Unique.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/cmc-a5/final.json`
- `/tmp/cmc-a5/scripts/build_final.py`
- `/tmp/cmc-a5/scripts/gen_types_final.py`
- `/tmp/cmc-a5/scripts/gen_assembly.py`
- `/tmp/cmc-a5/scripts/body.lean`
- `/tmp/cmc-a5/lean/TypesFinal.lean`
- `/tmp/cmc-a5/lean/AssemblyFinal.lean`
- `/tmp/cmc-a5/lean/Inst.lean`
- `/tmp/cmc-a5/lean/Names.lean`
- `/tmp/cmc-a5/lean/Names2.lean`

The snapshot contract (manifest: project b4d606db, mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean, and each snapshot chapter contract has only its frozen final sorry; the pinned packages are SimonGMT 2b366308 and Mathlib 25730c7c. SimonGMT Chapter06 says Federer–Fleming compactness remains a separate obligation and contains only point slices of products. Neither SimonGMT nor the snapshot Mathlib has a closure, deformation, Lipschitz-slicing or flat-convergence theorem (rg: no match). These results, Riesz representation and absolute continuity of normal currents, and IM calculus therefore remain children with complete parent-written proofs. Reusable library facts: WeaklyConvergesOn.massOn_le_liminf and WeaklyConvergesOn.boundary, the Chapter01 Riesz, compactness, density and Lusin theorems, the Chapter02 area formulas and the Chapter03 rectifiability API. Every SimonGMT and Mathlib declaration cited by name in the child proofs exists in the pinned sources. The 451-node DAG contains no cmc_ name, and the snapshot project has no cmc_ or dtc_ name. dtc_vanish_off_support is a comparator-accepted node whose frozen type equals the vanish_off_support child type, so it is reused verbatim; accepted declarations covering parts of mass_equals_rep_measure and im_calculus are named in remarks. In the workspace build, all 12 exact child types elaborate after import GMT.Ch07.Submission. The conditional assembly of CompactnessOfMinimizingCurrents from the six used child types depends only on propext, Classical.choice and Quot.sound, and current subtraction uses the contract instance. The identical previously accepted split was dropped only by the runtime node bound (max_nodes = 200 with about 200 DAG nodes); the current configuration allows 1000 nodes. Book lines 176–260 confirm the two corrections used in local_comparison.
