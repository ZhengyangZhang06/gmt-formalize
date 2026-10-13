# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.extend_to_univ-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3(c) of the parent proof (extension of a current supported in the compact K ⊂ U to ℝ^P, same masses, compatible boundary, IM with the same IMRep), here built from the IMRep with (IR) instead of a cutoff formula. The sibling vanish_off_support (the accepted declaration dtc_vanish_off_support) says: Z(ω) = 0 whenever tsupport ω ∩ spt Z = ∅.
1. Fix an IMRep R = (M, θ, ξ) of X in U. U ∖ K is open (K is compact, hence closed). If ω ∈ 𝒟ⁿ(U) and tsupport ω ⊆ U ∖ K, then tsupport ω ∩ spt X ⊆ (U ∖ K) ∩ K = ∅, so X(ω) = 0 by vanish_off_support. Thus every value in the supremum defining M_{U∖K}(X) is ENNReal.ofReal(0) = 0, so M_{U∖K}(X) = 0, and by (ME) (U open, R represents X, U ∖ K open) R.measure(U ∖ K) = 0.
2. Since M ⊆ U, the Borel set M ∖ K is contained in U ∖ K, so ∫_{M∖K} θ dHⁿ = R.measure(M ∖ K) ≤ R.measure(U ∖ K) = 0. As θ ≥ 1 on M, Hⁿ(M ∖ K) ≤ ∫_{M∖K} θ dHⁿ = 0.
3. Apply (IR) to (U, R, E := K) (K is Borel): there is an IMRep R₁ in U with carrier M ∩ K, multiplicity θ and orientation ξ. Let R̂ be the same data (M ∩ K, θ, ξ) regarded as an IMRep in ℝ^P = univ. Every field of the structure IMRep univ n holds: M ∩ K is Borel and countably n-rectifiable, θ is measurable and positive on M ∩ K, ξ is (Hⁿ⌞(M ∩ K))-a.e. strongly measurable and for Hⁿ-a.e. x ∈ M ∩ K orients an approximate tangent space of M ∩ K at x (these fields do not involve the domain and are those of R₁); M ∩ K ⊆ univ; and for every compact K' ⊆ ℝ^P, ∫_{M∩K∩K'} θ dHⁿ ≤ ∫_{M∩K} θ dHⁿ < ∞ because K is a compact subset of U and R is locally integrable in U.
4. Apply (IR) to (univ, R̂, E := univ) (univ is open): there are Y ∈ 𝒟_n(ℝ^P) and an IMRep R̂' in ℝ^P with carrier (M ∩ K) ∩ univ = M ∩ K, multiplicity θ and orientation ξ that represents Y. Hence Y is IM and Y(ω) = ∫_{M∩K} θ⟨ω, ξ⟩ dHⁿ for every ω ∈ 𝒟ⁿ(ℝ^P).
5. (Restriction.) Let ω ∈ 𝒟ⁿ(U); as a form it belongs to 𝒟ⁿ(ℝ^P) (testFormOnInclusion). By step 4 and Hⁿ(M ∖ K) = 0 (step 2; the sets M ∩ K and M differ by an Hⁿ-null set, Mathlib setIntegral_congr_set), Y(ω) = ∫_{M∩K} θ⟨ω, ξ⟩ dHⁿ = ∫_M θ⟨ω, ξ⟩ dHⁿ = X(ω), the last equality because R represents X. So (Y.restrictDomain (subset_univ U))(ω) = Y(ω) = X(ω) for every ω, i.e. Y.restrictDomain (subset_univ U) = X (GeometricCurrentOn.ext).
6. (Support.) Let x ∈ ℝ^P ∖ K. As K is closed there is r > 0 with closedBall(x, r) ∩ K = ∅. V := ball(x, r) is open with compact closure (contained in closedBall(x, r)) in ℝ^P. If ω ∈ 𝒟ⁿ(ℝ^P) and tsupport ω ⊆ V, then ω = 0 on K ⊇ M ∩ K, so Y(ω) = 0 by step 4. Hence V lies in the zero region of Y and x ∉ spt Y. Therefore spt Y ⊆ K.
7. (Mass.) By (ME) in ℝ^P (univ is open and R̂' represents Y), M(Y) = M_{ℝ^P}(Y) = R̂'.measure(ℝ^P) = ∫_{M∩K} θ dHⁿ = R.measure(K) ≤ R.measure(U) = M_U(X) = M(X), the last two equalities by (ME) in U with W := U.
8. (Boundary mass.) By Mathlib IsCompact.exists_cthickening_subset_open choose δ > 0 with K_δ := cthickening(δ, K) ⊆ U; K_δ is compact. By Mathlib exists_contMDiffMap_one_nhds_of_subset_interior (closed set K, t := K_δ, K ⊆ thickening(δ, K) ⊆ interior K_δ) (with smoothness index ∞, converted to ContDiff ℝ ∞ by contMDiff_iff_contDiff) there is a smooth ζ : ℝ^P → [0, 1] that equals 1 on an open set V ⊇ K and vanishes outside K_δ; so tsupport ζ ⊆ K_δ is compact and contained in U. Let ω ∈ 𝒟^m(ℝ^P) be admissible for M_{ℝ^P}(∂Y), i.e. |ω(x)| ≤ 1 for all x. Then ζω is smooth with tsupport contained in K_δ, so ζω ∈ 𝒟^m(U), and |ζ(x)ω(x)| = ζ(x)|ω(x)| ≤ 1, so ζω is admissible for M_U(∂X). On the open set V, ζω = ω, so d(ζω) = dω on V (the exterior derivative at a point only depends on the form near that point), in particular on M ∩ K ⊆ K ⊆ V. Using step 4 for dω and d(ζω) (both in 𝒟ⁿ(ℝ^P)) and step 5 for d(ζω) ∈ 𝒟ⁿ(U):
 ∂Y(ω) = Y(dω) = ∫_{M∩K} θ⟨dω, ξ⟩ dHⁿ = ∫_{M∩K} θ⟨d(ζω), ξ⟩ dHⁿ = Y(d(ζω)) = X(d(ζω)) = ∂X(ζω).
 Hence ENNReal.ofReal(∂Y(ω)) = ENNReal.ofReal(∂X(ζω)) ≤ M_U(∂X). Taking the supremum over admissible ω gives M(∂Y) ≤ M(∂X). ∎

## Key steps

1. spt X ⊆ K gives M_{U∖K}(X) = 0 (vanish_off_support), so by (ME) the carrier of an IMRep of X is Hⁿ-null outside K.
2. Restrict the carrier to K with (IR), read the data as an IMRep in ℝ^P and take the current Y it represents (again (IR)).
3. Y restricts to X on 𝒟ⁿ(U), vanishes away from K, and M(Y) = R.measure(K) ≤ M(X) by (ME).
4. A smooth cutoff ζ = 1 near K gives ∂Y(ω) = ∂X(ζω), hence M(∂Y) ≤ M(∂X).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n "cmc_fc_|flat.?conver|deformation|slic" local-references/123e8435b4a2469b/project/GMT --glob '*.lean'`
- `rg -n -i "flat norm|flat convergence|deformation theorem|federer.?fleming" local-references/123e8435b4a2469b/mathlib/Mathlib --glob '*.lean' (no match)`
- `rg -n "theorem FiniteMeasure.limsup_measure_closed_le_of_tendsto|theorem Monotone.ae_differentiableAt|theorem MonotoneOn.intervalIntegral_deriv_mem_uIcc|theorem measurable_deriv |theorem tendsto_of_subseq_tendsto|theorem extraction_of_frequently_atTop |theorem exists_contMDiffMap_one_nhds_of_subset_interior|theorem lipschitz_infDist_pt|theorem _root_.IsCompact.exists_cthickening_subset_open|theorem integral_withDensity_eq_integral_smul |theorem lintegral_liminf_le " local-references/123e8435b4a2469b/mathlib/Mathlib --glob '*.lean'`
- `rg -n "theorem HasDerivAt.tendsto_slope_zero_left|theorem ENNReal.tsum_geometric|theorem Finite.exists_infinite_fiber|theorem countable_meas_level_set_pos|theorem ENNReal.ofReal_tsum_of_nonneg|theorem withDensity_absolutelyContinuous|theorem tendsto_measure_iInter_atTop|theorem Summable.of_norm_bounded " local-references/123e8435b4a2469b/mathlib/Mathlib --glob '*.lean'`
- `grep -n '^def \|^theorem \|^structure ' in lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,CurrentLocalEquality,Forms}.lean; grep -n 'theorem simon_theorem_4_16_compact_metrizable\|theorem finiteMeasure_tendsto_subseq_of_compact_metrizable' Chapter01/CompactMetrizableCompactness.lean; grep -n 'countablyRectifiable_of_measure_zero' Chapter03/Rectifiable.lean`
- `python3 scan of dag.json: siblings of root.compactness_of_minimizing_currents-a1 and their frozen types; cross-parent dependency edges (only accepted nodes); accepted reusable declarations (dtc_vanish_off_support, dtc_isIntegerMultiplicity_sub, dtc_extend_by_zero, dtc_restrictDomain_isIntegerMultiplicity, dor_imrep_massOn_eq_measure_and_support, rsd_cmr_imrep_restrict, dor_ims_unitOrientation_dual); collisions of the seven cmc_fc_* names (none)`
- `sed -n 1790,1960p, 2000,2200p, 3150,3260p, 5071,5200p, 6480,6620p /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py (_solve_children, _existing_lean_name_problem, _overlay_accepted_children, _node_worktree, _leaf_author_task)`
- `sed -n 2004,2140p book/chapter-06.txt (Simon Ch. 6, 7.1–7.2)`
- `lake env lean /tmp/fcdec/Types.lean (8 child types + 5 conjunct projections); lake env lean /tmp/fcdec/Assembly.lean (#print axioms fc_assembly); lake env lean /tmp/fcdec/Inst.lean (pp.explicit Sub instance); lake env lean /tmp/fcdec/Avail.lean … /tmp/fcdec/Avail5.lean (#check probes of the import closure of GMT.Ch07.Submission)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Portmanteau.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/CountablyGenerated.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1/decomposition-v5.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/CompactMetrizableCompactness.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/fcdec/Types.lean`
- `/tmp/fcdec/Assembly_checked.lean`
- `/tmp/fcdec/Inst.lean`
- `/tmp/fcdec/Avail.lean`
- `/tmp/fcdec/Avail2.lean`
- `/tmp/fcdec/Avail3.lean`
- `/tmp/fcdec/Avail4.lean`
- `/tmp/fcdec/Avail5.lean`

The snapshot (project b4d606db, mathlib 25730c7c) Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. The snapshot has no cmc_fc_ declaration. Neither the snapshot project nor Mathlib proves slicing, deformation, closure or flat convergence; the Ch06 contract only states slices as its own frozen sorry. These therefore remain the parent's prerequisite theorems and reach the children as exact antecedents. The pinned Mathlib supplies the elementary tools the children cite: isCompact_univ_pi, IsCompact.tendsto_subseq, tendsto_pi_nhds, Monotone.countable_not_continuousAt, lintegral_liminf_le, lintegral_lintegral_swap, measurable_measure_prodMk_left, Filter.Tendsto.liminf_le_liminf_comp, exists_contMDiffMap_one_nhds_of_subset_interior, IsCompact.exists_cthickening_subset_open, lipschitz_infDist_pt, integral_withDensity_eq_integral_smul, withDensity_absolutelyContinuous, Finite.exists_infinite_fiber, ENNReal.tsum_geometric and HasSum.tendsto_sum_nat. #check confirms all of them after import GMT.Ch07.Submission. FiniteMeasure.limsup_measure_closed_le_of_tendsto, MonotoneOn.intervalIntegral_deriv_mem_uIcc and SimonGMT finiteMeasure_tendsto_subseq_of_compact_metrizable exist in the pinned sources but lie outside that import closure, so good_slice avoids them. Among accepted DAG declarations, dtc_vanish_off_support is reused with its identical type. The eight child types elaborate, and the conditional assembly of the exact parent type compiles with only propext, Classical.choice and Quot.sound.
