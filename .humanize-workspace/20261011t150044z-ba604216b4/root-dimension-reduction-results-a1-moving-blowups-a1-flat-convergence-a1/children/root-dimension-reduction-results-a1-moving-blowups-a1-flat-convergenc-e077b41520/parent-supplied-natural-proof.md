# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.flat_convergence-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.flat_convergence-a1.extend_to_univ-a1`
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
8. (Boundary mass.) By Mathlib IsCompact.exists_cthickening_subset_open choose δ > 0 with K_δ := cthickening(δ, K) ⊆ U; K_δ is compact. By Mathlib exists_contMDiffMap_one_nhds_of_subset_interior (closed set K, t := K_δ, K ⊆ thickening(δ, K) ⊆ interior K_δ) (with smoothness index ∞, converted to ContDiff ℝ ∞ by contMDiff_iff_contDiff) there is a smooth ζ : ℝ^P → [0, 1] that equals 1 on an open set V ⊇ K and vanishes outside K_δ; so tsupport ζ ⊆ K_δ is compact and contained in U. Let ω ∈ 𝒟^m(ℝ^P) be admissible for M_{ℝ^P}(∂Y), i.e. |ω(x)| ≤ 1 for all x. Then ζω is smooth with tsupport contained in K_δ, so ζω ∈ 𝒟^m(U), and |ζ(x)ω(x)| = ζ(x)|ω(x)| ≤ 1, so ζω is admissible for M_U(∂X). (Homogeneity of the Euclidean coefficient norm, directly from the definition covectorEuclideanNorm: for t ∈ ℝ and an m-covector α, |tα| = (Σ_I ((tα)(e_{I_1}, …, e_{I_m}))²)^{1/2} = (t²·Σ_I α(e_{I_1}, …, e_{I_m})²)^{1/2} = |t|·|α|, the sums running over the strictly increasing I : {1, …, m} → {1, …, P}; SimonGMT records only the cases t = 0 and t = −1. Here t = ζ(x) ∈ [0, 1].) On the open set V, ζω = ω, so d(ζω) = dω on V (the exterior derivative at a point only depends on the form near that point), in particular on M ∩ K ⊆ K ⊆ V. Using step 4 for dω and d(ζω) (both in 𝒟ⁿ(ℝ^P)) and step 5 for d(ζω) ∈ 𝒟ⁿ(U):
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
- `cat RUN/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean; mathlib/simongmt revs in lake-manifest.json`
- `python3 scans of RUN/dag.json: selected node and the frozen types of its six depends_on; nodes with lean_statement identical to the selected one (root.compactness_of_minimizing_currents-a1.flat_convergence-a1) and to each proposed child; statuses of that subtree; lean_name prefix dimred_mbl_fc (no match); node count 821`
- `read RUN/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1/decomposition-v1.json; git show a4486f3c7cd80fe7b0fa778632a5bc063d6a7748 (speculative assembly of cmc_flat_convergence)`
- `grep -n '_existing_lean_name_problem|depends_on|prerequisite_ids|existing_by_name' /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py; contract_scope/child_modules in verifier/gmt-compare.py`
- `#check after import GMT.Ch07.Submission: Poincare.SimonGMT.Chapter01.simon_theorem_4_16_compact_metrizable, MeasureTheory.FiniteMeasure, MonotoneOn.intervalIntegrable_deriv, MonotoneOn.intervalIntegral_deriv_mem_uIcc (unknown); Measure.countable_meas_level_set_pos, measurable_deriv, tendsto_of_subseq_tendsto, lintegral_liminf_le, Monotone.countable_not_continuousAt, IsCompact.tendsto_subseq, exists_contMDiffMap_one_nhds_of_subset_interior, IsCompact.exists_cthickening_subset_open, Finite.exists_infinite_fiber, extraction_of_frequently_atTop, measurable_measure_prodMk_left, lintegral_lintegral_swap, integral_withDensity_eq_integral_smul, withDensity_absolutelyContinuous, AEStronglyMeasurable.mono_ac, GeometricCurrentOn.boundary_boundary, WeaklyConvergesOn.boundary, WeaklyConvergesOn.massOn_le_liminf, countablyRectifiable_of_measure_zero (exist)`
- `lake env lean /tmp/fcB/FinalTypes.lean (8 child challenges) and /tmp/fcB/FinalAssembly.lean (#print axioms AssemblyCond); lean_contract.validate_lean_statement on all child types`
- `sed -n on SimonGMT Chapter06 Currents.lean (GeometricCurrentOn, TestFormOnConverges, WeaklyConvergesOn), Mass.lean (massAdmissibleOn, massOn, mass), CurrentLocalEquality.lean (restrictDomain, zeroRegion, support); book/chapter-06.txt lines 2000–2145 (7.1–7.2) and 290–305 (2.11)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-flat-convergence-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1/decomposition-v1.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/CompactMetrizableCompactness.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/fcB/FinalTypes.lean`
- `/tmp/fcB/FinalAssembly.lean`

The pins match: HEAD b4d606d, Mathlib 25730c7c, SimonGMT 2b366308. Submission.lean is byte-identical to the frozen contract.

Availability in the pinned libraries:
- SimonGMT supplies currents, sequential continuity, mass/massOn as sups over admissible forms, support, restrictDomain, weak convergence, ∂∂ = 0, boundary weak continuity and lower semicontinuity of mass.
- The pinned libraries lack flat convergence, the deformation theorem and slicing; these come from the parent's prerequisites.
- simon_theorem_4_16_compact_metrizable, FiniteMeasure and the MonotoneOn deriv-integral lemmas are outside the import closure. good_slice therefore uses Helly selection and Tonelli/Fatou instead.

The only accepted declaration with a child type is dtc_vanish_off_support, which is reused with its identical type. The parallel node cmc_flat_convergence has the identical parent type; its seven audited child types are reused verbatim under fresh dimred_mbl_fc_* names, since those nodes are unaccepted under another parent.

Results: all 8 child types elaborate, and the conditional assembly proves the exact parent type from the six prerequisite types and the child types (axioms propext, Classical.choice, Quot.sound).
