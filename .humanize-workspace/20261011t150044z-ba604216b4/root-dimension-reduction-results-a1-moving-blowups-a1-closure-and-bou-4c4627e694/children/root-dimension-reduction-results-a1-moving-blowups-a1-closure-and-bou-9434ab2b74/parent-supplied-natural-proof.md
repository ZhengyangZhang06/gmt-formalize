# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.convergence_tools-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, T1, T2 and the paragraph (MM). Notation: ‖ω‖_∞ := sup_x |ω(x)| (Euclidean coefficient norm), ξ(ω) := x ↦ ξ(x)(ω(x)).

Part (T1): compactness of Radon measures.
1. If U = ∅ take φ := id and μ := 0; every assertion is trivial (the only compact/open subsets of U are empty and functions with tsupport in ∅ vanish). Assume U ≠ ∅ and put, for m ≥ 1, K_m := {x ∈ U : |x| ≤ m, dist(x, ℝ^P ∖ U) ≥ 1/m} (K_m := B̄_m(0) if U = ℝ^P). Each K_m is compact, K_m ⊆ int K_{m+1}, and ⋃_m K_m = U; every compact C ⊆ U lies in some K_m.
2. For each m the measures μ_j restricted to K_m are finite measures on the compact metrizable space K_m with sup_j μ_j(K_m) < ∞ (hypothesis). SimonGMT Chapter01 simon_theorem_4_16_compact_metrizable (applied on the subtype K_m to the pulled-back measures; its hypothesis ⨆_j μ_j(K) < ∞ for compact K ⊆ K_m holds by monotonicity) gives a subsequence along which ∫_{K_m} h dμ_j converges for every h ∈ C(K_m). A diagonal argument over m gives one strictly increasing φ : ℕ → ℕ such that for every m and every h ∈ C(K_m), lim_j ∫_{K_m} h dμ_{φ(j)} exists.
3. For f continuous with compact support, tsupport f ⊆ U, choose m with tsupport f ⊆ K_m; then ∫ f dμ_{φ(j)} = ∫_{K_m} f|_{K_m} dμ_{φ(j)} converges. Hence Λ(f) := lim_j ∫ f dμ_{φ(j)} is defined on C_c(U) (functions on the locally compact Hausdorff, σ-compact space U, extended by 0); Λ is linear and positive.
4. Riesz–Markov–Kakutani (Mathlib RealRMK.rieszMeasure on the subtype U, which is locally compact as an open subset of ℝ^P, IsOpen.locallyCompactSpace) gives a Borel measure μ_U on U, finite on compact sets, with Λ(f) = ∫ f dμ_U. Let μ := the push-forward of μ_U by the inclusion U ↪ ℝ^P (a measurable embedding as U is open). Then μ(ℝ^P ∖ U) = 0, μ(K) < ∞ for compact K ⊆ U, and ∫ f dμ = Λ(f) = lim_j ∫ f dμ_{φ(j)} for every continuous f with compact support in U.
5. limsup on compact sets: let C ⊆ U be compact (if C = ∅ both sides vanish) and ε₀ > 0 with C_{ε₀} := {dist(·, C) ≤ ε₀} ⊆ U. For 0 < ε ≤ ε₀ choose (Urysohn) f continuous, 0 ≤ f ≤ 1, f = 1 on C, f = 0 off {dist(·, C) < ε}; then μ_{φ(j)}(C) ≤ ∫ f dμ_{φ(j)} → ∫ f dμ ≤ μ(C_ε). Thus limsup_j μ_{φ(j)}(C) ≤ μ(C_ε) for every ε ∈ (0, ε₀]; as ε ↓ 0, C_ε ↓ C (C closed) and μ(C_{ε₀}) < ∞, so μ(C_ε) → μ(C) and limsup_j μ_{φ(j)}(C) ≤ μ(C).
6. liminf on open sets: let G ⊆ U be open. For compact C ⊆ G choose f continuous, 0 ≤ f ≤ 1, f = 1 on C, tsupport f ⊆ G compact; then μ(C) ≤ ∫ f dμ = lim_j ∫ f dμ_{φ(j)} ≤ liminf_j μ_{φ(j)}(G). G is the increasing union of countably many compact sets C_m, so μ(G) = sup_m μ(C_m) ≤ liminf_j μ_{φ(j)}(G).

Part (T2): convergence of restrictions.
7. Fix ω ∈ 𝒟^k(U); C := tsupport ω is compact ⊆ U and ‖ω‖_∞ < ∞. Put a_j := ∫_{f<t} ξ_j(ω) dμ_j and a := ∫_{f<t} ξ_X(ω) dμ_X. These are absolutely convergent: μ_j-a.e. (resp. μ_X-a.e.) |ξ_j(x)(ω(x))| ≤ |ω(x)| ≤ ‖ω‖_∞1_C(x), and μ_j(C), μ_X(C) < ∞.
8. Let ε > 0. The compact sets C₁ := C ∩ {f ≤ t − ε} and C₂ := C ∩ {f ≥ t} are disjoint (f continuous). Choose χ_ε ∈ C^∞(ℝ^P; [0, 1]) with compact support in the open set U ∖ C₂ and χ_ε = 1 on C₁ (smooth Urysohn function for the compact set C₁ inside the open set U ∖ C₂). Then χ_εω ∈ 𝒟^k(U).
9. On C we have 1_{f<t} − χ_ε = 0 where f ≤ t − ε (1 − 1) and where f ≥ t (0 − 0), and |1_{f<t} − χ_ε| ≤ 1 everywhere; ω = 0 off C. As ξ_j(x) is linear, X_j(χ_εω) = ∫ χ_ε ξ_j(ω) dμ_j, hence |a_j − X_j(χ_εω)| = |∫ (1_{f<t} − χ_ε) ξ_j(ω) dμ_j| ≤ ‖ω‖_∞ μ_j(C ∩ {t − ε ≤ f ≤ t}), and likewise |a − X(χ_εω)| ≤ ‖ω‖_∞ μ_X(C ∩ {t − ε < f < t}).
10. C ∩ {t − ε ≤ f ≤ t} is a compact subset of U, so limsup_j μ_j(C ∩ {t − ε ≤ f ≤ t}) ≤ μ(C ∩ {t − ε ≤ f ≤ t}) by hypothesis, and X_j(χ_εω) → X(χ_εω) by weak convergence. Therefore limsup_j |a_j − a| ≤ ‖ω‖_∞ (μ(C ∩ {t − ε ≤ f ≤ t}) + μ_X(C ∩ {t − ε < f < t})).
11. Let ε = 1/m → 0. The sets C ∩ {t − 1/m ≤ f ≤ t} decrease to C ∩ {f = t} and μ(C) < ∞, so their μ-measures tend to μ(C ∩ {f = t}) ≤ μ{f = t} = 0; the sets C ∩ {t − 1/m < f < t} decrease to ∅ and μ_X(C) < ∞, so their μ_X-measures tend to 0. Hence limsup_j |a_j − a| = 0, i.e. a_j → a.

Part (MM): measurable majorant of slice masses.
12. If b ≤ a then Ioo a b = ∅ and g := 0 works. Let a < b. For each j define F_j : ℝ → ℝ, F_j(t) := (μ_j(G ∩ {a < f < min(t, b)})).toReal. The sets increase with t and are contained in G ∩ {a < f < b}, of finite μ_j-measure, so F_j is nondecreasing, F_j(a) = 0 and F_j(b) = (μ_j(G ∩ {a < f < b})).toReal.
13. Let t ∈ (a, b) and 0 < h < t − a. The set S := {t − h < f < t} is Borel (f continuous), so for the (arbitrary) set E := G ∩ {a < f < t}, μ_j(E) = μ_j(E ∩ S) + μ_j(E ∖ S) (Mathlib measure_inter_add_sdiff), with E ∩ S = G ∩ {t − h < f < t} and E ∖ S ⊇ G ∩ {a < f < t − h}. All quantities are finite, so μ_j(G ∩ {t − h < f < t}) ≤ F_j(t) − F_j(t − h).
14. A monotone function ℝ → ℝ is differentiable a.e. (Mathlib Monotone.ae_differentiableAt); the union over j of the exceptional sets is null. If F_j is differentiable at t ∈ (a, b), then by step 13 ofReal(h⁻¹)·μ_j(G ∩ {t − h < f < t}) ≤ ofReal((F_j(t) − F_j(t − h))/h) → ofReal(F_j'(t)) as h ↓ 0, so liminf_{h↓0} ofReal(h⁻¹)μ_j(G ∩ {t − h < f < t}) ≤ ofReal(F_j'(t)) and, by the hypothesis, Z_j(t) ≤ L·ofReal(F_j'(t)).
15. Define g(t) := L · liminf_j ofReal(deriv F_j t). Each deriv F_j is measurable (Mathlib measurable_deriv), hence g is measurable. By step 14, for a.e. t ∈ (a, b): liminf_j Z_j(t) ≤ liminf_j (L·ofReal(F_j'(t))) = L·liminf_j ofReal(F_j'(t)) = g(t) (multiplication by the finite constant L is monotone and continuous on [0, ∞], so it commutes with liminf).
16. deriv F_j ≥ 0 (F_j is nondecreasing; where it is not differentiable deriv F_j = 0), deriv F_j is integrable on [a, b] (Mathlib MonotoneOn.intervalIntegrable_deriv) and ∫_a^b deriv F_j ≤ F_j(b) − F_j(a) (Mathlib MonotoneOn.intervalIntegral_deriv_mem_uIcc). Hence ∫⁻_{(a,b)} ofReal(deriv F_j) = ofReal(∫_a^b deriv F_j) ≤ μ_j(G ∩ {a < f < b}). By Fatou's lemma for measurable functions (Mathlib lintegral_liminf_le), ∫⁻_{(a,b)} g = L ∫⁻_{(a,b)} liminf_j ofReal(deriv F_j) ≤ L liminf_j ∫⁻_{(a,b)} ofReal(deriv F_j) ≤ L liminf_j μ_j(G ∩ {a < f < b}). This proves (MM). ∎

Implementation note: simon_theorem_4_16_compact_metrizable lives in the SimonGMT module Poincare.SimonGMT.Chapter01.CompactMetrizableCompactness, and MonotoneOn.intervalIntegrable_deriv and MonotoneOn.intervalIntegral_deriv_mem_uIcc in Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable; GMT.Ch07.Submission does not import these modules, so the formalization must import them.

Remark (how siblings use (MM)): if μ_j(G ∩ {a<f<b}) ≤ Λ < ∞ for all j, then ∫⁻ g < ∞, so g < ∞ a.e. and liminf_j Z_j(t) < ∞ for a.e. t ∈ (a, b) (for a constant sequence: Z(t) < ∞ a.e.); if μ_j(G ∩ {a<f<b}) → 0, then g = 0 a.e. and liminf_j Z_j(t) = 0 for a.e. t ∈ (a, b).

## Key steps

1. T1: exhaust U by compacts K_m, apply SimonGMT simon_theorem_4_16_compact_metrizable on each K_m and diagonalize.
2. T1: the limit functional on C_c(U) is positive linear; Riesz–Markov–Kakutani gives μ, pushed forward to ℝ^P.
3. T1: Urysohn approximations from above (compact sets) and below (open sets) give the limsup/liminf inequalities.
4. T2: for ε > 0 a smooth cutoff χ_ε ≡ 1 on C ∩ {f ≤ t−ε}, ≡ 0 on C ∩ {f ≥ t} reduces the restricted integrals to X_j(χ_εω) up to ‖ω‖_∞μ_j(C ∩ {t−ε ≤ f ≤ t}).
5. T2: limsup on the compact level band and μ{f = t} = 0, μ_X-continuity from above, and X_j(χ_εω) → X(χ_εω) give convergence.
6. MM: F_j(t) := μ_j(G ∩ {a < f < min(t,b)}) is monotone; the slice bound gives Z_j ≤ L F_j' wherever F_j is differentiable (a.e.).
7. MM: g := L liminf_j F_j' is measurable and Fatou with ∫_a^b F_j' ≤ F_j(b) − F_j(a) gives the integral bound.

## Reference use

### local-project

Queries:
- `cat RUN/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean; cmp SNAPSHOT/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean`
- `python3 scans of RUN/dag.json: selected node, frozen types and status of its five dependencies, lean_name matches for cbr_isoperimetric_filling (accepted, other parent) and for the prefix dmcbr_ (none among 937 nodes), byte comparison of the child types with the children of root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1`
- `grep -n '_existing_lean_name_problem|_accepted_checkpoint' /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `rg -c dmcbr SNAPSHOT (no match, exit 1); rg -n -i 'isoperimetric|closure theorem|FedererFleming|DeformationTheorem' SNAPSHOT/project/GMT -g '*.lean'`
- `rg -n -F over SNAPSHOT/mathlib/Mathlib, found: EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Isometry.euclideanHausdorffMeasure_image, MeasureTheory.Measure.euclideanHausdorffMeasure_smul₀, euclideanHausdorffMeasure_zero, euclideanHausdorffMeasure_zero_or_top, exists_disjoint_closedBall_covering_ae, ae_tendsto_average_norm_sub, tendsto_filterAt, tendstoUniformlyOn_of_ae_tendsto, lintegral_liminf_le, countable_meas_level_set_pos, measure_inter_add_sdiff, ext_of_generate_finite, isPiSystem_isOpen, MonotoneOn.intervalIntegral_deriv_mem_uIcc, MonotoneOn.intervalIntegrable_deriv, Monotone.ae_differentiableAt, measurable_deriv, rieszMeasure, LipschitzOnWith.extend_real, LipschitzOnWith.extend_pi, finite_approx_of_totallyBounded, hausdorffMeasure_zero_singleton, one_le_hausdorffMeasure_zero_of_nonempty, IsOpen.locallyCompactSpace, ext_of_forall_integral_eq_of_IsFiniteMeasure; not found as literal 'theorem X' headers but located as to_additive/namespace/alias/instance declarations: isAddLeftInvariant_eq_smul, AlternatingMap.map_linearDependent, MeasurableSet.exists_isClosed_diff_lt, Module.Finite.multilinearMap; no match: measure_inter_add_diff (the cited name is measure_inter_add_sdiff)`
- `rg -n over .lake/packages/simongmt/Poincare, all found: simon_theorem_4_16_compact_metrizable, simon_theorem_3_3, simon_theorem_3_26_i, exists_isClosed_continuousOn_of_measurable, simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure, realUnitBallVolume_nat_eq, measure_toOuterMeasure_isBorelRegular, exteriorDerivative_affinePullbackForm, GeometricCurrentOn.boundary_affinePushforward, WeaklyConvergesOn.massOn_le_liminf, WeaklyConvergesOn.boundary, GeometricCurrentOn.boundary_boundary, countablyRectifiable_of_measure_zero, countablyRectifiable_range, countablyRectifiable_iUnion, CountablyRectifiable.mono; sed on the massOn, support, restrictDomain, HasApproximateTangentSpaceAt and blowUpMap definitions`
- `lake env lean (v4.35.0-rc3) on /tmp/dimred_cbr2/lean/AllTypes.lean (12 types, sorry warnings only), /tmp/dimred_cbr2/lean/Assembly.lean (#print axioms: propext, Classical.choice, Quot.sound) and /tmp/dimred_cbr2/lean/InstCheck.lean; lean_contract.validate_lean_statement on all 12 types`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-4c4627e694/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-4c4627e694/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-ba6febc1b9/decomposition-audit-v1.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/Unique.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/HausdorffDensityBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/CompactMetrizableCompactness.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/dimred_cbr2/lean/AllTypes.lean`
- `/tmp/dimred_cbr2/lean/Assembly.lean`
- `/tmp/dimred_cbr2/lean/InstCheck.lean`

Pins match (HEAD b4d606d = snapshot project commit, Mathlib 25730c7c, SimonGMT 2b366308), and Submission.lean is byte-identical to the frozen contract and to the snapshot copy. The snapshot has no dmcbr declaration and no proved closure, deformation or isoperimetric theorem; its Chapter 6 matches are contract definitions only. Every Mathlib and SimonGMT name cited by the child proofs exists in the pinned sources. The five dependency types in dag.json are unchanged since attempt 1. cbr_isoperimetric_filling is accepted but owned by another parent and was reported reserved, so it is not reused; dmcbr_isoperimetric_filling and the other dmcbr_ names match no DAG node. All 12 child types elaborate, and the sorry-free conditional assembly proves the exact parent type with axioms propext, Classical.choice, Quot.sound.
