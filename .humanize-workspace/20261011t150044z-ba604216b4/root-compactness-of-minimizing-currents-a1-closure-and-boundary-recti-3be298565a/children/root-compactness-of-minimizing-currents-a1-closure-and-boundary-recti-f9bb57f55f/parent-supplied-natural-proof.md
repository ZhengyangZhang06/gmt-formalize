# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.slice_limit-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.slice_limit-a1.slice_boundary_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

This is the summed majorant of step 7 of the parent proof (slice mass plus slice-boundary mass); its boundary part absorbs the identity ∂Z_t = −∂B_t of step 9. Fix the data. For a Borel measure ν on ℝ^P, an open W and t ∈ ℝ write J_ν(h) := ofReal(h⁻¹) · ν(W ∩ {t − h < f < t}) ∈ [0, ∞] and ℓ_ν := liminf_{h → 0+} J_ν(h), the limit inferior along the filter 𝓝[>] 0.

1. First slicing. Apply (SL) with k := d, the open set U, T := X, the representations (μ, ξ) of X and (μ', ξ') of ∂X, the function f and the constant L (all its hypotheses are hypotheses of the present statement). It yields families A_t ∈ 𝒟_{d+1}(U), B_t ∈ 𝒟_d(U) with A_t(ω) = ∫_{f<t} ξ(ω) dμ and B_t(η) = ∫_{f<t} ξ'(η) dμ' for all t, ω, η; these are the required currents and give the first two conclusions. (SL) also gives M_W(Z_t) ≤ L ℓ_μ for every open W and every t, where Z_t := ∂A_t − B_t. Fix an open W and t ∈ ℝ; it remains to prove the combined bound.

2. Two inequalities in [0, ∞].
(i) For functions u, v with values in [0, ∞] and any filter F: liminf_F u + liminf_F v ≤ liminf_F (u + v). Indeed liminf_F u = sup_{S ∈ F} inf_{x ∈ S} u(x) (Filter.liminf_eq_iSup_iInf), and for S, S' ∈ F we have inf_{x∈S} u(x) + inf_{x∈S'} v(x) ≤ inf_{x ∈ S ∩ S'} (u(x) + v(x)) ≤ liminf_F (u + v), because S ∩ S' ∈ F. In [0, ∞], (sup_{S ∈ F} a_S) + (sup_{S' ∈ F} b_{S'}) ≤ c whenever a_S + b_{S'} ≤ c for all S, S' ∈ F (Mathlib ENNReal.biSup_add_biSup_le'; both index families are nonempty because univ ∈ F), which proves (i).
(ii) J_{μ+μ'}(h) = J_μ(h) + J_{μ'}(h) for every h, by (μ + μ')(E) = μ(E) + μ'(E) (Measure.add_apply) and distributivity. Hence, by (i) with F := 𝓝[>] 0, ℓ_μ + ℓ_{μ'} ≤ ℓ_{μ+μ'}, and multiplying by L (multiplication by a fixed element of [0, ∞] is monotone; mul_add): L ℓ_μ + L ℓ_{μ'} ≤ L ℓ_{μ+μ'}.

3. Case d = 0. Then Z_t is a 0-current and boundaryMassOn(Z_t, W) = 0 by definition. So M_W(Z_t) + boundaryMassOn(Z_t, W) = M_W(Z_t) ≤ L ℓ_μ ≤ L ℓ_μ + L ℓ_{μ'} ≤ L ℓ_{μ+μ'} by steps 1 and 2.

4. Case d = d' + 1.
(a) Second slicing. The current ∂X ∈ 𝒟_{d'+1}(U) has the admissible representation (μ', ξ') (hypothesis). Its boundary ∂∂X is 0 (SimonGMT GeometricCurrentOn.boundary_boundary) and has the admissible representation (0, 0) given by the zero measure and the zero field: the zero measure is finite on compact sets; every function is a.e. strongly measurable for the zero measure (aestronglyMeasurable_zero_measure); every a.e. statement holds for the zero measure (ae_zero); and ∂∂X(η) = 0 = ∫ 0 d0 (integral_zero_measure). Apply (SL) with k := d', U, T := ∂X, the representations (μ', ξ') of ∂X and (0, 0) of ∂∂X, f and L. It yields families A'_t ∈ 𝒟_{d'+1}(U), B'_t ∈ 𝒟_{d'}(U) with A'_t(η) = ∫_{f<t} ξ'(η) dμ' = B_t(η) for every test form η, B'_t(ζ) = ∫_{f<t} 0 d0 = 0 for every ζ, and M_W(∂A'_t − B'_t) ≤ L ℓ_{μ'}. Currents are determined by their values (GeometricCurrentOn.ext), so A'_t = B_t and B'_t = 0; hence ∂A'_t − B'_t = ∂B_t − 0 = ∂B_t and M_W(∂B_t) ≤ L ℓ_{μ'}.
(b) Boundary of the slice. The boundary is additive: (S − T).boundary(ζ) = (S − T)(dζ) = S(dζ) − T(dζ) = ∂S(ζ) − ∂T(ζ). Hence ∂Z_t = ∂∂A_t − ∂B_t = 0 − ∂B_t, using ∂∂A_t = 0 (GeometricCurrentOn.boundary_boundary).
(c) For every current S ∈ 𝒟_m(U) and every set W, M_W(0 − S) ≤ M_W(S). Indeed, if ω ∈ 𝒟^m(U) is admissible for M_W (tsupport ω ⊆ W and covectorEuclideanNorm(ω(x)) ≤ 1 for all x), then so is −ω (tsupport(−ω) = tsupport ω by tsupport_neg, and covectorEuclideanNorm(−α) = covectorEuclideanNorm(α) by SimonGMT covectorEuclideanNorm_neg), and (0 − S)(ω) = −S(ω) = S(−ω) by linearity (map_neg). Hence ofReal((0 − S)(ω)) = ofReal(S(−ω)) ≤ M_W(S) (GeometricCurrentOn.le_massOn), and taking the supremum over ω gives the claim.
(d) Therefore boundaryMassOn(Z_t, W) = M_W(∂Z_t) = M_W(0 − ∂B_t) ≤ M_W(∂B_t) ≤ L ℓ_{μ'}, and M_W(Z_t) + boundaryMassOn(Z_t, W) ≤ L ℓ_μ + L ℓ_{μ'} ≤ L ℓ_{μ+μ'} by steps 1, 4(a)–(c) and 2. ∎

## Key steps

1. (SL) for X with (μ, ξ), (μ', ξ') gives A_t, B_t with the integral formulas and M_W(∂A_t − B_t) ≤ L ℓ_μ.
2. In [0, ∞], liminf u + liminf v ≤ liminf (u + v), so L ℓ_μ + L ℓ_{μ'} ≤ L ℓ_{μ+μ'}.
3. If d = 0, boundaryMassOn is 0 and the bound follows.
4. If d = d' + 1, (SL) for ∂X with (μ', ξ') and the zero representation of ∂∂X = 0 identifies its first family with B_t and its second with 0, giving M_W(∂B_t) ≤ L ℓ_{μ'}.
5. ∂(∂A_t − B_t) = 0 − ∂B_t and M_W(0 − S) ≤ M_W(S) bound boundaryMassOn by L ℓ_{μ'}; add the two bounds.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp snapshot project/GMT/Ch07/Contract.lean with workspace GMT/Ch07/Contract.lean (identical); diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `rg -n "cbrsl_" <snapshot>/project (no match); rg -n "restrictDomain" <snapshot>/project/GMT --glob '*.lean' (only the blowUp definition in Contract/Submission); rg -n "theorem .*massOn_restrictDomain|boundary_restrictDomain|restrictDomain_restrictDomain" over <snapshot>/project, <snapshot>/mathlib/Mathlib and lake-packages-25730c7c/simongmt/Poincare (no match)`
- `grep -rn "theorem .*liminf_add\|theorem .*add_liminf\|lemma .*liminf_add" <snapshot>/mathlib/Mathlib --include=*.lean (only AddCommGroup and EReal versions; no ℝ≥0∞ version)`
- `grep -rn in <snapshot>/mathlib/Mathlib for: extraction_of_frequently_atTop, frequently_lt_of_liminf_lt (to_dual of frequently_lt_of_lt_limsup), liminf_le_of_frequently_le', limsup_eq_iInf_iSup (to_dual liminf_eq_iSup_iInf), limsup_comp, limsup_le_limsup_of_le, Tendsto.limsup_comp_le_limsup, ae_lt_top, ae_all_iff, ae_restrict_iff', countable_meas_level_set_pos, measure_eq_zero_iff_ae_notMem, Set.Countable.measure_zero, sigmaFinite_of_locallyFinite, isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts, Bornology.IsBounded.subset_ball, closure_ball_subset_closedBall, ball_subset_ball, ball_subset_ball', iSup_add_iSup_le, biSup_add_biSup_le', aestronglyMeasurable_zero_measure, integral_zero_measure, ae_zero, tsupport_neg, mul_le_mul_left' (absent in this Mathlib)`
- `reading lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,CurrentLocalEquality}.lean (GeometricCurrentOn, boundary, boundary_boundary, ext, zero_apply, WeaklyConvergesOn.boundary, massOn, massAdmissibleOn, le_massOn, massOn_mono, WeaklyConvergesOn.massOn_le_liminf, covectorEuclideanNorm_neg, restrictDomain, testFormOnInclusion)`
- `python3 -I scans of dag.json: node depth (3), statuses, frozen lean_statement of convergence_tools-a1 (cbr_measure_convergence_tools) and im_local-a1 (cbr_isIntegerMultiplicity_of_local), and collisions of the three proposed lean_names among 749 names (none; no 'cbrsl' prefix in use)`
- `sed -n of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/speculation.py contract() and runtime.py lines 1860-1960, 3160-3200, 6530-6620 (prerequisites = children + depends_on; depends_on restricted to sibling keys; cross-branch lean_name rule)`
- `python3 -I scope.py: verifier/lean_contract.py validate_lean_statement on the three statements (pass) and verifier/gmt-compare.py contract_scope(Contract.lean, GMT.Ch07.main_theorem) replay (open Filter Function Set MeasureTheory Metric; open scoped ENNReal Topology; namespace GMT.Ch07; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt); noncomputable section; end)`
- `lake env lean /tmp/slice-limit-decomp-x91/lean/{Check0,Assembly,Children,Children2,Final,FinalPP,Combined}.lean (Combined: childA/childB/childC axioms propext, Classical.choice, Quot.sound; parentAssembly proves the exact frozen parent type with only the two sibling stubs unproved)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/EReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/NullSingletonClass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Filter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/TestFunction.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-3be298565a/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-3be298565a/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-3be298565a/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-ba6febc1b9/parent-supplied-natural-proof.md`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/speculation.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/slice-limit-decomp-x91/lean/Assembly.lean`
- `/tmp/slice-limit-decomp-x91/lean/Combined.lean`
- `/tmp/slice-limit-decomp-x91/lean/Final.lean`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean. Neither the snapshot project, Mathlib nor SimonGMT has restriction-mass lemmas (massOn of restrictDomain, boundary of restrictDomain), an ℝ≥0∞ liminf-superadditivity lemma, a slicing or closure theorem, or any 'cbrsl_' declaration. Child A therefore proves the restriction facts itself and child B proves liminf superadditivity via liminf_eq_iSup_iInf and ENNReal.biSup_add_biSup_le'. Every other cited Mathlib/SimonGMT lemma exists at the pinned commits; mul_le_mul_left' is absent, and gcongr was used in the check. The runtime gives a child only its sibling depends_on and its own children, so CL(d), LOC, SL and MM enter the children verbatim as hypotheses that the parent discharges. All three exact statements pass validate_lean_statement and elaborate in the comparator's replayed scope. Full Lean proofs of all three children compile with only propext, Classical.choice and Quot.sound. A Lean proof of the exact frozen parent type from the children and the two frozen sibling types also compiles. The three names are unique among the 749 DAG names.
