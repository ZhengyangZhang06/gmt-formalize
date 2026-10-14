# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.slice_limit-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.slice_limit-a1.slice_sum_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent step 3 ((SL) for X_i and, if d ≥ 1, (SL) for ∂X_i with the representation (0, 0) of ∂∂X_i = 0), the identity ∂Z_{i,t} = −∂B_{i,t} of step 6 and the summed majorant (μ_i + μ'_i) of step 4, for one current X. Uses the accepted siblings boundary_slice (dmcbr_sl_sb_boundaryMassOn_slice_le), mass_neg (dmcbr_sl_sb_massOn_eq_of_apply_eq_neg) and liminf_add (dmcbr_sl_sb_ennreal_liminf_add_le). Notation: for an open W, t ∈ ℝ and a measure ν on ℝ^P, S_h := W ∩ {t − h < f < t} and ℓ_ν := liminf_{h→0+} ofReal(h⁻¹)ν(S_h) (liminf along 𝓝[>]0, in [0, ∞]).
1. First slicing. Apply (SL) with k := d, the open U, T := X, the representations (μ, ξ) of X and (μ', ξ') of ∂X, f and L; all its hypotheses are hypotheses of the statement. It yields families A_t ∈ 𝒟_{d+1}(U), B_t ∈ 𝒟_d(U) with A_t(ω) = ∫_{f<t}ξ(ω)dμ and B_t(η) = ∫_{f<t}ξ'(η)dμ' for all t, ω, η; these are the required families. It also gives (i) M_W(∂A_t − B_t) ≤ L·ℓ_μ for every open W and every t. Fix an open W and t ∈ ℝ and put Z_t := ∂A_t − B_t; it remains to prove the combined bound.
2. boundaryMassOn(Z_t, W) = boundaryMassOn(B_t, W). Prove, for a fresh degree m (case split on m, not on d), that boundaryMassOn(∂A' − B', W) = boundaryMassOn(B', W) for all A' ∈ 𝒟_{m+1}(U) and B' ∈ 𝒟_m(U). If m = 0 both sides are 0 by the definition of boundaryMassOn. If m = e + 1, let ζ ∈ 𝒟^e(U). Subtraction of currents is pointwise and ∂T(ζ) = T(dζ) (SimonGMT GeometricCurrentOn.boundary_apply), so ∂(∂A' − B')(ζ) = (∂A' − B')(dζ) = ∂A'(dζ) − B'(dζ) = ∂∂A'(ζ) − ∂B'(ζ). Since ∂∂A' = 0 (GeometricCurrentOn.boundary_boundary), this equals −∂B'(ζ). Hence mass_neg (with n := e, T₁ := ∂(∂A' − B'), T₂ := ∂B') gives M_W(∂(∂A' − B')) = M_W(∂B'), which is the claim for m = e + 1. Apply it with m := d, A' := A_t, B' := B_t.
3. Boundary bound. Apply boundary_slice with (SL), m := d, the open U, T := X, the representation (μ', ξ') of ∂X (finite on compacts of U, a.e. strongly measurable, a.e. bounded, ∂X(η) = ∫ξ'(η)dμ'), f, L, t, B := B_t (whose values are ∫_{f<t}ξ'(η)dμ' by step 1) and the open W. It gives boundaryMassOn(B_t, W) ≤ L·ℓ_{μ'}, so by step 2 boundaryMassOn(Z_t, W) ≤ L·ℓ_{μ'}.
4. Summation. For every h, ofReal(h⁻¹)·(μ + μ')(S_h) = ofReal(h⁻¹)·μ(S_h) + ofReal(h⁻¹)·μ'(S_h) (Measure.add_apply and mul_add). By liminf_add with ι := ℝ and F := 𝓝[>]0, ℓ_μ + ℓ_{μ'} ≤ ℓ_{μ+μ'}.
5. Conclusion. By (i), step 3, distributivity and step 4 (multiplication by L in [0, ∞] is monotone): M_W(Z_t) + boundaryMassOn(Z_t, W) ≤ L·ℓ_μ + L·ℓ_{μ'} = L·(ℓ_μ + ℓ_{μ'}) ≤ L·ℓ_{μ+μ'}. ∎

## Key steps

1. (SL) for X with (μ, ξ), (μ', ξ') gives A_t, B_t with the integral identities and M_W(∂A_t − B_t) ≤ L·ℓ_μ.
2. For a fresh degree m, ∂(∂A' − B') = −∂B' pointwise (∂∂ = 0), so boundaryMassOn(∂A' − B', W) = boundaryMassOn(B', W) by mass_neg (both 0 if m = 0).
3. boundary_slice ((SL) for ∂X with the zero representation of ∂∂X) gives boundaryMassOn(B_t, W) ≤ L·ℓ_{μ'}.
4. (μ + μ')(S_h) splits termwise and liminf_add gives L·ℓ_μ + L·ℓ_{μ'} ≤ L·ℓ_{μ+μ'}.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp project/GMT/Ch07/Contract.lean against workspace GMT/Ch07/Contract.lean and Submission.lean (identical)`
- `rg -n "theorem countable_meas_level_set_pos|theorem ae_lt_top |theorem ae_restrict_iff' |theorem ae_all_iff|theorem Countable.measure_zero|sigmaFinite_of_locallyFinite|isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts" mathlib/Mathlib/MeasureTheory`
- `rg -n "theorem extraction_of_frequently_atTop |theorem frequently_lt_of_liminf_lt|theorem limsup_comp |theorem limsup_le_limsup_of_le|theorem liminf_le_of_frequently_le'|theorem liminf_le_liminf " mathlib/Mathlib/Order; rg -n "frequently_lt_of_liminf_lt|^theorem limsup_comp" mathlib/Mathlib/Order/LiminfLimsup.lean; rg -n "closure_ball_subset_closedBall" mathlib/Mathlib/Topology/MetricSpace`
- `rg -n "restrictDomain|massOn" project/GMT/Ch07 (contract definitions only; no restriction or slice lemmas in the snapshot project)`
- `grep/sed of SimonGMT Chapter06 Currents.lean (GeometricCurrentOn, WeaklyConvergesOn, boundary_apply, boundary_boundary), Mass.lean (massAdmissibleOn, massOn, massOn_mono, le_massOn, WeaklyConvergesOn.massOn_le_liminf), CurrentLocalEquality.lean (restrictDomain, testFormOnInclusion)`
- `python3 -I over dag.json: statuses/types of cmc_slice_mass_bounds, dtc_bc_tc_cl_foundations, cmc_exists_massRepresentation, cbr_slice_mass_majorant, cbr_sublevel_restriction_tendsto, dtc_restrictDomain_isIntegerMultiplicity, dmcbr_sl_sb_*; string equality (MM)=cbr_slice_mass_majorant, (T2)=cbr_sublevel_restriction_tendsto, (REP)=cmc_exists_massRepresentation; parallel decompositions of cbr_slice_property_of_weak_limit and dmcbr_slice_property_of_weak_limit and their children; name and identical-type scan for the 5 new names`
- `lake env lean /tmp/dtc_sl_split/FinalCheck.lean (8 child types, proofs of 5 new children, assembly of the selected type; #print axioms) and /tmp/dtc_sl_split/Test4.lean (restriction-composition variant of local_closure: kernel deterministic timeout)`
- `verifier/lean_contract.py validate_lean_statement on all 8 lean_statements; verifier/gmt-compare.py contract_scope for the comparator prefix`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-c5ce175623/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-e6c3d0d31e/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-3be298565a/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-1c173fa73c/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-788730048c/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/dtc_sl_split/FinalCheck.lean`
- `/tmp/dtc_sl_split/Test4.lean`
- `/tmp/dtc_sl_split/subs.json`

The snapshot (local-project, project b4d606db, Mathlib 25730c7c) has a Ch07 Contract.lean byte-identical to the workspace Contract.lean and Submission.lean. It contains no restriction-mass, slice-convergence or local-closure lemma: the project matches only definitions. Every Mathlib lemma named in the child proofs exists at the pinned revision: countable_meas_level_set_pos (SFinite.lean:320), the instances sigmaFinite_of_locallyFinite and isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts, ae_lt_top (Markov.lean:159), ae_restrict_iff' (Restrict.lean:629), ae_all_iff (AE.lean:151), extraction_of_frequently_atTop (AtTopBot/Basic.lean:114), frequently_lt_of_liminf_lt (to_dual at LiminfLimsup.lean:645), limsup_le_limsup_of_le, liminf_le_of_frequently_le' and closure_ball_subset_closedBall. They resolve after import GMT.Ch07.Submission. The SimonGMT facts used are boundary_apply, boundary_boundary, restrictDomain, massOn_mono, le_massOn and WeaklyConvergesOn.massOn_le_liminf. Foundations' (MM) and (T2) conjuncts are byte-equal to the accepted cbr_slice_mass_majorant and cbr_sublevel_restriction_tendsto. The three reused dmcbr_sl_sb_* declarations are accepted with types byte-identical to the submitted ones. FinalCheck.lean proves all five new children and the selected type from the children plus the slicing and foundations types, with axioms propext, Classical.choice and Quot.sound. An independent reviewer reproduced this and accepted. The restriction-composition variant of local_closure hit a kernel timeout, so the direct-ball route is prescribed.
