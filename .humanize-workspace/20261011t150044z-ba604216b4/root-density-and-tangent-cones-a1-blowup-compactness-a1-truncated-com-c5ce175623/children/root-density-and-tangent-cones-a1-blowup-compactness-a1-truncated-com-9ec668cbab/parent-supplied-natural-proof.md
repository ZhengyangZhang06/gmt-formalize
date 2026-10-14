# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.slice_limit-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.slice_limit-a1.level_null-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent proof ("ν{f = t} = ν'{f = t} = 0 off a countable set (countable_meas_level_set_pos)"), stated for one measure ν. Write E_t := {x : f(x) = t}.
1. ν is s-finite. By hypothesis ν is finite on every compact set (Mathlib class IsFiniteMeasureOnCompacts, built from the hypothesis as ⟨fun K hK => h K hK⟩). ℝ^P is locally compact, so every point has a compact neighbourhood (a closed ball) of finite ν-measure, i.e. ν is locally finite (Mathlib instance isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts). A locally finite measure on a second-countable space is σ-finite (Mathlib instance sigmaFinite_of_locallyFinite; ℝ^P is second countable), hence s-finite.
2. Countably many charged levels. The sets E_t (t ∈ ℝ) are measurable (f is measurable and singletons of ℝ are measurable) and pairwise disjoint. For an s-finite measure and measurable f, the set S := {t ∈ ℝ : 0 < ν(E_t)} is countable (Mathlib Measure.countable_meas_level_set_pos). For completeness: write ν = Σ_n ν_n with finite ν_n; if ν(E_t) > 0 then ν_n(E_t) > 1/m for some n, m ∈ ℕ; for fixed n, m at most m·ν_n(ℝ^P) of the disjoint sets E_t satisfy ν_n(E_t) > 1/m; so S is a countable union of finite sets.
3. A countable subset of ℝ is Lebesgue-null (it is a countable union of null singletons; Set.Countable.measure_zero). Hence L¹(S) = 0.
4. In [0, ∞], ν(E_t) ≠ 0 if and only if 0 < ν(E_t) (pos_iff_ne_zero). Therefore L¹({t : ¬ ν(E_t) = 0}) = L¹(S) = 0, which is exactly the statement that ν(E_t) = 0 for L¹-a.e. t (Mathlib ae_iff). ∎

## Key steps

1. ν is finite on compact sets, hence locally finite and σ-finite (s-finite) on ℝ^P.
2. Measure.countable_meas_level_set_pos: only countably many of the disjoint level sets {f = t} have positive ν-measure.
3. Countable subsets of ℝ are Lebesgue-null, so ν{f = t} = 0 for a.e. t (ae_iff).

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
