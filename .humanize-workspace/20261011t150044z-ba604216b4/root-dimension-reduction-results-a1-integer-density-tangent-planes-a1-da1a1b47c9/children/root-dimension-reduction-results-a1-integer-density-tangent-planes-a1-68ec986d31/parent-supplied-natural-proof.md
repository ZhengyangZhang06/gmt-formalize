# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1.subseq_criterion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. The filter 𝓝[>]0 on ℝ is countably generated: 𝓝 0 is countably generated (ℝ is first countable) and 𝓝[>]0 = 𝓝 0 ⊓ 𝓟(Ioi 0). Hence, by the subsequence criterion for countably generated filters (Mathlib `Filter.tendsto_of_subseq_tendsto`), it suffices to show: for every sequence ns : ℕ → ℝ with Tendsto ns atTop (𝓝[>]0) there is ms : ℕ → ℕ with f(ns(ms(j))) → L.
2. Let ns → 𝓝[>]0. Since Ioi 0 ∈ 𝓝[>]0, ns(n) > 0 for all large n; fix N ∈ ℕ with ns(n) > 0 for all n ≥ N. Since 𝓝[>]0 ≤ 𝓝 0, also ns(n) → 0.
3. Define λ_j := ns(j + N). Then λ_j > 0 for every j (because j + N ≥ N), and λ_j → 0, as the composition of ns → 0 with the map j ↦ j + N, which tends to atTop.
4. By the hypothesis applied to (λ_j) there is a strictly increasing φ with f(λ_{φ(j)}) → L. Put ms(j) := φ(j) + N. Then ns(ms(j)) = ns(φ(j) + N) = λ_{φ(j)}, so f(ns(ms(j))) = f(λ_{φ(j)}) → L.
5. By step 1, f(t) → L as t → 0⁺. ∎

## Key steps

1. 𝓝[>]0 is countably generated, so Filter.tendsto_of_subseq_tendsto reduces the claim to sequences ns → 𝓝[>]0.
2. Such ns is eventually positive and tends to 0; the shifted sequence λ_j = ns(j + N) is a positive null sequence.
3. The hypothesis applied to λ gives φ, and ms(j) = φ(j) + N is the required subsequence.

## Reference use

### local-project

Queries:
- `python3 scan of dag.json: lean_statement/status of the selected node, its siblings idtp_cse_edge_tangent_plane and idtp_cse_cone_stationary_radial, and accepted lemmas cbr_vague_portmanteau, cbr_imRep_measure_basic, cmc_fcl_imrep_integral_data, dtc_blowUp_testForm_corr, rsd_imrep_compact_measure_ne_top, dimred_cs_mi_hasMassDensity_unique, imrep_represents_support_eq_inter_measure_support, imrep_approxTangent_starProjection_aesm`
- `rg -n 'le_liminf_measure_open_of_tendsto|limsup_measure_closed_le_of_tendsto|tendsto_measure_thickening_of_isCompact|tendsto_measure_cthickening_of_isCompact|tendsto_measure_cthickening_of_isClosed' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n 'theorem euclideanHausdorffMeasure_eq_volume|Isometry.euclideanHausdorffMeasure_image|euclideanHausdorffMeasure_image' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n 'theorem tendsto_of_subseq_tendsto|lemma support_mem_ae :|theorem one_of_mem_closedBall|def mkContinuous|theorem volume_pi_Ioo|theorem ofReal_integral_eq_lintegral_ofReal|theorem tendsto_of_le_liminf_of_limsup_le' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n 'volume_preserving_measurableEquiv|theorem volume_preserving_ofLp|PiLp.volume_preserving' and namespace check of volume_Icc_pi in local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `grep -n 'HasApproximateTangentSpaceAt.unique|regular_euclideanHausdorffMeasure_restrict_submodule|def HasApproximateTangentSpaceAt' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean; grep 'abbrev Covector|abbrev TestFormOn|structure GeometricCurrentOn' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06`
- `grep -c <name> dag.json for all 8 idtp_cse_bml_* names (0 each); grep -rl idtp_cse_bml nodes/ (no match); rg -ln 'idtp_cse_bml|cbr_vague_portmanteau' local-references/123e8435b4a2469b/project (no match); parallel grep -rl --include=*.lean idtp_cse_bml over */gmt-ch07/GMT of 1127 ch07 worktrees (no match)`
- `lake env lean /tmp/bml-decomp-k7q2/check/Stmts.lean (8 types elaborate); ParentAx.lean (#print axioms: propext, Classical.choice, Quot.sound + named child/sibling/accepted axioms); M4.lean; Small.lean; Probe3.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-da1a1b47c9/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Portmanteau.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/CountablyGenerated.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/.swarm-worktrees/1d7c72121c37997a9fc2/gmt-ch07/GMT/Ch07/Submission.lean`
- `/tmp/bml-decomp-k7q2/check/Stmts.lean`
- `/tmp/bml-decomp-k7q2/check/ParentAx.lean`
- `/tmp/bml-decomp-k7q2/check/M4.lean`
- `/tmp/bml-decomp-k7q2/check/Small.lean`

The pins match: the workspace Submission.lean (GMT.Ch07, frozen opens) is the compiler authority, at mathlib 25730c7c and SimonGMT 2b36630.

Every Mathlib and SimonGMT name cited in the child proofs exists at these pins: Filter.tendsto_of_subseq_tendsto, Measure.support_mem_ae, ContDiffBump.one_of_mem_closedBall, AlternatingMap.mkContinuous, Isometry.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, PiLp.volume_preserving_ofLp, Real.volume_pi_Ioo / Real.volume_Icc_pi, ofReal_integral_eq_lintegral_ofReal, tendsto_of_le_liminf_of_limsup_le, tendsto_measure_cthickening_of_isCompact, HasApproximateTangentSpaceAt.unique and regular_euclideanHausdorffMeasure_restrict_submodule.

The accepted cross-branch lemmas used have these DAG types: cbr_vague_portmanteau (proved in worktree Submission.lean), cbr_imRep_measure_basic, cmc_fcl_imrep_integral_data, dtc_blowUp_testForm_corr, rsd_imrep_compact_measure_ne_top, dimred_cs_mi_hasMassDensity_unique and imrep_represents_support_eq_inter_measure_support. None of them, and neither sibling, reaches this node in the DAG.

The snapshot project (the frozen contract at b4d606db) has no idtp_cse_bml_* or cbr_* match. The 8 proposed names are unreserved everywhere.

All 8 types elaborate. The parent follows from the 4 direct children, the 2 siblings and the 4 accepted lemmas, kernel-checked with only standard axioms besides those named hypotheses. box_mass_limit follows from its 4 sibling children.
