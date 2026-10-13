# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1.box_mass_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation: η_λ := dilation a λ; for 0 < η < 1/2, U_η := {w : |w| < 3, |⟨w, a⟩| < 1 − η, |⟨w, e⟩| < 1 − η} and K_η := {w : |w| ≤ 3, |⟨w, a⟩| ≤ 1 + η, |⟨w, e⟩| ≤ 1 + η}; H(λ) := μ(Z(s, λ))/ofReal(λ²); ν := m·H²⌞Q, i.e. (m : [0,∞])•μHE[2].restrict Q.
1. (Reduction.) By the sibling subseq_criterion (Submission.idtp_cse_bml_tendsto_nhdsGT_of_subseq) with f := H and L := 4m, it suffices to show: for every sequence λ_j > 0 with λ_j → 0 there is a strictly increasing φ with H(λ_{φ(j)}) → 4m.
2. Fix such (λ_j). Take φ from (V) and put t_j := λ_{φ(j)}; then t_j > 0 and t_j → 0 (φ strictly increasing, so φ(j) → ∞).
3. (The limit measure.) By the sibling square_measure, H²⌞Q is finite on compact sets; hence so is ν (ν(K) = m·(H²⌞Q)(K) < ∞). For measurable S, ν(S) = m·(H²⌞Q)(S) (Measure.smul_apply). For continuous compactly supported g, ∫ g dν = m·∫_Q g dH² (integral_smul_measure, (m : [0,∞]).toReal = m). So (V) along φ reads: t_j^{-2}∫ g∘η_{t_j} dμ → ∫ g dν.
4. (Portmanteau.) The sibling rescaled_portmanteau, applied to μ, ν, a and (t_j), gives: (C) limsup_j ofReal(t_j^{-2})·μ(η_{t_j}^{-1}(K)) ≤ ν(K) for compact K; (O) ν(U) ≤ liminf_j ofReal(t_j^{-2})·μ(η_{t_j}^{-1}(U)) for open U.
5. (Rewriting H.) H(t_j) = μ(Z(s, t_j))·ofReal(t_j²)^{-1} = ofReal(t_j^{-2})·μ(Z(s, t_j)), since ofReal(t_j²)^{-1} = ofReal((t_j²)^{-1}) (t_j² > 0) and (t_j^{-1})² = (t_j²)^{-1}.
6. (Sandwich.) Fix η ∈ (0, 1/2). Since t_j → 0, for all large j: 20t_j < 1, 30t_j < η, 6t_j < s and t_j ≤ s. For such j, the sibling box_inclusions (with s' := t_j) gives η_{t_j}^{-1}(U_η) ⊆ Z(s, t_j) and Z(s, t_j) ∩ B_{3t_j}(a) ⊆ η_{t_j}^{-1}(K_η). By (L), μ(Z(s, t_j)) ≤ μ(Z(s, t_j) ∩ B_{3t_j}(a)) + μ(Z(s, t_j) ∖ B_{3t_j}(a)) = μ(Z(s, t_j) ∩ B_{3t_j}(a)) ≤ μ(η_{t_j}^{-1}(K_η)). Multiplying by ofReal(t_j^{-2}) and using step 5: eventually ofReal(t_j^{-2})·μ(η_{t_j}^{-1}(U_η)) ≤ H(t_j) ≤ ofReal(t_j^{-2})·μ(η_{t_j}^{-1}(K_η)).
7. (Bounds for fixed η.) U_η is open (intersection of strict sublevel sets of the continuous functions |w|, |⟨w, a⟩|, |⟨w, e⟩|), and K_η is closed and contained in B̄(0, 3), hence compact. Since 1 − η ∈ [0, 2] and 1 + η ∈ [0, 2], square_measure gives ν(U_η) = m·ofReal(4(1 − η)²) and ν(K_η) = m·ofReal(4(1 + η)²). Since liminf and limsup are monotone under eventual inequalities, (O), (C) and step 6 give m·ofReal(4(1 − η)²) ≤ liminf_j H(t_j) and limsup_j H(t_j) ≤ m·ofReal(4(1 + η)²).
8. (η → 0.) As η → 0⁺, m·ofReal(4(1 ∓ η)²) → m·ofReal(4) = 4m (continuity of ofReal and of multiplication by the finite constant m on [0, ∞]). As step 7 holds for every η ∈ (0, 1/2): 4m ≤ liminf_j H(t_j) and limsup_j H(t_j) ≤ 4m. In the complete linear order [0, ∞] this gives H(t_j) → 4m (tendsto_of_le_liminf_of_limsup_le).
9. By step 1, μ(Z(s, s'))/ofReal(s'²) → 4m as s' → 0⁺. ∎

## Key steps

1. Reduce via subseq_criterion to a subsequence t_j along which (V) holds.
2. ν := m·H²⌞Q is finite on compacts with ∫ g dν = m∫_Q g dH², so rescaled_portmanteau gives the liminf (open) / limsup (compact) bounds.
3. box_inclusions and (L) give, eventually, ofReal(t_j^{-2})μ(η^{-1}U_η) ≤ μ(Z(s, t_j))/ofReal(t_j²) ≤ ofReal(t_j^{-2})μ(η^{-1}K_η).
4. square_measure gives ν(U_η) = 4m(1 − η)² and ν(K_η) = 4m(1 + η)²; letting η → 0 squeezes liminf and limsup to 4m.

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
