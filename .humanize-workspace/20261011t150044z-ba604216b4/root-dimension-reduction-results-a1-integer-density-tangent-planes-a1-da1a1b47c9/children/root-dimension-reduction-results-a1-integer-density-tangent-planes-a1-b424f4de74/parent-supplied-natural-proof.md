# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1.tilt_decay-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation: d(x) := ξ(x)(β) = R.orient x β; η_λ := dilation a λ (η_λ(y) = λ^{-1}(y − a)); X(s') := ∫⁻_{B_{3s'}(a)} ofReal(1 − |d|) dμ.
0. (Facts about μ.) By the accepted Submission.cbr_imRep_measure_basic (W := univ): μ(K) < ∞ for every compact K, and R.orient is a.e.-strongly measurable for μ, hence so is d (composition with the continuous evaluation ξ ↦ ξ(β)). Since R represents C, C(ω) = ∫ ξ(x)(ω(x)) dμ(x) for every ω ∈ 𝒟²(ℝ^P) (accepted Submission.cmc_fcl_imrep_integral_data, last conjunct; equivalently R.Represents together with R.action ω = ∫ ξ(x)(ω x) dμ from cbr_imRep_measure_basic). Consequently every bounded a.e.-strongly measurable function vanishing outside a compact set is μ-integrable.
1. (Reduction.) By the sibling subseq_criterion (Submission.idtp_cse_bml_tendsto_nhdsGT_of_subseq) with f(s') := X(s')/ofReal(s'²) and L := 0, it suffices to show: for every sequence λ_j > 0 with λ_j → 0 there is a strictly increasing φ with X(λ_{φ(j)})/ofReal(λ_{φ(j)}²) → 0.
2. Fix such (λ_j) and take φ, C', c from (BP). Write t_j := λ_{φ(j)} > 0, η_j := η_{t_j} and C_j := blowUp C a t_j.
3. (Bump and test form.) Let ϑ be the smooth bump function (Mathlib ContDiffBump centered at 0 with rIn = 3 < rOut = 4): ϑ ∈ C^∞(ℝ^P), 0 ≤ ϑ ≤ 1, ϑ = 1 on B̄(0, 3) and support ϑ = B(0, 4); so ϑ is continuous with compact support (tsupport ϑ = B̄(0, 4)). Put ω_ϑ(x) := ϑ(x)•β. Then ω_ϑ is C^∞ (smooth scalar times a constant) with compact support, so ω_ϑ ∈ 𝒟²(ℝ^P) (TestFormOn univ 2), and ω_ϑ(x)(a, e) = ϑ(x)·β(a, e) = ϑ(x).
4. (Limit side.) dilation a t_j is a bijection of ℝ^P, so dilation a t_j '' univ = univ and ω_ϑ is a test form for the domain of C_j; hence currentEval(C_j, ω_ϑ) = C_j(ω_ϑ) (the `dif_pos` branch of currentEval). By ConvergesWeakly, C_j(ω_ϑ) → C'(ω_ϑ) = c∫_Q ϑ dH² = c·I, where I := ∫_Q ϑ dH² ≥ 0 (ϑ ≥ 0).
5. (Pull-back.) By the accepted Submission.dtc_blowUp_testForm_corr (U := univ, x := a, λ := t_j), there is ω'_j ∈ 𝒟²(ℝ^P) with ω'_j(y) = ω_ϑ(η_j(y)) = ϑ(η_j y)•β for all y, and C_j(ω_ϑ) = t_j^{-2}·C(ω'_j). By step 0 and linearity of ξ(y): C(ω'_j) = ∫ ξ(y)(ϑ(η_j y)•β) dμ(y) = ∫ ϑ(η_j y)·d(y) dμ(y). So C_j(ω_ϑ) = t_j^{-2}∫ (ϑ∘η_j)·d dμ.
6. (Integrability.) ϑ∘η_j is continuous with values in [0, 1] and vanishes outside η_j^{-1}(B̄(0, 4)) = B̄(a, 4t_j), a compact set of finite μ-measure. Since |d| ≤ 1 μ-a.e., the functions ϑ∘η_j, (ϑ∘η_j)·d, (ϑ∘η_j)·|d| and (ϑ∘η_j)(1 − |d|) are μ-integrable (step 0).
7. (Squeeze.) Put A_j := t_j^{-2}∫ ϑ∘η_j dμ, B_j := t_j^{-2}∫ (ϑ∘η_j)|d| dμ and D_j := A_j − B_j = t_j^{-2}∫ (ϑ∘η_j)(1 − |d|) dμ. As (ϑ∘η_j)(1 − |d|) ≥ 0 μ-a.e., D_j ≥ 0. By step 5 and |∫ h| ≤ ∫ |h|, |C_j(ω_ϑ)| ≤ t_j^{-2}∫ (ϑ∘η_j)|d| dμ = B_j, so 0 ≤ D_j ≤ A_j − |C_j(ω_ϑ)|. By the last clause of (BP) with g := ϑ, A_j → m·I; by step 4, |C_j(ω_ϑ)| → |c|·I = m·I. Hence A_j − |C_j(ω_ϑ)| → 0 and D_j → 0.
8. (Ball estimate.) For y ∈ B_{3t_j}(a), |η_j(y)| = |y − a|/t_j < 3, so ϑ(η_j y) = 1. Therefore 1_{B_{3t_j}(a)}(y)·ofReal(1 − |d(y)|) ≤ ofReal(ϑ(η_j y)(1 − |d(y)|)) for every y (equality on the ball; the right side is ≥ 0 off it). Integrating, X(t_j) ≤ ∫⁻ ofReal((ϑ∘η_j)(1 − |d|)) dμ = ofReal(∫ (ϑ∘η_j)(1 − |d|) dμ), by ofReal_integral_eq_lintegral_ofReal (the integrand is integrable and a.e. nonnegative). Multiplying by ofReal(t_j²)^{-1} = ofReal(t_j^{-2}): X(t_j)/ofReal(t_j²) ≤ ofReal(D_j).
9. Since D_j → 0, ofReal(D_j) → ofReal(0) = 0, and 0 ≤ X(t_j)/ofReal(t_j²) ≤ ofReal(D_j); hence X(t_j)/ofReal(t_j²) → 0, which is what step 1 requires. ∎

## Key steps

1. Reduce via subseq_criterion to the subsequence t_j given by (BP).
2. Test C_j = blowUp C a t_j against ω_ϑ = ϑ·β (ϑ a smooth bump, = 1 on B̄(0, 3)): C_j(ω_ϑ) → c∫_Q ϑ dH², and by dtc_blowUp_testForm_corr and the representation, C_j(ω_ϑ) = t_j^{-2}∫ (ϑ∘η_j)·ξ(β) dμ.
3. 0 ≤ t_j^{-2}∫ (ϑ∘η_j)(1 − |ξ(β)|) dμ ≤ t_j^{-2}∫ ϑ∘η_j dμ − |C_j(ω_ϑ)| → m∫_Q ϑ − |c|∫_Q ϑ = 0.
4. ϑ∘η_j = 1 on B_{3t_j}(a), so X(t_j)/ofReal(t_j²) is bounded by ofReal of that quantity, which tends to 0.

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
