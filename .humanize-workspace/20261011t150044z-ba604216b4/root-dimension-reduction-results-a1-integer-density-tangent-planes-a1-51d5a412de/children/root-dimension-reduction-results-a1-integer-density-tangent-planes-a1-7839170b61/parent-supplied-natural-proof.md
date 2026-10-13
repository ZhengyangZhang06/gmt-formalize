# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.edge_tangent_plane-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.edge_tangent_plane-a1.edge_direction_support-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 (sector points of density k ≥ 1 lie in spt C) and the polar-coordinate computation of step 2(d) (y_j = a + λ_j e = t_j(cos φ_j a + sin φ_j e)) of the parent proof, specialised to σ = 0, u = 1. Notation: ω_2 := unitBallVolume 2; B_ρ(y) open ball.
1. (Choice of l₀.) Take l₀ := δ > 0. Fix l with 0 < l < δ.
2. (Polar form of a + l·e.) Put t := √(1 + l²) > 0 and φ := arctan l. Since l > 0, φ > 0 (Real.arctan_pos), and φ < l < δ (Real.arctan_lt_self). By Real.cos_arctan and Real.sin_arctan, cos φ = 1/√(1 + l²) and sin φ = l/√(1 + l²), hence t·cos φ = 1 and t·sin φ = l, and t•(cos φ•a + sin φ•e) = (t cos φ)•a + (t sin φ)•e = a + l•e. By the hypothesis (with these t, φ), HasMassDensity C y k for y := a + l•e: k ≥ 0 and the quotients q(ρ) := C.massOn(B_ρ(y))/(ω_2·ofReal(ρ²)) tend to ofReal(k) as ρ → 0⁺ (filter 𝓝[>] 0).
3. (Suppose y ∉ spt C.) Fix R ∈ IMRep(univ, 2) with R.Represents C (IsIntegerMultiplicity C). Apply the accepted lemma `Submission.dimred_im_mass_measure` (P, n := 2, U := univ, T := C, R; univ is open): (a) C.massOn W = R.measure W for every open W; (b) for x ∈ univ, x ∈ spt C iff R.measure(B_ε(x)) ≠ 0 for every ε > 0. Since y ∈ univ and y ∉ spt C, (b) gives ε > 0 with R.measure(B_ε(y)) = 0. For 0 < ρ < ε, by (a) and monotonicity, C.massOn(B_ρ(y)) = R.measure(B_ρ(y)) ≤ R.measure(B_ε(y)) = 0, so q(ρ) = 0/(ω_2·ofReal(ρ²)) = 0 (ENNReal.zero_div).
4. (Contradiction.) The interval (0, ε) belongs to 𝓝[>] 0, so q is eventually 0 along 𝓝[>] 0 and q → 0. The filter 𝓝[>] 0 on ℝ is non-trivial and [0, ∞] is Hausdorff, so limits are unique: ofReal(k) = 0, i.e. (k : ℝ) ≤ 0, contradicting k ≥ 1. Hence y = a + l•e ∈ spt C, for every 0 < l < l₀. ∎
(Remark, an equivalent route for steps 3–4 that uses only the definitions: if y ∉ spt C = univ \ zeroRegion C, then y lies in an open W on which C vanishes (C(ω) = 0 whenever tsupport ω ⊆ W); choose ε > 0 with B_ε(y) ⊆ W; for 0 < ρ < ε every mass-admissible form for B_ρ(y) has support in W, so every value ofReal(C ω) in the supremum defining C.massOn(B_ρ(y)) is 0 and C.massOn(B_ρ(y)) = 0; then conclude as in step 4.)

## Key steps

1. l₀ := δ; for 0 < l < δ, t := √(1+l²), φ := arctan l ∈ (0, δ) satisfy t(cos φ a + sin φ e) = a + l e.
2. Hence HasMassDensity C (a + l e) k with k ≥ 1.
3. If a + l e ∉ spt C, dimred_im_mass_measure gives massOn(B_ρ) = 0 for small ρ, so the density limit would be 0 ≠ ofReal k; contradiction.

## Reference use

### local-project

Queries:
- `python3 scan of dag.json: lean_statement/status of idtp_cone_tangent_cone_planar, dimred_im_mass_measure, dtc_blowUp_imrep, dimred_cs_mi_hasMassDensity_unique, rsd_imrep_compact_measure_ne_top, idtp_cse_massOn_ball_lower_bound, and of the cone_sector_endpoint_density and cone_tangent_cone_planar subtrees`
- `python3 scan of dag.json lean_statements for existing plane-IMRep / dilation-integral / local-finiteness / density-uniqueness lemmas (patterns '∃ R … IMRep … span|Submodule', 'Orthonormal … IMRep', 'dilation … R.measure … Tendsto', 'R.measure K ≠ ∞', 'HasMassDensity … θ = θ'')`
- `grep -lE 'idtp_cse_etp_' dag.json nodes/ GMT/ local-references/123e8435b4a2469b/project; ls ../.swarm-worktrees/*/gmt-ch07/GMT/Ch07/Submission.lean | xargs -P 16 grep -l idtp_cse_etp_ (no match anywhere)`
- `grep SimonGMT: def CountablyRectifiable, countablyRectifiable_range, def HasApproximateTangentSpaceAt, hasApproximateTangentSpaceAt_submodule, GeometricCurrentOn.support / zeroRegion / VanishesOn, GeometricCurrentOn.massOn / massAdmissibleOn, Covector / DifferentialForm / TestFormOn / GeometricCurrentOn`
- `grep Mathlib (workspace and snapshot): Isometry.euclideanHausdorffMeasure_preimage, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, withDensity_const, integral_smul_measure, integral_map, integral_const_mul, Real.arctan_lt_self, Real.arctan_pos, Real.cos_arctan, Real.sin_arctan, Real.one_sub_sq_div_two_le_cos, IsCompact.tendsto_subseq, isCompact_sphere, ContinuousAlternatingMap.apply, Submodule.starProjection_eq_self_iff, Submodule.eq_starProjection_of_mem_of_inner_eq_zero, Submodule.starProjection_inner_eq_zero, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero, Submodule.eq_of_le_of_finrank_eq, finrank_span_eq_card, Continuous.integrable_of_hasCompactSupport, tendsto_one_div_add_atTop_nhds_zero_nat`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean GMT/Ch07/Submission.lean (identical); lake-manifest.json mathlib rev vs manifest.json mathlib_commit (equal)`
- `lake env lean /tmp/etp_check/Stmts.lean; lake env lean /tmp/etp_check/Parent.lean; lake env lean /tmp/etp_review/All.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-51d5a412de/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-18ac87081c/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Arctan.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/tmp/etp_check/Stmts.lean`
- `/tmp/etp_check/Parent.lean`
- `/tmp/etp_review/All.lean`

Pins match: project b4d606db, mathlib 25730c7c and SimonGMT 2b36630. The snapshot Submission.lean is byte-identical to the workspace contract, which is the compiler authority. No existing DAG or library declaration provides any of the seven children: the flat-current IMRep, the blow-up push-forward vague limit, the frame sign, rescaled-limit membership, the cusp or the localization. All seven are therefore new, with unreserved idtp_cse_etp_* names (no occurrence in the DAG, node records, GMT/, the snapshot or any worktree). Reused accepted lemmas are dtc_blowUp_imrep, dimred_im_mass_measure, dimred_cs_mi_hasMassDensity_unique and rsd_imrep_compact_measure_ne_top; their DAG types match their uses. Every cited Mathlib/SimonGMT name exists at the pins. All 7 child types elaborate, and the parent's frozen type is kernel-checked from them with stubs. An independent reviewer fully formalized all 7 children using only standard axioms plus the accepted dtc_blowUp_imrep and dimred_im_mass_measure; I re-ran that file and it compiles.
