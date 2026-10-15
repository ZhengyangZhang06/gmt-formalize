# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.edge_tangent_plane-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.edge_tangent_plane-a1.plane_frame_sign-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the end of step 2(d) (Q = span{a, e} ⊆ Q' and equal dimensions give Q' = Q) and step 2(e) (orientation: α(τ) = det(O)·α(a, e)) of the parent proof. Notation: Q' := span{τ_0, τ_1} = Submodule.span ℝ (range τ), W := span{a, e}.
1. (dim Q' = 2.) τ is orthonormal, hence linearly independent (Orthonormal.linearIndependent), so finrank Q' = card(Fin 2) = 2 (finrank_span_eq_card).
2. (dim W = 2.) The pair ![a, e] is orthonormal (|a| = |e| = 1, ⟨a, e⟩ = 0, hence also ⟨e, a⟩ = 0), hence linearly independent, so finrank W = 2.
3. (Q' = Q.) W ≤ Q because a, e ∈ Q, and finrank W = 2 = finrank Q; since Q is finite-dimensional, W = Q (Submodule.eq_of_le_of_finrank_eq). Likewise W ≤ Q' because a, e ∈ Q' (hypothesis), and finrank W = 2 = finrank Q', so W = Q'. Hence Q' = W = Q, the first claim.
4. (Coordinates of τ.) For i ∈ {0, 1}, τ_i ∈ Q' = W = span{a, e}, so τ_i = x_i·a + y_i·e for some reals x_i, y_i (Submodule.mem_span_pair). Write p := x_0, q := y_0, r := x_1, s := y_1.
5. (Orthonormality in coordinates.) Using ⟨a, a⟩ = ⟨e, e⟩ = 1 and ⟨a, e⟩ = ⟨e, a⟩ = 0 and bilinearity of the inner product: 1 = |τ_0|² = p² + q², 1 = |τ_1|² = r² + s², and 0 = ⟨τ_0, τ_1⟩ = pr + qs.
6. (The determinant is ±1.) Put D := ps − qr. Lagrange's identity (ps − qr)² + (pr + qs)² = (p² + q²)(r² + s²) (expand both sides) gives D² = 1·1 − 0² = 1, hence D = 1 or D = −1. Let ε := 1 if D = 1 and ε := −1 if D = −1; then ε ∈ ℤ, |ε| = 1 and (ε : ℝ) = D.
7. (Covectors.) Let α ∈ Covector(ℝ^P, 2), a continuous alternating 2-linear map. Since a function on Fin 2 is determined by its two values, τ = ![τ_0, τ_1] = ![pa + qe, ra + se]. By linearity of α in each argument, α(τ) = pr·α(a, a) + ps·α(a, e) + qr·α(e, a) + qs·α(e, e). As α is alternating, α(a, a) = α(e, e) = 0 (map_eq_zero_of_eq) and α(e, a) = −α(a, e) (antisymmetry, from 0 = α(a + e, a + e) = α(a, e) + α(e, a)). Hence α(τ) = (ps − qr)·α(a, e) = D·α(a, e) = ε·α(![a, e]). ∎

## Key steps

1. finrank span τ = 2 and finrank span{a,e} = 2 (orthonormal ⇒ independent).
2. span{a,e} ≤ Q and ≤ span τ with equal finrank ⇒ span τ = span{a,e} = Q.
3. τ_i = x_i a + y_i e; orthonormality gives p²+q² = r²+s² = 1, pr+qs = 0, so D = ps − qr = ±1 (Lagrange identity).
4. Bilinearity + alternation: α(τ) = D·α(a, e); take ε := D ∈ {±1}.

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
