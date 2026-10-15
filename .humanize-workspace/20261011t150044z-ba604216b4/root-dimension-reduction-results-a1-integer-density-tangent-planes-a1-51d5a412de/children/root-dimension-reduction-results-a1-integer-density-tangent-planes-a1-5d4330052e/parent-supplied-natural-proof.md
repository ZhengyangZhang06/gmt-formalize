# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.edge_tangent_plane-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.edge_tangent_plane-a1.rescaled_limit_mem-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the common core of steps 2(d) and 3 of the parent proof (the test functions g_{w,r}, the inclusion of a small ball around a + λ_j w_j in η_j⁻¹ of a ball around w, the lower bound ω_2 r² for the rescaled integrals, and closedness). Notation: η_j := dilation a λ_j, so η_j(x) = −λ_j^{−1}a + λ_j^{−1}x = λ_j^{−1}(x − a); ω_2 := unitBallVolume 2 = volume(B_1(0) ⊆ Euclid 2); A_j(g) := λ_j^{−2}∫ g(η_j(x)) dμ(x).
1. (ω_2.) The open unit ball of Euclid 2 is nonempty and open, so it has positive Lebesgue measure (measure_ball_pos); it is bounded, so it has finite measure (measure_ball_lt_top). Hence κ := ω_2.toReal > 0, and for t ≥ 0, (ω_2·ofReal(t)).toReal = κ·t.
2. (Assume the contrary.) Suppose w ∉ S. As S is closed, its complement is open, so there is ρ > 0 with B_ρ(w) ∩ S = ∅. Put r := ρ/4 > 0 and g(z) := min(1, max(0, 2 − |z − w|/(2r))). Then g is continuous, 0 ≤ g ≤ 1, g(z) = 1 if |z − w| ≤ 2r, and g(z) = 0 if |z − w| ≥ 4r = ρ. Hence the support of g lies in closedBall(w, ρ), which is compact (ℝ^P is proper), so g has compact support; and g = 0 on S (points of S satisfy |z − w| ≥ ρ). Therefore ∫_S g dH² = 0 (setIntegral_eq_zero_of_forall_eq_zero), and (V) gives A_j(g) → m·0 = 0.
3. (Integrability.) η_j is a homeomorphism of ℝ^P (affine with linear part λ_j^{−1}·id, λ_j ≠ 0), so g∘η_j is continuous with compact support (support ⊆ η_j⁻¹(tsupport g), compact). Since μ is finite on compact sets (IsFiniteMeasureOnCompacts μ), g∘η_j is μ-integrable (Continuous.integrable_of_hasCompactSupport). Put B_j := B_{λ_j r}(a + λ_j w_j); B_j ⊆ closedBall(a + λ_j w_j, λ_j r), compact, so μ(B_j) < ∞ and the indicator 1_{B_j} is μ-integrable.
4. (Lower bound for large j.) By w_j → w and (L) (with this r), there is J such that for all j ≥ J: |w_j − w| < r and ω_2·ofReal((λ_j r)²) ≤ μ(B_j). Fix j ≥ J. For x ∈ B_j, η_j(x) − w_j = λ_j^{−1}(x − (a + λ_j w_j)), so |η_j(x) − w_j| < λ_j^{−1}·λ_j r = r, hence |η_j(x) − w| < 2r and g(η_j(x)) = 1. Since g ≥ 0 everywhere, 1_{B_j} ≤ g∘η_j pointwise, and integral monotonicity (both integrable, step 3) gives μ(B_j).toReal = ∫ 1_{B_j} dμ ≤ ∫ g∘η_j dμ. As μ(B_j) < ∞, monotonicity of ENNReal.toReal on finite values (ENNReal.toReal_mono) applied to ω_2·ofReal((λ_j r)²) ≤ μ(B_j) gives μ(B_j).toReal ≥ (ω_2·ofReal((λ_j r)²)).toReal = κλ_j²r² (step 1). Multiplying by λ_j^{−2} > 0: A_j(g) ≥ κ r² for every j ≥ J.
5. (Contradiction.) Passing to the limit in A_j(g) ≥ κr² (j ≥ J) gives 0 = lim A_j(g) ≥ κr² > 0 (ge_of_tendsto), which is impossible. Hence w ∈ S. ∎

## Key steps

1. ω_2 ∈ (0, ∞), κ := ω_2.toReal > 0.
2. If w ∉ S pick a bump g = 1 on closedBall(w, 2r), 0 off B_{4r}(w), with B_{4r}(w) ∩ S = ∅; then ∫_S g dH² = 0 and (V) forces λ_j^{−2}∫ g∘η_j dμ → 0.
3. For large j, |w_j − w| < r and η_j maps B_{λ_j r}(a + λ_j w_j) into B_{2r}(w), so ∫ g∘η_j dμ ≥ μ(B_{λ_j r}(a + λ_j w_j)) ≥ κλ_j²r² by (L).
4. Hence λ_j^{−2}∫ g∘η_j dμ ≥ κr² > 0 eventually, contradicting the limit 0; so w ∈ S.

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
