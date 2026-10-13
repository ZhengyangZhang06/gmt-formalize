# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.edge_tangent_plane-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.edge_tangent_plane-a1.blowup_vague_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2(a)–2(c) of the parent proof (representation of the limit, representations of the blow-ups, vague convergence (V)), for general n. Notation: Hⁿ := μHE[n], Q' := span(range τ), C_j := blowUp C a λ_j (hλ_j ≠ 0), η_j := dilation a λ_j, so η_j(x) = −λ_j^{−1}a + λ_j^{−1}x = λ_j^{−1}(x − a). Fix R ∈ IMRep(univ, n) with R.Represents C and a continuous g : ℝ^P → ℝ with compact support.
1. (A representation of C'.) By the sibling `Submission.idtp_cse_etp_plane_imrep` (P, n, τ, c; τ orthonormal, c ≠ 0) there is R' ∈ IMRep(univ, n) with R'.action ω = c·∫_{Q'} ω(x)(τ) dHⁿ for every ambient n-form ω, and R'.measure = (|c| : [0,∞])·Hⁿ⌞Q'. For every test form ω ∈ 𝒟ⁿ(ℝ^P), the hypothesis gives C'(ω) = c·∫_{Q'} ω(x)(τ) dHⁿ = R'.action ω, so R'.Represents C'. Moreover ∫ g dR'.measure = ((|c| : [0,∞]).toReal)·∫_{Q'} g dHⁿ = |c|·∫_{Q'} g dHⁿ (`integral_smul_measure`; toReal of a natural number cast is that number).
2. (Representations of the blow-ups.) For each j apply the accepted lemma `Submission.dtc_blowUp_imrep` with P, n, U := univ, T := C, x := a, lam := λ_j, hlam := (λ_j > 0) and the representation R: it gives R_j ∈ IMRep(dilation a λ_j '' univ, n) with R_j.Represents C_j (C_j = blowUp C a λ_j (hλ_j).ne', exactly the j-th current in the hypothesis MassMeasuresConverge) and R_j.measure(B) = ofReal(λ_j^{−n})·R.measure(η_j⁻¹(B)) for every measurable B. Choose such an R_j for every j (choice), obtaining a family (R_j)_j with R_j.Represents C_j for all j.
3. (Push-forward formula.) Fix j. η_j is continuous (affine), hence measurable. For every measurable B, (ofReal(λ_j^{−n})·(η_j)_#R.measure)(B) = ofReal(λ_j^{−n})·R.measure(η_j⁻¹(B)) = R_j.measure(B) (Measure.map_apply, smul_apply). Two measures that agree on all measurable sets are equal (Measure.ext), so R_j.measure = ofReal(λ_j^{−n})•(η_j)_#R.measure. Since g is continuous it is strongly measurable, so ∫ g dR_j.measure = (ofReal(λ_j^{−n})).toReal·∫ g d(η_j)_#R.measure (integral_smul_measure) = λ_j^{−n}·∫ g(η_j(x)) dR.measure(x) (integral_map with η_j measurable and g a.e.-strongly measurable; toReal(ofReal t) = t for t = λ_j^{−n} ≥ 0). Both identities hold without any integrability assumption.
4. (Vague convergence.) Apply MassMeasuresConverge (j ↦ C_j) C' to the family (R_j) (step 2), to R' (step 1, R'.Represents C') and to f := g (continuous, compactly supported, tsupport g ⊆ univ): ∫ g dR_j.measure → ∫ g dR'.measure. By steps 3 and 1 this says λ_j^{−n}·∫ g(η_j(x)) dR.measure(x) → |c|·∫_{Q'} g dHⁿ. ∎

## Key steps

1. plane_imrep gives R' representing C' with ∫ g dR'.measure = |c|∫_{Q'} g dHⁿ.
2. dtc_blowUp_imrep gives, for each j, R_j representing blowUp C a λ_j with R_j.measure = ofReal(λ_j^{−n})•(η_j)_#R.measure.
3. ∫ g dR_j.measure = λ_j^{−n}∫ g∘η_j dR.measure (integral_smul_measure, integral_map).
4. MassMeasuresConverge applied to (R_j), R', g yields the limit.

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
