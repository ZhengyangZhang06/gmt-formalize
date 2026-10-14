# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.smooth_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

0. (LOC) denotes the locality conclusion of the sibling toolkit (dimred_mbl_dt_lpo_current_toolkit), available from (VO) and (REP). S(X) is compact: it is the image of the compact set Icc 0 1 ×ˢ spt X under the continuous map (t,x) ↦ ι(t,x) (WithLp.toLp, Fin.cons, WithLp.ofLp are continuous).
1. Slices of H. F, G, H are C^∞, hence differentiable. By the sibling affine_homotopy (ii) at t = 0 and t = 1, for all x, v: H(ι(0,x)) = F(x) + 0•(G x − F x) = F(x) and DH(ι(0,x))(Jv) = DF(x)v + 0•(…) = DF(x)v; H(ι(1,x)) = F(x) + 1•(G x − F x) = G(x) and DH(ι(1,x))(Jv) = DF(x)v + 1•(DG(x)v − DF(x)v) = DG(x)v.
2. Degree 0.
2.1. Apply the sibling cutoff (dimensions N+1 → N', degree 0, the C^∞ map H, the form ω, K = S(X)): there are θ'' ∈ 𝒟^0(ℝ^{N+1}) and an open W'' ⊇ S(X) with θ''(y) = H^#ω(y) and dθ''(y) = (dω(H y)).compContinuousLinearMap (DH y) for y ∈ W''.
2.2. By hypothesis θ = H^#(dω) on an open W_θ ⊇ S(X). Hence θ and the test form dθ'' = exteriorDerivativeTestOn univ 0 θ'' agree on the open set W_θ ∩ W'', which contains S(X) ⊇ spt C. By (LOC), C(θ) = C(dθ'') = ∂C(θ'') (GeometricCurrentOn.boundary_apply).
2.3. The boundary hypothesis for β := θ'' gives η₀, η₁ with η_s(x)(v) = θ''(ι(s,x))(J∘v) and ∂C(θ'') = X(η₁) − X(η₀).
2.4. X(η₀) = X(ηF): let W_F be the open set containing spt X on which ηF = F^#ω and V₀ := W_F ∩ {x : ι(0,x) ∈ W''}. V₀ is open (x ↦ ι(0,x) is continuous) and contains spt X (for x ∈ spt X, ι(0,x) ∈ S(X) ⊆ W'' since 0 ∈ [0,1]). For x ∈ V₀ and all v, by step 1 and ContinuousAlternatingMap.compContinuousLinearMap_apply: η₀(x)(v) = θ''(ι(0,x))(J∘v) = ω(H(ι(0,x)))(i ↦ DH(ι(0,x))(J v_i)) = ω(F x)(i ↦ DF(x)v_i) = (F^#ω)(x)(v) = ηF(x)(v). So η₀ = ηF on V₀ and (LOC) gives X(η₀) = X(ηF).
2.5. In the same way, with s = 1, G, the open set W_G on which ηG = G^#ω and V₁ := W_G ∩ {x : ι(1,x) ∈ W''}, we get η₁ = ηG on V₁ ⊇ spt X and X(η₁) = X(ηG).
2.6. Hence X(ηG) − X(ηF) = X(η₁) − X(η₀) = ∂C(θ'') = C(θ).
3. Degree k+1.
3.1. As in 2.1 with degree k+1: θ'' ∈ 𝒟^{k+1}(ℝ^{N+1}) and an open W'' ⊇ S(X) with θ'' = H^#ω and dθ'' = H^#(dω) on W''.
3.2. As in 2.2, θ = H^#(dω) = dθ'' on W_θ ∩ W'' ⊇ S(X) ⊇ spt C, so C(θ) = C(dθ'') = ∂C(θ'') by (LOC).
3.3. θ'' = H^#ω = θ' on the open set W'' ∩ W_θ' ⊇ S(X) ⊇ spt C', so C'(θ'') = C'(θ') by (LOC).
3.4. The boundary hypothesis for β := θ'' gives η₀, η₁ with η_s(x)(v) = θ''(ι(s,x))(J∘v) and ∂C(θ'') = X(η₁) − X(η₀) − C'(θ''); exactly as in 2.4–2.5 (now with v ∈ (ℝ^N)^{k+1}) X(η₀) = X(ηF) and X(η₁) = X(ηG).
3.5. Hence C(θ) = X(ηG) − X(ηF) − C'(θ'), i.e. X(ηG) − X(ηF) = C(θ) + C'(θ').

## Key steps

1. S(X) compact; slices of H at t = 0, 1 restrict to F, G with DH∘J = DF, DG (affine_homotopy)
2. cut-off θ'' = H^#ω near S(X) with dθ'' = H^#(dω) there (cutoff)
3. locality: C(θ) = C(dθ'') = ∂C(θ''); in degree k+1 also C'(θ'') = C'(θ')
4. boundary relation for θ''; its slices η₀, η₁ agree with F^#ω, G^#ω near spt X, so X(η₀) = X(ηF), X(η₁) = X(ηG)
5. rearrange

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (project_commit b4d606db, mathlib_commit 25730c7c); cmp SNAPSHOT/project/GMT/Ch07/Contract.lean workspace GMT/Ch07/Submission.lean (identical)`
- `rg -n -i "lipschitz.*push|pushforward.*lipschitz|mollif|cutoff|homotopy" SNAPSHOT/project/GMT -g "*.lean" (only the unproved Ch06 specification IsLipschitzPushforward / LipschitzPushforwardIntegerMultiplicity, not imported by Ch07); rg -c "dimred_mbl_dt_lpo" SNAPSHOT/project SNAPSHOT/mathlib (no match)`
- `grep -rn in SNAPSHOT/mathlib/Mathlib for dist_normed_convolution_le, HasCompactSupport.contDiff_convolution_left, norm_fderiv_le_of_lipschitz, norm_integral_le_of_norm_le_const (Bochner and intervalIntegral), extDeriv_pullback, hasStrictFDerivAt_compContinuousLinearMap, exists_contMDiffMap_one_nhds_of_subset_interior, IsCompact.exists_thickening_subset_open, ContinuousAlternatingMap.curryLeft_apply_apply, Fin.comp_cons, compContinuousLinearMap_apply (all found); grep for a ContDiff lemma for compContinuousLinearMap (none, so smoothness of pull-backs goes through analyticOnNhd_compContinuousLinearMapCLM)`
- `read SimonGMT Chapter06 Currents.lean, Mass.lean, CurrentLocalEquality.lean, Forms.lean, FormSupNorm.lean (GeometricCurrentOn, TestFormOnConverges, boundary_apply, boundary_boundary, ext, tsupport_exteriorDerivative_subset, exteriorDerivativeTestOn, massOn, mass, massOn_mono, le_massOn, covectorEuclideanNorm_neg, support, zeroRegion, isOpen_zeroRegion, exteriorDerivativeOn_pullbackFormWithin)`
- `python3 scans of RUN/dag.json: twin node cmcdt_lp_pushforward_operators and its 8 children (all decomposing, so names not shareable); accepted lean_statements for support calculus, bounded functional to current, locality, mass of differences, mollifiers, cut-off pull-backs (reused verbatim cmcsd_support_calculus and cmc_fc_sc_current_of_coeff_bound; also found cbrld_cone_eval_eq_of_eqOn_open, cmc_fc_cs_massOn_sub_le, dpf_pb_smooth_pullback_isTestForm; no accepted vector-valued Lipschitz mollifier, d-compatible cut-off pull-back or Lipschitz push-forward); no lean_name with prefix dimred_mbl_dt_lpo`
- `git show a95facf7331fbcc8f2266d39e1372ae42727bfa1:GMT/Ch07/Submission.lean (accepted dpf_pb_smooth_pullback_isTestForm proof: analyticOnNhd_compContinuousLinearMapCLM + ContDiff.clm_apply)`
- `lake env lean /tmp/opsplit-ffa/Stmts.lean (all 12 child types elaborate in the comparator scope; TestAssembly derives the exact selected type from the cylinder and covector_bounds sibling types and lpush_construction, lpush_properties, lipschitz_homotopy; #print axioms: propext, Classical.choice, Quot.sound); lake env lean /tmp/opsplit-ffa/wire/TestWire_{E,F,G,H,I,J}.lean (dependency applications typecheck); both validate_lean_statement implementations accept all 12 types`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-ff10f656a8/parent-child-handoff.json`
- `/tmp/opsplit-ffa/Stmts.lean`
- `/tmp/opsplit-ffa/wire/TestWire_G.lean`
- `/tmp/opsplit-ffa/wire/TestWire_J.lean`

Pins match: project b4d606db and Mathlib 25730c7c, and the workspace Submission equals the frozen Ch07 contract. None of the snapshot project, Mathlib or SimonGMT has a Lipschitz push-forward of currents, a mollifier for vector-valued Lipschitz maps, or a cut-off pull-back lemma that is compatible with the exterior derivative. The Ch06 push-forward is only an unproved specification, and Ch07 does not import it. The Mathlib infrastructure the children need does exist: normed ContDiffBump convolutions, extDeriv_pullback, the analytic precomposition operator, smooth Urysohn, thickenings, curryLeft and the integral bounds. Two required facts already exist as comparator-accepted DAG declarations with exactly the needed types, and are reused verbatim: cmcsd_support_calculus and cmc_fc_sc_current_of_coeff_bound. The ten new obligations use fresh, unused names (dimred_mbl_dt_lpo_*). All 12 types elaborate and pass both validators. A Lean assembly derives the exact selected type from the children and the two sibling contracts, using only propext, Classical.choice and Quot.sound.
