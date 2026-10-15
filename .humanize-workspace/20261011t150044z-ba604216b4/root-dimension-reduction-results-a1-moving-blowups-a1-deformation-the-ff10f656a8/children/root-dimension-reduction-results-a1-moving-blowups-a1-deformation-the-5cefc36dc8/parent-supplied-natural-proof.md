# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.affine_homotopy-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Coordinates. p₀(y) := (WithLp.ofLp y) 0 : ℝ^{N+1} → ℝ and tail(y) := WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)) : ℝ^{N+1} → ℝ^N are continuous linear maps, and J(v) := WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v)) is linear ℝ^N → ℝ^{N+1}, hence a continuous linear map (finite dimension). By Fin.cons_zero, Fin.tail_cons and Fin.cons_succ: p₀(ι(t,x)) = t, tail(ι(t,x)) = x, ι(s,z) = s•e₀ + J(z) (compare coordinates with Fin.cases), and every w ∈ ℝ^{N+1} satisfies w = p₀(w)•e₀ + J(tail w). Moreover ‖w‖² = p₀(w)² + ‖tail w‖² (EuclideanSpace.norm_eq, Fin.sum_univ_succ), so |p₀(w)| ≤ ‖w‖ and ‖tail w‖ ≤ ‖w‖.
2. (i) Define H(y) := F(tail y) + p₀(y)•(G(tail y) − F(tail y)). It is C^∞: compositions of C^∞ maps with continuous linear maps, a difference, a product of the C^∞ scalar p₀ with a C^∞ map, and a sum. By step 1, H(ι(t,x)) = F(x) + t•(G(x) − F(x)).
3. (ii) Let y₀ := ι(t,x) and D := fderiv ℝ H y₀, so H has derivative D at y₀.
3.1. The curve c(s) := ι(s,x) = s•e₀ + J(x) has derivative e₀ at every s. By the chain rule (HasFDerivAt.comp_hasDerivAt at s = t, c(t) = y₀), s ↦ H(c(s)) has derivative D(e₀) at t. But H(c(s)) = F(x) + s•(G(x) − F(x)) for all s, whose derivative is G(x) − F(x). By uniqueness of derivatives D(e₀) = G(x) − F(x).
3.2. The map ℓ(z) := ι(t,z) = t•e₀ + J(z) has derivative J at x, so z ↦ H(ℓ(z)) has derivative D ∘L J at x (chain rule, ℓ(x) = y₀). But H(ℓ(z)) = F(z) + t•(G(z) − F(z)) for all z, which has derivative DF(x) + t•(DG(x) − DF(x)) at x because F and G are differentiable at x. By uniqueness of Fréchet derivatives, D(Jv) = DF(x)v + t•(DG(x)v − DF(x)v) for all v.
3.3. Let A := DF(x) + t•(DG(x) − DF(x)). For w ∈ ℝ^{N+1}, steps 1, 3.1, 3.2 give D(w) = p₀(w)•D(e₀) + D(J(tail w)) = p₀(w)•(G(x) − F(x)) + A(tail w), so ‖D(w)‖ ≤ |p₀(w)|·‖G(x) − F(x)‖ + ‖A‖·‖tail w‖ ≤ (‖G(x) − F(x)‖ + ‖A‖)·‖w‖. The constant is ≥ 0, so ContinuousLinearMap.opNorm_le_bound gives ‖D‖ ≤ ‖G(x) − F(x)‖ + ‖A‖.

## Key steps

1. coordinates p₀, tail, J with ι(s,z) = s•e₀ + Jz, w = p₀(w)e₀ + J(tail w), |p₀ w|, ‖tail w‖ ≤ ‖w‖
2. H(y) := F(tail y) + p₀(y)•(G − F)(tail y) is C^∞ and affine in t along ι
3. chain rule along s ↦ ι(s,x) gives DH e₀ = G(x) − F(x)
4. chain rule along z ↦ ι(t,z) gives DH∘J = DF(x) + t(DG(x) − DF(x))
5. operator-norm bound from the decomposition of w

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
