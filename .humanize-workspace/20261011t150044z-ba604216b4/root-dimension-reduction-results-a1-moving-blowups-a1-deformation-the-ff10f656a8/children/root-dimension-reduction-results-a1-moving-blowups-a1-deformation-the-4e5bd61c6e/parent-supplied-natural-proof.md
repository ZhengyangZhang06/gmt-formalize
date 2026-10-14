# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.lpush_construction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Part A (one current). Fix N, N', k, Λ, a Λ-Lipschitz F and X ∈ NC_k(ℝ^N). We construct T ∈ 𝒟_k(ℝ^{N'}) with (★): for all Λ' ∈ ℝ, C^∞ Fs_j with ‖DFs_j(x)‖ ≤ Λ' on spt X and Fs_j → F uniformly on spt X, ω ∈ 𝒟^k(ℝ^{N'}) and ηs_j equal to Fs_j^#ω on open sets containing spt X, X(ηs_j) → T(ω).
A1. By the sibling mollify choose C^∞ Λ-Lipschitz F_j with dist(F_j x, F x) ≤ Λ/(j+1); then ‖DF_j(x)‖ ≤ Λ for all x (norm_fderiv_le_of_lipschitz) and F_j → F uniformly. For every ω and j choose, by the sibling cutoff (F_j, ω, K = spt X), a test form η°_j(ω) and an open W_j(ω) ⊇ spt X with η°_j(ω) = F_j^#ω on W_j(ω).
A2. For ω ∈ 𝒟^k(ℝ^{N'}), y ↦ |ω(y)| and y ↦ |dω(y)| are continuous with compact support (covectorEuclideanNorm is continuous: the square root of a finite sum of squares of the continuous evaluations α ↦ α(e_I)), so there are a_ω, b_ω with |ω(y)| ≤ a_ω and |dω(y)| ≤ b_ω for all y. For Λ₁ ∈ ℝ put K_ω(Λ₁) := Λ₁^k M(X).toReal b_ω + Λ₁^{k−1}(boundaryMassOn X univ).toReal a_ω.
A3. Cauchy property. For i, j apply the sibling cauchy_estimate with the C^∞ maps F_i, F_j (derivative bound Λ on spt X), δ_{ij} := Λ/(i+1) + Λ/(j+1) (dist(F_i x, F_j x) ≤ dist(F_i x, F x) + dist(F x, F_j x) ≤ δ_{ij}), a_ω, b_ω, ηF := η°_i(ω), ηG := η°_j(ω): |X(η°_j(ω)) − X(η°_i(ω))| ≤ δ_{ij}·K_ω(Λ). Since δ_{ij} → 0 as i, j → ∞, (X(η°_j(ω)))_j is Cauchy in ℝ; let L(ω) be its limit (CauchySeq.tendsto_limUnder).
A4. (★) for L. Let Λ', Fs, ω, ηs be as in (★) and Λ'' := max(Λ, Λ'). Given ε > 0, uniform convergence gives j₀ with dist(F x, Fs_j x) < ε for j ≥ j₀, x ∈ spt X. For j ≥ j₀ apply cauchy_estimate with F' := F_j, G' := Fs_j (‖DF_j(x)‖ ≤ Λ ≤ Λ'' and ‖DFs_j(x)‖ ≤ Λ' ≤ Λ'' on spt X), δ := Λ/(j+1) + ε (dist(F_j x, Fs_j x) ≤ Λ/(j+1) + ε on spt X), a_ω, b_ω, ηF := η°_j(ω), ηG := ηs_j: |X(ηs_j) − X(η°_j(ω))| ≤ (Λ/(j+1) + ε)·K_ω(Λ''). Hence limsup_j |X(ηs_j) − X(η°_j(ω))| ≤ ε·K_ω(Λ'') for every ε > 0, so X(ηs_j) − X(η°_j(ω)) → 0 and X(ηs_j) → L(ω).
A5. Linearity. For ω, ω' and r ∈ ℝ, the test forms η°_j(ω) + η°_j(ω') and r•η°_j(ω) equal F_j^#(ω + ω') on W_j(ω) ∩ W_j(ω') ⊇ spt X, resp. F_j^#(rω) on W_j(ω) ⊇ spt X, because α ↦ α.compContinuousLinearMap A is linear. A4 applied to the sequence (F_j) itself (C^∞, ‖DF_j‖ ≤ Λ, F_j → F uniformly) gives X(η°_j(ω) + η°_j(ω')) → L(ω + ω') and X(r•η°_j(ω)) → L(rω); by linearity of X these sequences equal X(η°_j(ω)) + X(η°_j(ω')) → L(ω) + L(ω') and r X(η°_j(ω)) → r L(ω). By uniqueness of limits L is additive and homogeneous, i.e. a linear map 𝒟^k(ℝ^{N'}) →ₗ ℝ.
A6. Bound. Let c > 0 with |ω(y)| ≤ c for all y. For x ∈ spt X ⊆ W_j(ω), by (L1), |η°_j(ω)(x)| = |(ω(F_j x)).compContinuousLinearMap (DF_j x)| ≤ ‖DF_j(x)‖^k |ω(F_j x)| ≤ Λ^k c. By the toolkit (A0), |X(η°_j(ω))| ≤ Λ^k c M(X).toReal, and in the limit |L(ω)| ≤ c·(Λ^k M(X).toReal).
A7. By the reused lemma cmc_fc_sc_current_of_coeff_bound (U = univ, A := Λ^k M(X).toReal) there is T ∈ 𝒟_k(ℝ^{N'}) with T(ω) = L(ω) for all ω, and by A4 T satisfies (★).
Part B (the operator). Using classical choice, define lpush N N' k F X := the current T of Part A built with a chosen Lipschitz constant Λ₀ of F, if (∃ Λ, LipschitzWith Λ F) ∧ IsCompact (spt X) ∧ M(X) < ∞ ∧ boundaryMassOn X univ < ∞, and := 0 otherwise. Given the data of CHAR (F Λ-Lipschitz, X NC, Fs, ω, ηs with the stated properties), the first case applies, so lpush N N' k F X is the current of Part A, and (★) — whose content does not involve the Lipschitz constant — gives X(ηs_j) → lpush N N' k F X (ω). This is CHAR.

## Key steps

1. mollifiers F_j and cut-off pull-backs η°_j(ω) (mollify, cutoff)
2. Cauchy property of X(η°_j(ω)) from the estimate (E) (cauchy_estimate); limit L(ω)
3. every admissible approximating sequence has the same limit (E again)
4. L is linear (characterization + uniqueness of limits) and |L ω| ≤ c Λ^k M(X) (A0, L1)
5. L is a current (cmc_fc_sc_current_of_coeff_bound); define lpush by choice, 0 off the NC/Lipschitz domain

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
