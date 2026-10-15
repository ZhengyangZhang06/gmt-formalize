# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.cylinder-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.cylinder-a1.cylinder_current-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 2 (definition cyl(X)(ω) := ∫_0^1 X(η^ω_t) dt, continuity of the integrand, linearity, the bound |cyl(X)(ω)| ≤ M(X)‖ω‖, current property and M(cyl X) ≤ M(X)) and step 4 (support).
- Step 1 of the parent is supplied by the sibling slice_forms.
- 0(b) is supplied by the reused siblings abs_le_mass (cmc_fc_sc_abs_le_mul_mass) and bounded_current (cmc_fc_sc_current_of_coeff_bound).
- 0(c)(S1) is supplied by the reused sibling support_vanish (rsd_cmr_support_subset_of_vanish).
- (CB) and (VO) are the antecedents; (CB) is passed to slice_forms.

A slice family of ω is a family η : ℝ → 𝒟^k(ℝ^N) with η_t(x)(v) = ω(ι(t, x))(e₀, Jv_1, …, Jv_k) for all t, x, v. M^ℝ := M(X).toReal ≥ 0.

1. Slice families. By slice_forms (A1), choose for every ω ∈ 𝒟^{k+1}(ℝ^{N+1}) a slice family η^ω. Any two slice families η, η' of the same ω are equal: η_t(x)(v) = η'_t(x)(v) for all t, x, v, so η_t(x) = η'_t(x) (ext), and η_t = η'_t in 𝒟^k(ℝ^N) (Subtype.ext, funext).

2. Continuity of t ↦ X(η_t). Let η be a slice family of ω and c ≥ 0 the constant of slice_forms (A2) for ω.
   (a) For s, t and ε > 0, the test form η_s − η_t satisfies |(η_s − η_t)(x)| = |η_s(x) − η_t(x)| ≤ c|s − t| ≤ c|s − t| + ε for all x, by (A2)(ii).
   (b) Since c|s − t| + ε > 0 and M(X) ≠ ∞, abs_le_mass gives |X(η_s) − X(η_t)| = |X(η_s − η_t)| ≤ (c|s − t| + ε)·M^ℝ.
   (c) Letting ε ↓ 0, |X(η_s) − X(η_t)| ≤ c·M^ℝ·|s − t|. So t ↦ X(η_t) is Lipschitz, hence continuous.

3. The functional L. Define L(ω) := ∫_0^1 X(η^ω_t) dt.
   (a) The slice formula is linear in ω. So for ω, ω' and a ∈ ℝ, t ↦ η^ω_t + η^{ω'}_t is a slice family of ω + ω' and t ↦ a·η^ω_t is one of aω. By step 1, η^{ω+ω'}_t = η^ω_t + η^{ω'}_t and η^{aω}_t = a·η^ω_t.
   (b) X is linear, and the integrands are continuous (step 2), hence interval integrable. So L(ω + ω') = L(ω) + L(ω') and L(aω) = a·L(ω): L is ℝ-linear.

4. Bound. Let c > 0 with |ω(y)| ≤ c for all y. By slice_forms (A2)(i), |η^ω_t(x)| ≤ |ω(ι(t, x))| ≤ c for all t, x. So |X(η^ω_t)| ≤ c·M^ℝ by abs_le_mass, and |L(ω)| ≤ c·M^ℝ·|1 − 0| = c·M^ℝ (intervalIntegral.norm_integral_le_of_norm_le_const).

5. The current, and (c). By bounded_current (P = N+1, n = k+1, U = univ, A = M^ℝ) and step 4, there is Y ∈ 𝒟_{k+1}(ℝ^{N+1}) with Y(ω) = L(ω) for all ω. If η is any slice family of ω, then η = η^ω (step 1), so Y(ω) = ∫_0^1 X(η_t) dt, and t ↦ X(η_t) is continuous (step 2). This is (c).

6. Mass, (a). M(Y) = M_univ(Y) is the supremum of ofReal(Y(ω)) over ω ∈ 𝒟^{k+1}(ℝ^{N+1}) with tsupport ω ⊆ univ and |ω(y)| ≤ 1 for all y. For such ω, step 4 with c = 1 gives Y(ω) = L(ω) ≤ |L(ω)| ≤ M^ℝ. So ofReal(Y(ω)) ≤ ofReal(M^ℝ) = M(X), since M(X) < ∞. Taking the supremum (sSup_le), M(Y) ≤ M(X).

7. Support, (b). Assume spt X is compact and let E := {ι(t, x) : t ∈ [0, 1], x ∈ spt X}.
   (a) E is the image of the compact set [0, 1] × spt X under the continuous map (t, x) ↦ ι(t, x) (coordinates t, x_1, …, x_N), so E is compact.
   (b) Let ω ∈ 𝒟^{k+1}(ℝ^{N+1}) with tsupport ω ∩ E = ∅, and t ∈ [0, 1]. By slice_forms (A2)(iii), tsupport η^ω_t ⊆ {x : ι(t, x) ∈ tsupport ω}. If some x ∈ tsupport η^ω_t also lay in spt X, then ι(t, x) ∈ tsupport ω ∩ E = ∅, which is impossible.
   (c) So tsupport η^ω_t is disjoint from spt X, and X(η^ω_t) = 0 by (VO) (P = N, n = k, U = univ, S = X).
   (d) The integrand vanishes on [0, 1] = uIcc 0 1, so Y(ω) = L(ω) = ∫_0^1 0 dt = 0 (intervalIntegral.integral_congr).
   (e) By support_vanish (U = univ open, K = E compact ⊆ univ), spt Y ⊆ E and spt Y is compact. ∎

## Key steps

1. Slice families exist (slice_forms (A1)) and are unique; t ↦ X(η_t) is Lipschitz by (A2)(ii) and abs_le_mass.
2. L(ω) := ∫_0^1 X(η^ω_t) dt is linear, and |L(ω)| ≤ c·M(X) whenever |ω| ≤ c ((A2)(i) and abs_le_mass).
3. bounded_current turns L into a current Y; testing admissible forms gives M(Y) ≤ M(X).
4. Forms missing E = ι([0, 1] × spt X) have slices missing spt X, so (VO) kills the integrand and support_vanish gives a compact spt Y ⊆ E.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (project_commit b4d606db, mathlib_commit 25730c7c); cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean (identical)`
- `python3 scan of /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json accepted lean_statements for the patterns '|X ω| ≤', '→ₗ[ℝ] ℝ', '.support ⊆', 'mass.toReal', '(A - B).mass', 'covectorEuclideanNorm ((' -> cmc_fc_sc_abs_le_mul_mass, cmc_fc_sc_current_of_coeff_bound, cmc_fc_cs_massOn_sub_le, rsd_cmr_support_subset_of_vanish, cbrld_cone_testForm_coeff_lipschitz, regcomp_covectorEuclideanNorm_seminorm_retract (status accepted, candidate commits, byte-identical lean_statement)`
- `grep -rn "dimred_mbl_dt_lpc" /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT --include=*.lean (no match); python3 lookup of the four new lean_names in dag.json (no node)`
- `python3 dump of dag.json nodes cmcdt_lpo_cylinder, cmcdt_lpo_slice_forms, cmcdt_lpo_current_toolkit (twin branch, status decomposing, different types: not reusable) and of the parent decomposition /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-a2fdfc1c6f/decomposition-v1.json`
- `grep -n 'def |theorem ' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,CurrentLocalEquality,Forms,AffineCurrentPushforward,Product,ParametricCurrentContinuity,FormSupNorm,GeometricPointProduct}.lean (GeometricCurrentOn, TestFormOnConverges, exteriorDerivativeTestOn, GeometricCurrentOn.boundary_apply, GeometricCurrentOn.ext, covectorEuclideanNorm, massAdmissibleOn, massOn, mass, massOn_mono, le_massOn, support, zeroRegion, exteriorDerivative_apply, affinePullbackForm, affinePullbackForm_isTestForm; no product with [[0,1]] beyond the point product)`
- `grep in pinned Mathlib: ContinuousAlternatingMap.curryLeft, curryLeftLI, curryLeft_apply_apply (Analysis/Normed/Module/Alternating/Curry.lean); compContinuousLinearMapCLM (Topology/Algebra/Module/Alternating/Topology.lean); fderiv_continuousAlternatingMap_apply_const (Analysis/Calculus/FDeriv/CompCLM.lean); ContinuousLinearMap.flipAlternating_apply_apply (Analysis/Normed/Module/Alternating/Basic.lean); extDeriv_apply (Analysis/Calculus/DifferentialForm/Basic.lean); Fin.cons_comp_succ_succAbove, Fin.removeNth_zero (Data/Fin/Tuple/Basic.lean); Isometry.isClosedEmbedding; Topology.IsClosedEmbedding.isProperMap; integral_integral_swap; AEStronglyMeasurable.comp_snd; Continuous.comp_aestronglyMeasurable₂; Integrable.of_bound; intervalIntegral.integral_eq_sub_of_hasDerivAt; Continuous.bounded_above_of_compact_support`
- `lake env lean /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dt_lpc_cylinder_decomposition/Types.lean, Assembly.lean, CheckD.lean, CheckS.lean, CheckF.lean, CheckC.lean (Lean toolchain lean-4.35.0-rc3-linux)`
- `python3 -I run of validate_lean_statement from /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py and /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py on all ten types`
- `grep of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_existing_lean_name_problem, _accepted_checkpoint, _overlay_accepted_children) and /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py (contract_scope, child_modules)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-ef7d79293b/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-a2fdfc1c6f/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-a2fdfc1c6f/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Product.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/ParametricCurrentContinuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Maps/Proper/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dt_lpc_cylinder_decomposition/Types.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dt_lpc_cylinder_decomposition/Assembly.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dt_lpc_cylinder_decomposition/CheckD.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dt_lpc_cylinder_decomposition/CheckS.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dt_lpc_cylinder_decomposition/CheckF.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dt_lpc_cylinder_decomposition/CheckC.lean`

Pins match: project b4d606db and Mathlib 25730c7c, and the workspace Submission is byte-identical to the frozen Ch07 contract. Neither the snapshot project, SimonGMT nor Mathlib contains the product [[0,1]] × X, its slice forms, the slice exterior-derivative identity, or a fundamental theorem of calculus under a current. SimonGMT supplies the affine pull-back of test forms (affinePullbackForm_isTestForm). Mathlib supplies curryLeft/curryLeftLI, compContinuousLinearMapCLM, extDeriv_apply, derivatives of evaluations, Fubini and FTC. Six needed toolkit facts already exist as accepted DAG declarations with exactly the required types, and are reused verbatim: cmc_fc_sc_abs_le_mul_mass, cmc_fc_sc_current_of_coeff_bound, cmc_fc_cs_massOn_sub_le, rsd_cmr_support_subset_of_vanish, cbrld_cone_testForm_coeff_lipschitz and regcomp_covectorEuclideanNorm_seminorm_retract. The four new obligations get fresh, unused names dimred_mbl_dt_lpc_*. All ten types elaborate in the challenge scope and pass both validators. A Lean assembly derives the exact selected type from the children plus the covector-bounds dependency. Each new child was proved in Lean from its declared siblings. Every check used only propext, Classical.choice and Quot.sound.
