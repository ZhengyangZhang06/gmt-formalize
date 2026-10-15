# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_dense-a1.constant_multiplicity_reduction-a1.imrep_current-a1`
- Child DAG node: `root.regular_set_dense-a1.constant_multiplicity_reduction-a1.imrep_current-a1.action_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the estimate in step 5 of the supplied proof of the selected theorem (parent proof, step 6(c): |E(ω)| ≤ sup_x ‖ω(x)‖·∫_{M∩K} θ dHⁿ, because |⟨α, ξ⟩| ≤ ‖α‖ Hⁿ-a.e.; Simon Ch. 6, Definition 3.1, chapter-06.txt lines 733–746). Notation: μ := Hⁿ⌞M = μHE[n].restrict R.carrier; f := ω regarded as the ambient form ℝ^P → Λⁿ(ℝ^P); g(x) := θ(x)·ξ(x)(f(x)); I_K := (∫⁻_{M∩K} θ dHⁿ).toReal. By the definition IMRep.action, R.action ω = ∫_M g dHⁿ = ∫ g dμ. Λⁿ and Λ_n = (Λⁿ)* carry operator norms, so |L(α)| ≤ ‖L‖·‖α‖ (ContinuousLinearMap.le_opNorm).

1. Preliminaries. K is compact, hence closed (IsCompact.isClosed) and Borel. By the field locallyIntegrable_mult of R applied to the compact K ⊆ U, ∫⁻_{M∩K} θ dHⁿ < ∞. The map x ↦ (θ(x) : ℝ) is measurable (θ is measurable and ℕ → ℝ is measurable) and nonnegative.

2. The function h := 1_K·θ. Let h(x) = (θ(x) : ℝ) for x ∈ K and h(x) = 0 otherwise. Since K is Borel, μ⌞K = (Hⁿ⌞M)⌞K = Hⁿ⌞(M ∩ K) (Measure.restrict_restrict and K ∩ M = M ∩ K).
(a) Integrability: h is μ-integrable iff θ is integrable for μ⌞K = Hⁿ⌞(M ∩ K) (integrable_indicator_iff). θ is measurable and nonnegative, so this holds as soon as ∫⁻ ofReal(θ) d(Hⁿ⌞(M ∩ K)) < ∞ (hasFiniteIntegral_iff_ofReal); since ofReal of a natural number m is m (ENNReal.ofReal_natCast), this lower integral equals ∫⁻_{M∩K} θ dHⁿ < ∞ (step 1).
(b) Value: ∫ h dμ = ∫_K θ dμ (integral_indicator, K Borel) = ∫ θ d(Hⁿ⌞(M ∩ K)) = (∫⁻ ofReal(θ) d(Hⁿ⌞(M ∩ K))).toReal (integral_eq_lintegral_of_nonneg_ae, θ ≥ 0 and measurable) = (∫⁻_{M∩K} θ dHⁿ).toReal = I_K.
Consequently ε·h is μ-integrable (Integrable.const_mul) and ∫ ε·h dμ = ε·∫ h dμ = ε·I_K (integral_const_mul).

3. Orientation bound. By the field orients of R, for μ-a.e. x there is a subspace Q with IsUnitOrientationOf (ξ(x)) Q; for every such x the sibling theorem imsupp_unit_orientation_ne_zero_norm_le_one gives ‖ξ(x)‖ ≤ 1. Hence ‖ξ(x)‖ ≤ 1 for μ-a.e. x.

4. Pointwise bound. Let x lie in the full-μ-measure set of step 3.
- If x ∈ K, then |g(x)| = θ(x)·|ξ(x)(f(x))| ≤ θ(x)·‖ξ(x)‖·‖f(x)‖ ≤ θ(x)·(1·ε) = ε·h(x), using θ(x) ≥ 0, ‖ξ(x)‖ ≤ 1, 0 ≤ ‖f(x)‖ and the hypothesis ‖f(x)‖ ≤ ε.
- If x ∉ K, then x ∉ tsupport f because tsupport f ⊆ K, so f(x) = 0 (image_eq_zero_of_notMem_tsupport) and g(x) = θ(x)·ξ(x)(0) = 0 = ε·h(x).
Hence |g(x)| ≤ ε·h(x) for μ-a.e. x.

5. Integral estimate. The bound ε·h is μ-integrable (step 2), so the norm estimate for Bochner integrals (norm_integral_le_of_norm_le, which requires integrability of the bound only, not of g) and step 4 give |∫ g dμ| ≤ ∫ ε·h dμ = ε·I_K.

6. Conclusion. Since R.action ω = ∫ g dμ, we get |R.action ω| ≤ ε·(∫⁻_{M∩K} θ dHⁿ).toReal. (No sign condition on ε is needed: every step above is valid for any real ε satisfying the hypothesis.) ∎

## Key steps

1. K compact ⊆ U is Borel and ∫⁻_{M∩K} θ dHⁿ < ∞ (locallyIntegrable_mult).
2. h = 1_K·θ is Hⁿ⌞M-integrable with ∫ h d(Hⁿ⌞M) = (∫⁻_{M∩K} θ dHⁿ).toReal (restrict_restrict, integral_indicator, integral_eq_lintegral_of_nonneg_ae).
3. ‖ξ(x)‖ ≤ 1 for Hⁿ⌞M-a.e. x (orients and the reused sibling imsupp_unit_orientation_ne_zero_norm_le_one).
4. |θ(x)·ξ(x)(ω(x))| ≤ ε·h(x) a.e., because ω = 0 off K ⊇ tsupport ω and ‖ω‖ ≤ ε.
5. norm_integral_le_of_norm_le gives |R.action ω| ≤ ∫ ε·h = ε·(∫⁻_{M∩K} θ dHⁿ).toReal.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; cat local-references/123e8435b4a2469b/manifest.json`
- `python3 over dag.json: lean_name, lean_statement and status of all 212 nodes; list of accepted declarations; collision check for rsd_cmr_ic_action_integrable and rsd_cmr_ic_action_abs_le`
- `git show 2e5d20d49a4a41f79e81db1a65e850fb919b38ba (accepted Submission.imsupp_unit_orientation_ne_zero_norm_le_one); git log --oneline b4d606d..2e5d20d; git diff --stat b4d606d 2e5d20d`
- `git show 4bd211adf80cdeb3dff58ca747a26ef9f64cdc96 (accepted dtc_point_current: GeometricCurrentOn construction and iteratedFDeriv ℝ 0 handling)`
- `sed simongmt Poincare/SimonGMT/Chapter06/Currents.lean and Forms.lean (testFormOnSubmodule, TestFormOnConverges, GeometricCurrentOn, IntegerRectifiableCurrentData.action docstring)`
- `rg -n 'theorem .*(clm_apply|apply_continuousLinearMap|aestronglyMeasurable_comp₂)' mathlib/Mathlib/MeasureTheory; grep -n isBoundedBilinearMap_apply Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean; grep exists_bound_of_continuous, integrable_indicator_iff, hasFiniteIntegral_iff_ofReal, Integrable.mono', norm_integral_le_of_norm_le`
- `#check norm_integral_le_of_norm_le, norm_iteratedFDeriv_zero, integral_indicator, Measure.restrict_restrict, integral_eq_lintegral_of_nonneg_ae, ContinuousAlternatingMap.le_opNorm, integral_add, integral_const_mul, Metric.tendstoUniformlyOn_iff`
- `lake env lean /tmp/rsd-cmr-ic-decomp/{Elab,Assembly,Children,Full,Full2,Iface}.lean and /tmp/rsd-cmr-ic-decomp/gen/{GenIface,GenFull}.lean with #print axioms`
- `python3 over nodes/*/decomposition-v*.json (integrability children in other branches; accepted-reuse precedent in root-density-and-tangent-cones-a1-im-sub-a1/decomposition-v3.json)`
- `sed /runtime/flows/gmt-claude-07a3972eec1d/_recursive_lean/runtime.py (_solve_children, _existing_lean_name_problem, _install_parent_supplied_child_handoff, _accepted_checkpoint, accepted-child overlay) and store.py (ensure); issue-workers.json, issue-claims/22ac3a995036b376/1170.json, swarm-configs/9ee872b1d99941cea888bdafaaee4bf9.json`
- `grep -n '3.1 Definition' book/chapter-06.txt (lines 733-746)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1-imrep-current-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-support-eq-measure-sup-2d6f974584/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-im-sub-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/9ee872b1d99941cea888bdafaaee4bf9.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/HasFiniteIntegral.lean`
- `/runtime/flows/gmt-claude-07a3972eec1d/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-07a3972eec1d/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/rsd-cmr-ic-decomp/gen/GenIface.lean`
- `/tmp/rsd-cmr-ic-decomp/gen/GenFull.lean`
- `/tmp/rsd-cmr-ic-decomp/gen/subproblems.json`

Snapshot and contract:
- The snapshot (project b4d606d, Mathlib 25730c7c) contract is byte-identical to the workspace Contract.lean and Submission.lean.
- The pinned SimonGMT library does not prove that an integer multiplicity triple defines a current. Currents.lean says the integral continuity estimate is still missing.

Accepted declaration reused:
- Exactly one accepted DAG declaration has the needed type: imsupp_unit_orientation_ne_zero_norm_le_one (candidate 2e5d20d, operator-norm bound ‖ξ‖ ≤ 1). It is reused at its identical type.
- Its candidate history over b4d606d is one handoff commit plus a 44-line theorem insertion.
- rsdic_imrep_action_int_combination is linear in the representation, not in ω, so it does not give linearity.
- dor_ims_unitOrientation_dual and covectorEuclideanNorm_gram_bounds use the Euclidean coefficient norm, not the operator norm that test-form convergence controls.

New children:
- The integrability type is unaccepted in three other branches, so it gets the fresh name rsd_cmr_ic_action_integrable. The estimate gets rsd_cmr_ic_action_abs_le. Neither name occurs in the 212 DAG nodes.
- Mathlib tools used in the compiled child proofs: HasCompactSupport.exists_bound_of_continuous, integrable_indicator_iff, Measure.restrict_restrict, hasFiniteIntegral_iff_ofReal, ENNReal.ofReal_natCast, isBoundedBilinearMap_apply with Continuous.comp_aestronglyMeasurable and AEStronglyMeasurable.prodMk, Integrable.mono', norm_integral_le_of_norm_le, integral_indicator, integral_eq_lintegral_of_nonneg_ae.
- Lean instance caveat: IMRep.aestronglyMeasurable_orient uses ContinuousLinearMap.topologicalSpace, so ContinuousLinearMap.aestronglyMeasurable_comp₂ does not unify; the bounded-bilinear evaluation route works.

Lean checks:
- The parent assembly (norm_iteratedFDeriv_zero, Metric.tendstoUniformlyOn_iff, integral_add, integral_const_mul) compiles against the exact frozen child types.
- The full chain compiles with only propext, Classical.choice and Quot.sound.
- The worker's max_nodes = 1000 leaves room for the 2 new nodes.
