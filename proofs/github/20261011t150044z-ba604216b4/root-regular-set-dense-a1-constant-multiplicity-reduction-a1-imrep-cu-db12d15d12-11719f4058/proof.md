# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_dense-a1.constant_multiplicity_reduction-a1.imrep_current-a1`
- Child DAG node: `root.regular_set_dense-a1.constant_multiplicity_reduction-a1.imrep_current-a1.action_integrable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1–3 of the supplied proof of the selected theorem (Simon Ch. 6, Definition 3.1, formula (‡), chapter-06.txt lines 733–746: the integrand of (‡) is integrable because |⟨ω, ξ⟩| ≤ sup‖ω‖ Hⁿ-a.e. and θ is locally Hⁿ-integrable). Notation: μ := Hⁿ⌞M = μHE[n].restrict R.carrier; f := ω regarded as the ambient form ℝ^P → Λⁿ(ℝ^P) (Covector (Euclid P) n); K_ω := tsupport f; g(x) := θ(x)·ξ(x)(f(x)), the function in the statement. Λⁿ and Λ_n = (Λⁿ)* carry operator norms, so |L(α)| ≤ ‖L‖·‖α‖ for L ∈ Λ_n and α ∈ Λⁿ (ContinuousLinearMap.le_opNorm).

1. The test form. ω ∈ TestFormOn U n means: f is C^∞, hence continuous; f has compact support, i.e. K_ω is compact; and K_ω ⊆ U. A continuous function with compact support is bounded, so there is C ∈ ℝ with ‖f(x)‖ ≤ C for every x ∈ ℝ^P (HasCompactSupport.exists_bound_of_continuous). Moreover f(x) = 0 for every x ∉ K_ω (image_eq_zero_of_notMem_tsupport). K_ω is closed (isClosed_tsupport), hence a Borel set.

2. Orientation bound. By the field orients of R, for μ-a.e. x there is a subspace Q of ℝ^P with IsUnitOrientationOf (ξ(x)) Q. For every such x, the sibling theorem imsupp_unit_orientation_ne_zero_norm_le_one applied to ξ(x) and Q gives ‖ξ(x)‖ ≤ 1. Hence ‖ξ(x)‖ ≤ 1 for μ-a.e. x.

3. The dominating function. Let h := 1_{K_ω}·θ, i.e. h(x) = (θ(x) : ℝ) for x ∈ K_ω and h(x) = 0 otherwise. The map x ↦ (θ(x) : ℝ) is measurable, being the composition of the measurable θ (field measurable_mult) with the cast ℕ → ℝ. Since K_ω is Borel, h is μ-integrable if and only if θ is integrable for the restriction μ⌞K_ω (integrable_indicator_iff), and μ⌞K_ω = (Hⁿ⌞M)⌞K_ω = Hⁿ⌞(M ∩ K_ω) (Measure.restrict_restrict, K_ω measurable, and K_ω ∩ M = M ∩ K_ω). The function θ is measurable and nonnegative, so it is integrable for Hⁿ⌞(M ∩ K_ω) as soon as ∫⁻ ofReal(θ) d(Hⁿ⌞(M ∩ K_ω)) < ∞ (hasFiniteIntegral_iff_ofReal). Because ofReal of a natural number m equals m in [0, ∞] (ENNReal.ofReal_natCast), this lower integral is ∫⁻_{M∩K_ω} θ dHⁿ, which is finite by the field locallyIntegrable_mult of R applied to the compact set K_ω ⊆ U (step 1). Hence h is μ-integrable, and so is C·h (Integrable.const_mul).

4. Measurability of g. The map x ↦ (θ(x) : ℝ) is measurable (step 3), hence a.e. strongly measurable. ξ is a.e. strongly measurable for μ (field aestronglyMeasurable_orient). f is continuous, hence a.e. strongly measurable. The evaluation map E : Λ_n × Λⁿ → ℝ, E(L, α) = L(α), is a bounded bilinear map and therefore continuous (isBoundedBilinearMap_apply). So x ↦ (ξ(x), f(x)) is a.e. strongly measurable (AEStronglyMeasurable.prodMk) and x ↦ E(ξ(x), f(x)) = ξ(x)(f(x)) is a.e. strongly measurable (Continuous.comp_aestronglyMeasurable). Hence the product g(x) = θ(x)·ξ(x)(f(x)) is a.e. strongly measurable for μ.

5. Pointwise domination. Let x lie in the full-μ-measure set of step 2, so ‖ξ(x)‖ ≤ 1.
- If x ∈ K_ω, then |g(x)| = θ(x)·|ξ(x)(f(x))| ≤ θ(x)·‖ξ(x)‖·‖f(x)‖ ≤ θ(x)·(1·C) = C·h(x), using θ(x) ≥ 0, ‖ξ(x)‖ ≤ 1 and 0 ≤ ‖f(x)‖ ≤ C.
- If x ∉ K_ω, then f(x) = 0 (step 1), so g(x) = θ(x)·ξ(x)(0) = 0 = C·h(x).
Hence |g(x)| ≤ C·h(x) for μ-a.e. x.

6. Conclusion. g is a.e. strongly measurable for μ (step 4) and |g| ≤ C·h μ-a.e. with C·h μ-integrable (steps 3 and 5). By domination (Integrable.mono') g is μ-integrable, i.e. x ↦ (R.mult x : ℝ) · R.orient x (ω x) is integrable for μHE[n].restrict R.carrier. ∎

## Key steps

1. ω is continuous with compact support K_ω = tsupport ω ⊆ U, so ‖ω(x)‖ ≤ C for all x and ω = 0 off K_ω.
2. ‖ξ(x)‖ ≤ 1 for Hⁿ⌞M-a.e. x, from the orients field and the reused sibling imsupp_unit_orientation_ne_zero_norm_le_one.
3. h = 1_{K_ω}·θ is Hⁿ⌞M-integrable: it is θ on Hⁿ⌞(M ∩ K_ω), whose lower integral ∫⁻_{M∩K_ω} θ is finite by locallyIntegrable_mult.
4. g = θ·ξ(ω) is a.e. strongly measurable: θ is measurable, ξ is a.e. strongly measurable, ω is continuous, and evaluation (L, α) ↦ L(α) is continuous.
5. |g| ≤ C·h Hⁿ⌞M-a.e., so Integrable.mono' gives integrability of g.

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
