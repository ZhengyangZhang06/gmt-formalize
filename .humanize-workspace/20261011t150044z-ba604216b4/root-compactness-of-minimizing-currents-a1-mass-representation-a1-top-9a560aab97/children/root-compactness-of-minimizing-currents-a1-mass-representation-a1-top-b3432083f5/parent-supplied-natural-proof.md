# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.top_dim_null-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.top_dim_null-a1.directional_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, steps 1–2 (directional estimate), with the derivative, measurability and integrability details written out.
Notation: for y ∈ ℝⁿ, Da(y) := fderiv ℝ a y, a continuous linear functional on ℝⁿ; for g : ℝⁿ → ℝⁿ, div g(y) := LinearMap.trace ℝ (Euclid n) (fderiv ℝ g y). Fix a C^∞ function a : ℝⁿ → ℝ with compact support and |a| ≤ 1, and fix z ∈ ℝⁿ.
1. (Regularity of a.) The smoothness order ∞ is nonzero, so a is differentiable everywhere (ContDiff.differentiable) and Da : ℝⁿ → L(ℝⁿ, ℝ) is continuous (ContDiff.continuous_fderiv). Since a has compact support, so does Da (HasCompactSupport.fderiv). A continuous function with compact support is bounded (Continuous.bounded_above_of_compact_support), so there is M with ‖Da(y)‖ ≤ M for all y.
2. (Case z = 0.) Then a(q x + z) − a(q x) = 0 for every x, so the integral is 0 and |0| = 0 = Λ·‖0‖. From now on assume z ≠ 0 and put w := ‖z‖⁻¹•z. Then ‖w‖ = 1 and z = ‖z‖•w.
3. (Admissible fields.) Fix s ∈ ℝ and define g_s : ℝⁿ → ℝⁿ by g_s(y) := a(y + s•z)•w.
 (a) g_s is C^∞. The map y ↦ y + s•z is C^∞ and a is C^∞, so y ↦ a(y + s•z) is C^∞ (ContDiff.comp). Multiplying a C^∞ real function by the fixed vector w gives a C^∞ map (ContDiff.smul with contDiff_const).
 (b) g_s has compact support. y ↦ a(y + s•z) equals a ∘ τ for the homeomorphism τ = Homeomorph.addRight (s•z), so it has compact support (HasCompactSupport.comp_homeomorph). Multiplying by the constant function w preserves this (HasCompactSupport.smul_right).
 (c) ‖g_s(y)‖ = |a(y + s•z)|·‖w‖ = |a(y + s•z)| ≤ 1 for every y.
 (d) By the chain rule for a translation (hasFDerivAt_comp_add_right), y ↦ a(y + s•z) has derivative Da(y + s•z) at y. By HasFDerivAt.smul_const, g_s has derivative Da(y + s•z).smulRight w at y, which is the linear map v ↦ Da(y + s•z)(v)•w. Hence fderiv ℝ g_s y = Da(y + s•z).smulRight w (HasFDerivAt.fderiv). Its underlying linear map is the rank-one map v ↦ ℓ(v)•w with ℓ = Da(y + s•z) (ContinuousLinearMap.coe_smulRight), and the trace of such a map is ℓ(w) (LinearMap.trace_smulRight). Hence div g_s(y) = Da(y + s•z)(w).
 (e) Apply the hypothesis to g = g_s and use (d) at y = q x. For every s ∈ ℝ,
   |∫ h(x)·Da(q x + s•z)(w) dν(x)| ≤ Λ.   (∗)
4. (Fundamental theorem of calculus.) Fix x ∈ X and let φ(s) := a(q x + s•z). The curve s ↦ q x + s•z has derivative z at every s. By the chain rule (HasFDerivAt.comp_hasDerivAt), φ has derivative Da(q x + s•z)(z) at every s ∈ ℝ. The map s ↦ Da(q x + s•z)(z) is continuous, since Da is continuous and evaluation at z is continuous. Hence it is interval integrable on [0, 1]. By intervalIntegral.integral_eq_sub_of_hasDerivAt,
   a(q x + z) − a(q x) = φ(1) − φ(0) = ∫_0^1 Da(q x + s•z)(z) ds.
 Multiplying by the constant h(x) (intervalIntegral.integral_const_mul) gives h(x)·(a(q x + z) − a(q x)) = ∫_0^1 h(x)·Da(q x + s•z)(z) ds.
5. (Fubini.) Let μ₁ be Lebesgue measure on ℝ restricted to uIoc 0 1 = Ioc 0 1. It is a finite measure (Real.isFiniteMeasure_restrict_Ioc), and ∫_0^1 f(s) ds = ∫ f dμ₁. Since ν is finite, it is s-finite. Define G(s, x) := h(x)·Da(q x + s•z)(z) on ℝ × X, with the product measure μ₁ ⊗ ν.
 (a) G is AE-strongly measurable for μ₁ ⊗ ν. First, (s, x) ↦ h(x) is AE-strongly measurable because h is AE-strongly measurable for ν (AEStronglyMeasurable.comp_snd). Second, (s, x) ↦ Da(q x + s•z)(z) is the continuous map (s, y) ↦ Da(y + s•z)(z) composed with the measurable map (s, x) ↦ (s, q x), so it is measurable. The product of the two is AE-strongly measurable.
 (b) |G(s, x)| ≤ |h(x)|·‖Da(q x + s•z)‖·‖z‖ ≤ M‖z‖·|h(x)|, by ContinuousLinearMap.le_opNorm and step 1. The map (s, x) ↦ M‖z‖·|h(x)| is μ₁ ⊗ ν-integrable, since |h| ∈ L¹(ν) and μ₁ is finite (Integrable.comp_snd, Integrable.const_mul). Hence G ∈ L¹(μ₁ ⊗ ν) (Integrable.mono').
 (c) Combine step 4 with Fubini for interval integrals (intervalIntegral_integral_swap, applied to G):
   ∫ h(x)(a(q x + z) − a(q x)) dν(x) = ∫ (∫_0^1 G(s, x) ds) dν(x) = ∫_0^1 Φ(s) ds,
 where Φ(s) := ∫ h(x)·Da(q x + s•z)(z) dν(x). (Equivalently, use integral_integral_swap on ν ⊗ μ₁ together with intervalIntegral.integral_of_le.)
6. (Bound.) Each Da(p) is linear and z = ‖z‖•w, so Da(p)(z) = ‖z‖·Da(p)(w). Hence Φ(s) = ‖z‖·∫ h(x)·Da(q x + s•z)(w) dν(x) (integral_const_mul). By (∗), |Φ(s)| ≤ ‖z‖·Λ = Λ‖z‖ for every s ∈ ℝ. By intervalIntegral.norm_integral_le_of_norm_le_const, |∫_0^1 Φ(s) ds| ≤ Λ‖z‖·|1 − 0| = Λ‖z‖. By step 5(c), this is the claim |∫ h(x)(a(q x + z) − a(q x)) dν(x)| ≤ Λ‖z‖.

## Key steps

1. Da is continuous with compact support, so ‖Da‖ ≤ M. The case z = 0 is trivial; otherwise put w := z/‖z‖.
2. g_s(y) := a(y + s•z)•w is C^∞, compactly supported and has ‖g_s‖ ≤ 1. Its divergence is div g_s(y) = Da(y + s•z)(w) (trace of a rank-one map), so |∫ h(x)·Da(q x + s•z)(w) dν| ≤ Λ for every s.
3. FTC: h(x)(a(q x + z) − a(q x)) = ∫_0^1 h(x)·Da(q x + s•z)(z) ds.
4. Fubini on Leb|(0,1] ⊗ ν with integrable majorant M‖z‖|h(x)| gives ∫ h(a(q+z) − a(q)) dν = ∫_0^1 Φ(s) ds, where Φ(s) = ∫ h(x)·Da(q x + s•z)(z) dν.
5. Da(·)(z) = ‖z‖·Da(·)(w) gives |Φ(s)| ≤ Λ‖z‖, and the constant bound on [0, 1] gives the claim.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical); git -C lake-packages-25730c7c/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d, matches manifest)`
- `rg -n 'lemma trace_smulRight|theorem integral_integral_swap|lemma intervalIntegral_integral_swap|theorem integral_eq_sub_of_hasDerivAt|theorem integral_mul_left_eq_self|structure ContDiffBump|theorem zero_of_le_dist|theorem one_of_mem_closedBall|theorem exists_contDiff_support_eq_eq_one_iff|theorem tendsto_measure_cthickening_of_isCompact|theorem closure_eq_iInter_cthickening|theorem tendsto_integral_of_dominated_convergence|theorem Integrable.mul_prod|theorem Integrable.integral_prod_left|theorem Integrable.prod_right_ae|lemma Integrable.comp_snd|theorem hasFDerivAt_comp_add_right|instance isFiniteMeasure_restrict_Ioc|theorem eLpNorm_le_eLpNorm_fderiv_one' local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean'`
- `lake env lean /tmp/tdn2/Scope.lean (#check of the cited lemmas and #synth HasContDiffBump (Euclid 3) after import GMT.Ch07.Submission in the replayed contract scope; eLpNorm_le_eLpNorm_fderiv_one reports unknown identifier)`
- `lake env lean /tmp/tdn2/Stmts.lean (four child types + frozen parent type; instance checks IsAddHaarMeasure, SFinite, IsAddLeftInvariant, IsAddRightInvariant, IsFiniteMeasureOnCompacts, IsOpenPosMeasure, BorelSpace, ProperSpace, HasContDiffBump on Euclid n; (⊤ : ℕ∞) coerces to smooth order ∞ ≠ ω; ∫ y, a y and volume K are volume on Euclid n by rfl)`
- `lake env lean /tmp/tdn2/Assembly.lean (parent_from_children, D_from_C, #print axioms)`
- `lake env lean /tmp/tdn2/A/A.lean /tmp/tdn2/B/B.lean /tmp/tdn2/C/C.lean /tmp/tdn2/C/S.lean /tmp/tdn2/E2E/EndToEnd.lean /tmp/tdn2/final/Recheck.lean (#print axioms)`
- `python3 scan of dag.json lean_name for cmr_tdn_directional_bound, cmr_tdn_ball_average_bound, cmr_tdn_null_set_cutoffs, cmr_tdn_null_of_average_bound (no hits among 739 nodes); grep -rn cmr_tdn GMT/ local-references/123e8435b4a2469b/project lake-packages-25730c7c/simongmt lake-packages-25730c7c/mathlib/Mathlib (no match)`
- `sed -n 1388,1552p and 1801,1920p /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py; grep -n 'def _existing_lean_name_problem' -A 40 runtime.py; sed -n 545,612p verifier/gmt-compare.py (child scope replay); read this node's decomposition-v1.json, decomposition-audit-v1.json, decomposition-review-receipt-v1.json, decomposition-scope-v1.json and its dag.json entry (status decomposing, attempt 2, children [])`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-top-9a560aab97/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-top-9a560aab97/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-top-9a560aab97/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/tdn2/Scope.lean`
- `/tmp/tdn2/Stmts.lean`
- `/tmp/tdn2/Assembly.lean`
- `/tmp/tdn2/A/A.lean`
- `/tmp/tdn2/B/B.lean`
- `/tmp/tdn2/C/C.lean`
- `/tmp/tdn2/C/S.lean`
- `/tmp/tdn2/E2E/EndToEnd.lean`
- `/tmp/tdn2/final/Recheck.lean`

Pinned sources. The manifest pins project b4d606db and mathlib 25730c7c, and the active lake mathlib is at 25730c7c. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

Import closure. Every lemma cited by the child proofs is in the import closure of GMT.Ch07.Submission, for example:
- trace_smulRight (LinearAlgebra/Trace.lean:272);
- integral_integral_swap and intervalIntegral_integral_swap (Integral/Prod.lean:478 and :483);
- integral_eq_sub_of_hasDerivAt (IntervalIntegral/FundThmCalculus.lean:1148);
- ContDiffBump with one_of_mem_closedBall and zero_of_le_dist (BumpFunction/Basic.lean:70, :137, :163);
- exists_contDiff_support_eq_eq_one_iff (Geometry/Manifold/PartitionOfUnity.lean:789);
- tendsto_measure_cthickening_of_isCompact (BorelSpace/Metric.lean:185);
- closure_eq_iInter_cthickening (Thickening.lean:511);
- tendsto_integral_of_dominated_convergence (DominatedConvergence.lean:57).
The Sobolev inequality (SobolevInequality.lean:439) is not in the closure, as the handoff states.

Names. No cmr_tdn_ name exists in the 739-node DAG or in the project, SimonGMT or Mathlib sources.

Lean checks, in the comparator's replayed child scope:
- all four child types elaborate, with the relevant volume, bump and smoothness instances verified;
- complete proofs of all four children check;
- an end-to-end proof of the byte-identical frozen parent type checks with axioms [propext, Classical.choice, Quot.sound] only.

Retry context. The node's attempt-1 split had the same structure and passed audit, but its children were never activated. The DAG shows attempt 2, no children and no feedback.
