# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.slice_integrable-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.slice_integrable-a1.translate_continuous-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2–3 of the parent proof (unit orientations and dominated convergence), stated for an arbitrary continuous compactly supported j-form η in place of Φ∘ω.

Notation: μ := H^j⌞M = μHE[j].restrict R.carrier. By definition, R.action(γ) = ∫ θ(y)·ξ(y)(γ(y)) dμ(y) for every j-form γ. Put f_t(y) := θ(y)·ξ(y)(η(t + y)). The claim is that t ↦ ∫ f_t dμ is continuous.

1. (Unit orientations have norm ≤ 1.) By R.orients, μ-a.e. y has the following property (IsUnitOrientationOf): there are a subspace Q, an orthonormal family τ = (τ_1, …, τ_j) and a sign such that either ξ(y)(α) = α(τ) for all α ∈ Λ^j, or ξ(y)(α) = −α(τ) for all α. For such y and every α, |ξ(y)(α)| = |α(τ)| ≤ ‖α‖·∏_l ‖τ_l‖ = ‖α‖, by ContinuousAlternatingMap.le_opNorm and ‖τ_l‖ = 1 (orthonormality). Hence the operator norm satisfies ‖ξ(y)‖ ≤ 1 (ContinuousLinearMap.opNorm_le_bound), and |ξ(y)(β)| ≤ ‖ξ(y)‖·‖β‖ ≤ ‖β‖ for every β ∈ Λ^j. Call such y good; μ-a.e. y is good.
2. (Constants.) As η is continuous with compact support, there is C₀ with ‖η(z)‖ ≤ C₀ for all z (Continuous.bounded_above_of_compact_support); in particular C₀ ≥ ‖η(0)‖ ≥ 0. The set tsupport η is compact, hence bounded, so tsupport η ⊆ closedBall(0, r) for some r.
3. (Measurability.) Fix t.
   - y ↦ (θ(y) : ℝ) is measurable, since θ is measurable and ℕ → ℝ is measurable.
   - ξ is μ-a.e. strongly measurable (R.aestronglyMeasurable_orient).
   - y ↦ η(t + y) is continuous.
   - The evaluation map (L, β) ↦ L(β), from MultiVector P j × Λ^j to ℝ, is continuous.
   So y ↦ ξ(y)(η(t + y)) is μ-a.e. strongly measurable, being a continuous function of the a.e. strongly measurable pair (ξ(y), η(t + y)). Hence so is the product f_t.
4. (Pointwise continuity.) For each y, t ↦ f_t(y) = θ(y)·ξ(y)(η(t + y)) is continuous: t ↦ t + y and η are continuous, and ξ(y) is a continuous linear functional.
5. (A compact window.) Fix t₀ ∈ ℝ^P and let B := closedBall(0, r + ‖t₀‖ + 1), a compact Borel set. Suppose ‖t − t₀‖ < 1 and t + y ∈ tsupport η. Then ‖t + y‖ ≤ r and ‖t‖ ≤ ‖t − t₀‖ + ‖t₀‖ < ‖t₀‖ + 1. Hence ‖y‖ = ‖(t + y) − t‖ ≤ ‖t + y‖ + ‖t‖ ≤ r + ‖t₀‖ + 1, so y ∈ B.
6. (Integrable bound.) Put b(y) := C₀·1_B(y)·θ(y). The function 1_B·θ is μ-integrable:
   - it is a.e. strongly measurable, since θ is measurable and B is Borel;
   - ∫ 1_B·θ dμ = ∫_{M∩B} θ dH^j < ∞ by R.locallyIntegrable_mult, applied to the compact set B ⊆ ℝ^P (use integrable_indicator_iff and Measure.restrict_restrict).
   Hence b is μ-integrable.
7. (Domination.) Let t ∈ ball(t₀, 1) and let y be good (step 1).
   - If t + y ∈ tsupport η, then y ∈ B by step 5, and |f_t(y)| = θ(y)·|ξ(y)(η(t + y))| ≤ θ(y)·‖ξ(y)‖·‖η(t + y)‖ ≤ θ(y)·C₀ = b(y).
   - If t + y ∉ tsupport η, then η(t + y) = 0, so f_t(y) = θ(y)·ξ(y)(0) = 0 ≤ b(y), as C₀ ≥ 0 and θ ≥ 0.
   Thus |f_t| ≤ b μ-a.e. for every t in ball(t₀, 1), which is a neighbourhood of t₀.
8. (Dominated convergence.) By steps 3, 4, 6 and 7, the dominated convergence theorem for parametric integrals (Mathlib continuousAt_of_dominated) shows that t ↦ ∫ f_t dμ = R.action(y ↦ η(t + y)) is continuous at t₀.
9. Since t₀ was arbitrary, the function is continuous on ℝ^P (continuous_iff_continuousAt). ∎

## Key steps

1. μHE[j]⌞M-a.e., the unit orientation ξ(y) = ±(β ↦ β(τ)), with τ orthonormal, has operator norm ≤ 1.
2. ‖η‖ ≤ C₀ and tsupport η ⊆ closedBall(0, r). For each t the integrand f_t(y) = θ(y)ξ(y)(η(t + y)) is a.e. strongly measurable, and for each y it is continuous in t.
3. For ‖t − t₀‖ < 1 the integrand vanishes unless y ∈ B = closedBall(0, r + ‖t₀‖ + 1), and it is dominated by C₀·1_B·θ. This bound is integrable by local integrability of θ on the compact set B.
4. continuousAt_of_dominated gives continuity at every t₀, hence continuity.

## Reference use

### local-project

Queries:
- `cat manifest.json (project b4d606db1, mathlib 25730c7c); diff -q snapshot project/GMT/Ch07/Contract.lean vs workspace GMT/Ch07/Submission.lean (identical)`
- `python3 over dag.json: depth/status/depends_on of slice_integrable-a1 (depth 5; deps interior_product-a1, frame_measure-a1, both decomposing); frozen lean_statements of dimred_cs_sos_mt_interior_product and dimred_cs_sos_mt_frame_measure`
- `python3 over dag.json accepted lean_statements: patterns 'orient x α| ≤', '.action (fun', 'Continuous (fun t', 'ᗮ' with '.measure'/'.action', 'Bornology.IsBounded'+'μHE'+'span'+'≠ ∞'`
- `git show f899c748:GMT/Ch07/Submission.lean (accepted dimred_cs_ti_translate_action_hasDerivAt and unit_orientation_norm_le_one: domination via ‖R.orient‖ ≤ 1 and locallyIntegrable_mult on a closed ball)`
- `git show 4aa9ba8d:GMT/Ch07/Submission.lean | grep theorem/starProjection (accepted idtp_fons_cs_sos_product_current: monolithic, uses Submodule.starProjection_eq_self_iff / starProjection_apply_eq_zero_iff)`
- `grep -n cited_inherited inherited.py; grep -n 'max_depth|_inherited_prerequisites' runtime.py`
- `rg -n over snapshot mathlib: continuousAt_of_dominated, Measure.integrableOn_of_bounded, IntegrableOn.of_forall_sdiff_eq_zero (alias of_forall_diff_eq_zero), starProjection_eq_self_iff, starProjection_apply_eq_zero_iff, isClosed_orthogonal, withDensity_apply, abs_real_inner_le_norm, ContinuousAlternatingMap.le_opNorm, opNorm_le_bound, Continuous.bounded_above_of_compact_support, integral_eq_zero_of_ae, Bornology.IsBounded.isCompact_closure`
- `rg -n 'dimred_cs_sos_mt_si_|translate_action_continuous|span_bounded_measure' snapshot project and dag.json (no match)`
- `lake env lean /tmp/si-decomp/check/{Smoke,Assembly,Children,Elab}.lean (Lean v4.35.0-rc3)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-fff589dbdd/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-fff589dbdd/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-7f270cb1eb/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthogonal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/inherited.py`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/runtime.py`
- `/tmp/si-decomp/check/Assembly.lean`
- `/tmp/si-decomp/check/Children.lean`
- `/tmp/si-decomp/check/Elab.lean`

Pins match. The manifest records project b4d606db1 (= workspace HEAD) and mathlib 25730c7c, and the snapshot Contract.lean is byte-identical to the workspace Submission.lean.

No accepted declaration matches any child.
- No accepted node proves continuity of t ↦ R.action(η(t + ·)) or vanishing of translates under concentration on G^⊥.
- No accepted node proves finiteness of H^k on bounded subsets of a frame span.
- The closest are dimred_cs_ti_translate_action_hasDerivAt (f899c748), which only differentiates along a line, and idtp_fons_cs_sos_product_current (4aa9ba8d), which is monolithic.
- Their proofs confirm the API used here: ‖R.orient‖ ≤ 1 from IsUnitOrientationOf, locallyIntegrable_mult on closed balls, Submodule.starProjection_eq_self_iff and starProjection_apply_eq_zero_iff.

All Mathlib lemmas the child proofs need are in the snapshot at the files listed: continuousAt_of_dominated, Measure.integrableOn_of_bounded, IntegrableOn.of_forall_sdiff_eq_zero, isClosed_orthogonal, withDensity_apply, abs_real_inner_le_norm, ContinuousAlternatingMap.le_opNorm, opNorm_le_bound, Continuous.bounded_above_of_compact_support, integral_eq_zero_of_ae and Bornology.IsBounded.isCompact_closure.

The proposed names have no match in the snapshot project or dag.json. inherited.py adds frame_measure to span_bounded_finite as an inherited prerequisite, because that child's proof cites it by exact Lean name.

Lean checks (v4.35.0-rc3):
- All three child types elaborate after `import GMT.Ch07.Submission` with the contract opens.
- The frozen parent type compiles from the child stubs and the interior_product and frame_measure stubs, with no sorry of its own.
- Complete proofs of all three children compile: two use only standard axioms, and span_bounded_finite depends only on the frame_measure stub.
