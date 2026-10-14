# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.slice_integrable-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.slice_integrable-a1.translate_vanish-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 of the parent proof (vanishing off p(tsupport ω) under concentration), stated for an arbitrary compactly supported j-form η and an arbitrary subspace G.

Notation: H^j := μHE[j], M := R.carrier, θ := R.mult, ξ := R.orient. By definition, R.action(γ) = ∫_M θ(y)·ξ(y)(γ(y)) dH^j(y).

1. (The compact set.) Let p := G.starProjection, the orthogonal projection of ℝ^P onto G. It exists because G, a subspace of the finite-dimensional space ℝ^P, is complete (instance HasOrthogonalProjection). It is a continuous linear map with p(t) = t for t ∈ G (Submodule.starProjection_eq_self_iff) and p(y) = 0 for y ∈ G^⊥ (Submodule.starProjection_apply_eq_zero_iff). Put K := p(tsupport η). Since η has compact support, tsupport η is compact, so K is compact as a continuous image of a compact set. Fix t ∈ G with t ∉ K; we show R.action(y ↦ η(t + y)) = 0.
2. (M is H^j-almost contained in G^⊥.)
   - G^⊥ is closed (Submodule.isClosed_orthogonal), so A := ℝ^P ∖ G^⊥ is Borel.
   - By definition R.measure = (H^j⌞M).withDensity θ, so R.measure(A) = ∫_{M∩A} θ dH^j (withDensity_apply, Measure.restrict_restrict).
   - For x ∈ M, θ(x) > 0 (R.mult_pos), so θ(x) ≥ 1 since θ is ℕ-valued.
   - Since θ is measurable, setLIntegral_mono gives H^j(M ∩ A) = ∫_{M∩A} 1 dH^j ≤ ∫_{M∩A} θ dH^j = R.measure(A) = 0.
   Consequently y ∈ G^⊥ for H^j⌞M-a.e. y: the exceptional set {y : y ∉ G^⊥} = A has (H^j⌞M)-measure H^j(A ∩ M) = 0 (ae_iff, Measure.restrict_apply').
3. (The integrand vanishes on G^⊥.) Let y ∈ G^⊥ and suppose η(t + y) ≠ 0. Then t + y ∈ support η ⊆ tsupport η, and by linearity p(t + y) = p(t) + p(y) = t + 0 = t. Hence t = p(t + y) ∈ p(tsupport η) = K, contradicting t ∉ K. So η(t + y) = 0, and the integrand is θ(y)·ξ(y)(η(t + y)) = θ(y)·ξ(y)(0) = 0.
4. (Conclusion.) By steps 2 and 3, the integrand y ↦ θ(y)·ξ(y)(η(t + y)) vanishes H^j⌞M-almost everywhere. So its integral R.action(y ↦ η(t + y)) is 0 (integral_eq_zero_of_ae). As t ∈ G ∖ K was arbitrary, K has the required property. ∎

## Key steps

1. K := G.starProjection(tsupport η) is compact, as the continuous image of a compact set.
2. R.measure(ℝ^P ∖ G^⊥) = ∫_{M∖G^⊥} θ dH^j ≥ H^j(M ∖ G^⊥), since θ ≥ 1 on M. So H^j⌞M-a.e. point lies in G^⊥.
3. For t ∈ G ∖ K and y ∈ G^⊥, η(t + y) ≠ 0 would give t = p(t + y) ∈ K. So the integrand vanishes a.e. and the action is 0.

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
