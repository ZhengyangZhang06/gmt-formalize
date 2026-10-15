# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.slice_integrable-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.slice_integrable-a1.span_bounded_finite-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent proof.

Uses frame_measure (ii), the closed-box half of Submission.dimred_cs_sos_mt_frame_measure: for every r > 0, H^k({t ∈ G : |⟨g_i, t⟩| ≤ r for all i}) = ENNReal.ofReal((2r)^k).

1. Since E is bounded, E ⊆ closedBall(0, ρ) for some ρ ∈ ℝ (Bornology.IsBounded.subset_closedBall). Put r := max(ρ, 0) + 1, so that r > 0 and ρ ≤ r.
2. Let t ∈ E. Then t ∈ G, because E ⊆ G. For each i, Cauchy–Schwarz (abs_real_inner_le_norm) and ‖g_i‖ = 1 (orthonormality) give |⟨g_i, t⟩| ≤ ‖g_i‖·‖t‖ = ‖t‖ ≤ ρ ≤ r. Hence E ⊆ Box_r := {t : t ∈ G ∧ ∀ i, |⟨g_i, t⟩| ≤ r}.
3. By frame_measure (ii) with this r > 0, H^k(Box_r) = ENNReal.ofReal((2r)^k), which is finite (ENNReal.ofReal_ne_top).
4. By monotonicity of the measure (measure_mono), H^k(E) ≤ H^k(Box_r) < ∞, so μHE[k] E ≠ ∞. ∎

## Key steps

1. E ⊆ closedBall(0, ρ). With r = max(ρ, 0) + 1 > 0, Cauchy–Schwarz and ‖g_i‖ = 1 give E ⊆ {t ∈ G : |⟨g_i, t⟩| ≤ r for all i}.
2. frame_measure (ii) gives this closed box H^k-measure ENNReal.ofReal((2r)^k) < ∞; monotonicity finishes.

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
