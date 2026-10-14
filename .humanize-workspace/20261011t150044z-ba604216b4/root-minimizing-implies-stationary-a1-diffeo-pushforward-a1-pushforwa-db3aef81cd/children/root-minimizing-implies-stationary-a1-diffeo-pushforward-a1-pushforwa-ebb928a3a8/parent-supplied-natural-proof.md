# Parent-supplied natural-language proof

- Parent DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.pushforward_current-a1`
- Child DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.pushforward_current-a1.fderiv_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 of the parent proof. Simon 6.2.24(2)–(3) (chapter-06.txt lines 414–440) makes sense of f_#T for f "merely C¹ with f|spt T proper". The printed text omits this derivative estimate, so it is supplied here. Notation: E := ℝ^P (Euclid P); Dφ(x) := fderiv ℝ φ x ∈ E →L[ℝ] E; ‖·‖ is the operator norm.
1. Continuity of Dφ. φ is C¹, so x ↦ Dφ(x) is continuous (ContDiff.continuous_fderiv, using 1 ≠ 0).
2. Bound on K. K is compact and Dφ is continuous on K. So there is c ∈ ℝ with ‖Dφ(x)‖ ≤ c for all x ∈ K (IsCompact.exists_bound_of_continuousOn).
3. Choice of Λ. Put Λ := max(1, c). Then 0 ≤ 1 ≤ Λ and c ≤ Λ.
4. Points of K. If x ∈ K, then ‖Dφ(x)‖ ≤ c ≤ Λ by steps 2–3.
5. Points off K. Let x ∉ K.
   - A compact subset of the Hausdorff space E is closed (IsCompact.isClosed), so E ∖ K is open and is a neighbourhood of x.
   - By hypothesis φ(y) = y for every y ∈ E ∖ K, so φ agrees with id on a neighbourhood of x (φ =ᶠ[𝓝 x] id).
   - The derivative at x depends only on the germ at x (Filter.EventuallyEq.fderiv_eq). Hence Dφ(x) = D(id)(x) = id_E (fderiv_id).
   - Therefore ‖Dφ(x)‖ = ‖id_E‖ ≤ 1 ≤ Λ (ContinuousLinearMap.norm_id_le, step 3).
6. Conclusion. By steps 4–5, ‖Dφ(x)‖ ≤ Λ for every x ∈ E, and Λ ≥ 0 by step 3. So Λ is the required constant.

## Key steps

1. Dφ is continuous because φ is C¹.
2. Compactness of K gives c with ‖Dφ(x)‖ ≤ c on K.
3. K is closed, so φ = id near any x ∉ K; hence Dφ(x) = id and ‖Dφ(x)‖ ≤ 1.
4. Λ := max(1, c) ≥ 0 bounds ‖Dφ(x)‖ for every x.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db, mathlib 25730c7c); cmp project/GMT/Ch07/Contract.lean vs workspace GMT/Ch07/Contract.lean (identical)`
- `python3 -I over dag.json (509 nodes): lean_statements containing 'orient x' together with ≤/‖/Integrable; '‖R.orient'/IsUnitOrientationOf bounds; 'TestFormOnConverges'; '‖fderiv ℝ _ x‖ ≤'; duplicate lean_names (none)`
- `python3 -I: list all nodes under root.minimizing_implies_stationary-a1.diffeo_pushforward-a1 with lean_name/status (11 siblings, no dpf_pfc_* names)`
- `grep -l '<each of the 4 proposed names>' dag.json nodes/*/decomposition-v*.json nodes/*/parent-child-handoff.json; grep -rl dpf_pfc .humanize (no matches)`
- `rg -n 'TestFormOnConverges|compContinuousLinearMap|IsUnitOrientationOf|locallyIntegrable_mult' project/GMT --glob '*.lean'`
- `rg -n 'dpf_pfc|pairing_integrable|orient_abs|fderiv_norm_le_of_eq_id' project/GMT mathlib/Mathlib --glob '*.lean' (no match)`
- `grep -rn mathlib/Mathlib: compContinuousLinearMapCLM, continuous_compContinuousLinearMapCLM, norm_compContinuousLinearMap_le, le_opNorm, hasStrictFDerivAt_compContinuousLinearMap, Continuous.comp_aestronglyMeasurable₂, def AEStronglyMeasurable, measurable_from_nat, integrable_indicator_iff, integral_indicator, integral_eq_lintegral_of_nonneg_ae, norm_integral_le_of_norm_le, Integrable.mono'`
- `grep -rn TestFormOnConverges simongmt/Poincare/SimonGMT (definitions in Chapter06/Currents.lean; TestFormOnConverges.tendsto_eval in Chapter06/GeometricPointProduct.lean)`
- `sed -n book/chapter-06.txt lines 168-215 (6.1 test-form topology, 6.2.1-2.2), 395-445 (6.2.23-2.24), 725-760 (6.3.1)`
- `lake env lean /tmp/pfc-decomp-7f3a/Types.lean (4 child types + parent elaborate in replayed contract scope)`
- `lake env lean /tmp/pfc-decomp-7f3a/Assembly.lean (#print axioms assembly_conditional)`
- `lake env lean /tmp/pfc-decomp-7f3a/Children.lean (#print axioms childA/childD/childE/childB)`
- `lake env lean /tmp/pfc-decomp-7f3a/Final.lean (children as Submission.X in namespace GMT.Ch07, parent proved from them, comparator-style exact Submission.X checks, #print axioms NodeTarget0-4)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-pushforwa-db3aef81cd/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-pushforwa-db3aef81cd/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/GeometricPointProduct.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/pfc-decomp-7f3a/Types.lean`
- `/tmp/pfc-decomp-7f3a/Assembly.lean`
- `/tmp/pfc-decomp-7f3a/Children.lean`
- `/tmp/pfc-decomp-7f3a/Final.lean`

No declaration in the snapshot (project b4d606d, Mathlib 25730c7c) or in SimonGMT proves the selected statement or any proposed child, so the four children are new. None of the four names appears in dag.json (509 nodes), in any stored decomposition or handoff, anywhere under .humanize, in the project, in SimonGMT or in Mathlib.

Related nodes in other branches have different types and are not reused:
- unit_orientation_norm_le_one and rsd_mw_wlm_orient_opNorm_le_one: IsUnitOrientationOf ξ Q → ‖ξ‖ ≤ 1;
- regcomp_rim_action_integrable;
- lcn_mult_mul_orient_apply_integrableOn.
SimonGMT's TestFormOnConverges.tendsto_eval gives only pointwise convergence, not the uniform bound uniform_small provides.

Pinned Mathlib supplies every library fact the children use: ContDiff.continuous_fderiv, IsCompact.exists_bound_of_continuousOn, Filter.EventuallyEq.fderiv_eq, ContinuousLinearMap.norm_id_le, ContinuousAlternatingMap.le_opNorm, norm_compContinuousLinearMap_le, continuous_compContinuousLinearMapCLM, compContinuousLinearMapCLM_apply, Continuous.clm_apply, Continuous.comp_aestronglyMeasurable₂, measurable_from_nat, integrable_indicator_iff, Integrable.mono', integral_indicator, integral_eq_lintegral_of_nonneg_ae, norm_integral_le_of_norm_le, norm_iteratedFDeriv_zero and Metric.tendstoUniformlyOn_iff.

Lean checks:
- All four frozen child types and the parent type elaborate in the comparator's replayed contract scope.
- Complete proofs of the four children, and of the parent from Submission.dpf_pfc_*, compile in the Submission layout.
- Comparator-style `exact Submission.X` checks for all five declarations depend only on propext, Classical.choice and Quot.sound.
