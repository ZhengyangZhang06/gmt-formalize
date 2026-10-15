# Parent-supplied natural-language proof

- Parent DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.image_tangent_transport-a1`
- Child DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.image_tangent_transport-a1.composed_piece-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: first half of step 4 of the parent proof (Φ_i := φ∘F_i satisfies the hypotheses of the density lemma, and range DΦ_i(b) = Dφ(F_i b)(range DF_i(b))), with the details filled in. The parent normalises Λ ≥ 1 and uses the constant m/Λ; here m' := m/(Λ' + 1) avoids the normalisation and also covers Λ' = 0.
1. (i) For all a, a' ∈ ℝ^n, |φ(F a) − φ(F a')| ≤ Λ|F a − F a'| ≤ ΛL|a − a'|, so φ∘F is ΛL-Lipschitz (LipschitzWith.comp, which yields exactly the constant Λ * L).
2. (ii) Put m' := m/(Λ' + 1); m' > 0 because m > 0 and Λ' ≥ 0. Let a, a' ∈ B. The antilipschitz bound (AntilipschitzWith.le_mul_dist, with dist = norm of the difference) gives |F a − F a'| ≤ Λ'|φ(F a) − φ(F a')| ≤ (Λ' + 1)|φ(F a) − φ(F a')|. Hence m|a − a'| ≤ |F a − F a'| ≤ (Λ' + 1)|φ(F a) − φ(F a')|, and dividing by Λ' + 1 > 0 gives m'|a − a'| ≤ |φ(F a) − φ(F a')| = |(φ∘F)(a) − (φ∘F)(a')|.
3. (iii) Let a ∈ B. F is differentiable at a and φ is differentiable at F(a), so by the chain rule φ∘F is differentiable at a (DifferentiableAt.comp) with D(φ∘F)(a) = Dφ(F a) ∘L DF(a) (fderiv_comp). As a function this composite is Dφ(F a) ∘ DF(a) (ContinuousLinearMap.coe_comp), a composition of the injective maps DF(a) (hypothesis on B) and Dφ(F a) (hypothesis for every x), hence injective (Function.Injective.comp).
4. (iv) Let a ∈ B. By step 3 and ContinuousLinearMap.toLinearMap_comp, the linear map underlying D(φ∘F)(a) is (Dφ(F a) as a linear map) ∘ₗ (DF(a) as a linear map), and for linear maps range(g ∘ₗ f) = map g (range f) (LinearMap.range_comp). Hence range D(φ∘F)(a) = Submodule.map Dφ(F a) (range DF(a)).

## Key steps

1. Lipschitz constants multiply under composition: φ∘F is ΛL-Lipschitz.
2. The antilipschitz bound |F a − F a'| ≤ Λ'|φF a − φF a'| yields the lower constant m' = m/(Λ' + 1) > 0 on B.
3. Chain rule at a ∈ B: D(φ∘F)(a) = Dφ(F a)∘DF(a), injective as a composite of injective maps.
4. range(Dφ(F a)∘DF(a)) = Dφ(F a)(range DF(a)) by toLinearMap_comp and LinearMap.range_comp.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (project b4d606db, mathlib 25730c7c)`
- `rg -n 'approxTangentPlane' project/GMT --glob '*.lean'`
- `rg -n 'AntilipschitzWith|hausdorffMeasure_image_le|image_of_continuousOn_injOn|ae_imp_of_ae_restrict' project/GMT --glob '*.lean' (no match)`
- `rg -n 'dpf_itt|approxTangentPlane_eq|ae_of_ae_pieces|bilipschitz_image' project --glob '*.lean' (no match)`
- `rg -n 'euclideanHausdorffMeasure' mathlib/Mathlib --glob '*.lean'`
- `rg -n 'hausdorffMeasure_image_le' mathlib/Mathlib --glob '*.lean' -A6`
- `sed -n 60,240p mathlib/Mathlib/Topology/MetricSpace/Antilipschitz.lean (le_mul_dist, injective, isBounded_preimage)`
- `rg -n 'theorem MeasurableSet.image_of_continuousOn_injOn|theorem ae_imp_of_ae_restrict|theorem ae_restrict_iff|theorem measure_union_null|theorem measure_iUnion_null_iff|theorem ae_iff' mathlib/Mathlib --glob '*.lean'`
- `rg -n 'theorem toLinearMap_comp|theorem coe_comp|theorem range_comp |theorem fderiv_comp |theorem isCompact_of_isClosed_isBounded|theorem image_inter_preimage' in ContinuousLinearMap/Basic.lean, Submodule/Range.lean, FDeriv/Comp.lean, MetricSpace/Bounded.lean, Data/Set/Image.lean`
- `grep -n 'def CountablyRectifiable|def HasApproximateTangentSpaceAt|theorem HasApproximateTangentSpaceAt.unique|def blowUpMap' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `python3 -I scan of dag.json (509 nodes) and all nodes/*/decomposition-v*.json for lean names and statements matching approxTangent|Lipschitz|null|bilipschitz|antilipschitz and for dpf_* names`
- `grep -c dpf_itt dag.json DAG.md dag.mmd issue-workers.json github-workflow.json (all 0); git for-each-ref | grep image-tan; git diff --stat problems/ch07 <node branch> -- GMT (no Lean changes)`
- `python3 -I: importlib-load verifier/gmt-compare.py, contract_scope(GMT/Ch07/Contract.lean, 'GMT.Ch07.main_theorem')`
- `lake env lean /tmp/itt-decomp/Types.lean; lake env lean /tmp/itt-decomp/Assembly.lean; lake env lean /tmp/itt-decomp/Children.lean`
- `lake env lean /tmp/itt-decomp-final/Final.lean (#print axioms for the 4 children and assembly_conditional)`
- `lake env lean /tmp/itt-decomp-final2/D.lean (#check @dite_eq_left; proof via dite_eq_left)`
- `independent reviewer subagent: re-ran Final.lean, byte-compared statements with dag.json, simulated the comparator NodeSolution step, and probed the volume instance and CLM coercions in /tmp/itt-review-qtYkT3/`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Antilipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Module/Submodule/Range.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Image.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-image-tan-4eba0cda06/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-image-tan-4eba0cda06/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-tangent-projection-measurable-a1/decomposition-audit-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/itt-decomp/Types.lean`
- `/tmp/itt-decomp/Assembly.lean`
- `/tmp/itt-decomp/Children.lean`
- `/tmp/itt-decomp-final/Final.lean`
- `/tmp/itt-decomp-final2/D.lean`

The snapshot holds no proof of the selected statement or of any proposed child. In the project, approxTangentPlane appears only in its Ch07 definition (Contract/Submission line 259) and in the unrelated 4-argument Ch03 variant; no lemma relates it to HasApproximateTangentSpaceAt, and project/GMT has no antilipschitz, Hausdorff-image or a.e.-transfer lemma. The DAG has no node with a dpf_itt_ name or any of the four child types. One proposal in an accepted leaf node's decomposition (mis_tpm_approxTangentPlane_eq_of_hasApproxTangent) has the same type as chosen_tangent_plane but was never instantiated, so a new name is used.
Every library fact the child proofs cite exists in the pinned Mathlib 25730c7c or SimonGMT 2b36630 with compatible hypotheses:
- MeasurableSet.image_of_continuousOn_injOn (Polish/Basic.lean:821);
- AntilipschitzWith.injective, le_mul_dist and isBounded_preimage;
- Metric.isCompact_of_isClosed_isBounded and Set.image_inter_preimage;
- LipschitzWith.hausdorffMeasure_image_le (Hausdorff.lean:745);
- Measure.euclideanHausdorffMeasure_def, addHaarScalarFactor_volume_hausdorffMeasure_ne_zero and EuclideanSpace.euclideanHausdorffMeasure_eq_volume;
- ae_imp_of_ae_restrict (Restrict.lean:619, no measurability needed), ae_restrict_iff', measure_iUnion_null and measure_union_null;
- fderiv_comp, ContinuousLinearMap.coe_comp (function version) and toLinearMap_comp (linear-map version), LinearMap.range_comp;
- dite_eq_left (dif_pos is deprecated);
- SimonGMT HasApproximateTangentSpaceAt.unique (Rectifiable.lean:232).
All four child types elaborate in the comparator's replayed GMT.Ch07 scope. The parent's exact frozen type is proved from the two sibling types plus the four children using only propext, Classical.choice and Quot.sound, and each child was proved in scratch Lean using only those same axioms.
