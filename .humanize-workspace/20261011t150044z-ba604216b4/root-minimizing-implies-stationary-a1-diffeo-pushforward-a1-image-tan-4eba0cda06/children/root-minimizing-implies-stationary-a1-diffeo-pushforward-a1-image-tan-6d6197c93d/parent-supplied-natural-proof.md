# Parent-supplied natural-language proof

- Parent DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.image_tangent_transport-a1`
- Child DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.image_tangent_transport-a1.ae_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 of the parent proof (H^n(F_i(N_i)) ≤ L_i^n λ(N_i) = 0 and the inclusion of the exceptional set in Z ∪ ⋃_i F_i(N_i)), stated for an arbitrary property p; details filled in. λ := volume (Lebesgue measure) on ℝ^n.
1. Exceptional parameters. Fix i and put N_i := {b ∈ B_i : p(F_i b) fails}. From ∀ᵐ b ∂(λ⌞B_i), p(F_i b) we get ∀ᵐ b ∂λ, (b ∈ B_i → p(F_i b)) (ae_imp_of_ae_restrict; no measurability of B_i or of p is needed: take a measurable λ⌞B_i-null set T ⊇ {b : ¬p(F_i b)}; then λ(T ∩ B_i) = (λ⌞B_i)(T) = 0 and the exceptional set is contained in T ∩ B_i). By ae_iff this says λ({b : ¬(b ∈ B_i → p(F_i b))}) = 0. Every b ∈ N_i lies in that set, so λ(N_i) = 0 (measure_mono_null).
2. Null images. Let L_i be a Lipschitz constant of F_i. On ℝ^n, μHE[n] = λ (EuclideanSpace.euclideanHausdorffMeasure_eq_volume), so μHE[n](N_i) = 0. By definition μHE[n] = c·μH[n] with c := addHaarScalarFactor(λ, μH[n]) (Measure.euclideanHausdorffMeasure_def; the same constant c is used on ℝ^n and on ℝ^P), and c ≠ 0 (Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero). Hence μH[n](N_i) = 0. By LipschitzWith.hausdorffMeasure_image_le (exponent n ≥ 0), μH[n](F_i(N_i)) ≤ L_i^n μH[n](N_i) = 0, so μHE[n](F_i(N_i)) = c·0 = 0.
3. Covering the exceptional set. Let x ∈ M with p(x) false. If x ∉ ⋃_i F_i(B_i), then x ∈ M ∖ ⋃_i F_i(B_i). Otherwise x = F_i(b) for some i and some b ∈ B_i; then p(F_i b) fails, so b ∈ N_i and x ∈ F_i(N_i). Hence {x : ¬(x ∈ M → p(x))} = {x ∈ M : ¬p(x)} ⊆ (M ∖ ⋃_i F_i(B_i)) ∪ ⋃_i F_i(N_i).
4. The right-hand side of step 3 is μHE[n]-null: the first set by hypothesis, each F_i(N_i) by step 2, and a countable union and a finite union of null sets are null (measure_iUnion_null, measure_union_null). By monotonicity μHE[n]({x : ¬(x ∈ M → p(x))}) = 0, i.e. ∀ᵐ x ∂μHE[n], x ∈ M → p(x).
5. Since M is Borel, ∀ᵐ x ∂(μHE[n]⌞M), p(x) is equivalent to ∀ᵐ x ∂μHE[n], x ∈ M → p(x) (ae_restrict_iff'), which is step 4. The argument is uniform in n ≥ 0 and P ≥ 0 (for n = 0, λ on ℝ^0 is the unit point mass, so λ-null sets are empty, and μHE[0] = μH[0]).

## Key steps

1. From the restricted a.e. hypothesis, N_i = {b ∈ B_i : ¬p(F_i b)} is Lebesgue-null (ae_imp_of_ae_restrict, ae_iff).
2. μHE[n] = λ on ℝ^n and μHE[n] = c·μH[n] with c ≠ 0, so the Lipschitz Hausdorff bound gives μHE[n](F_i(N_i)) = 0.
3. Every x ∈ M where p fails lies in (M ∖ ⋃_i F_i(B_i)) ∪ ⋃_i F_i(N_i), a countable union of μHE[n]-null sets.
4. M is Borel, so ae_restrict_iff' converts this into ∀ᵐ x ∂(μHE[n]⌞M), p x.

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
