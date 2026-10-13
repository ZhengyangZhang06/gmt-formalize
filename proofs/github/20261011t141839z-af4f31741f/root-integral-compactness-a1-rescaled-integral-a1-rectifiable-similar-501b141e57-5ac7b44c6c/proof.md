# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1.rescaled_integral-a1`
- Child DAG node: `root.integral_compactness-a1.rescaled_integral-a1.rectifiable_similarity_preimage-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation. H^n := μHE[n] on ℝ^N = Euclidean N. Put σ(y) := ξ + t·y and η(x) := t^{-1}·(x − ξ). Since t ≠ 0, η(σ(y)) = y and σ(η(x)) = x. Chapter03.CountablyRectifiable n S means: there are M₀ with H^n(M₀) = 0 and maps F_j : ℝ^n → ℝ^N (j ∈ ℕ), each Lipschitz with some constant K_j ∈ ℝ≥0, such that S ⊆ M₀ ∪ ⋃_j range F_j.

1. Unpack the hypothesis for M. This gives M₀ with H^n(M₀) = 0 and maps F_j with Lipschitz constants K_j, such that M ⊆ M₀ ∪ ⋃_j range F_j.

2. η is Lipschitz with constant ‖t^{-1}‖₊.
   - For x, x' ∈ ℝ^N, η(x) − η(x') = t^{-1}·(x − x') (smul_sub, sub_sub_sub_cancel_right).
   - So dist(η x, η x') = |t^{-1}|·dist(x, x') (norm_smul), which gives the Lipschitz bound (LipschitzWith.of_dist_le_mul).
   - Hence G_j := η ∘ F_j : ℝ^n → ℝ^N is Lipschitz with constant ‖t^{-1}‖₊·K_j (LipschitzWith.comp).

3. The new exceptional set is M₀' := σ^{-1}(M₀). We show it is H^n-null.
   - First, σ^{-1}(M₀) = t^{-1}·{−ξ + x : x ∈ M₀}. If ξ + t·y ∈ M₀, then y = t^{-1}·(−ξ + (ξ + t·y)). Conversely, ξ + t·(t^{-1}·(−ξ + x)) = x.
   - The translation x ↦ −ξ + x is an isometry (isometry_add_left (−ξ)), so it preserves H^n of every set (Isometry.euclideanHausdorffMeasure_image).
   - Since t^{-1} ≠ 0, H^n(t^{-1}·X) = ‖t^{-1}‖₊^n • H^n(X) for every X (Measure.euclideanHausdorffMeasure_smul₀; write the image under x ↦ t^{-1}·x as the pointwise dilate via Set.image_smul).
   - Therefore H^n(M₀') = ‖t^{-1}‖₊^n • H^n(M₀) = ‖t^{-1}‖₊^n • 0 = 0.

4. Covering. Let y ∈ σ^{-1}(M), so σ(y) ∈ M ⊆ M₀ ∪ ⋃_j range F_j.
   - If σ(y) ∈ M₀, then y ∈ M₀'.
   - Otherwise σ(y) = F_j(v) for some j ∈ ℕ and v ∈ ℝ^n. Then G_j(v) = η(F_j(v)) = η(σ(y)) = t^{-1}·(t·y) = y (add_sub_cancel_left, smul_smul, inv_mul_cancel₀, one_smul). So y ∈ range G_j.

5. Thus σ^{-1}(M) ⊆ M₀' ∪ ⋃_j range G_j, where H^n(M₀') = 0 by step 3 and each G_j is Lipschitz by step 2. This is exactly Chapter03.CountablyRectifiable n (σ^{-1}(M)), with witnesses M₀' and (G_j)_j. ∎

## Key steps

1. Unpack M ⊆ M₀ ∪ ⋃_j F_j(ℝ^n) with H^n(M₀) = 0 and each F_j Lipschitz.
2. η(x) = t^{-1}(x − ξ) is ‖t^{-1}‖₊-Lipschitz, so each G_j := η ∘ F_j is Lipschitz.
3. σ^{-1}(M₀) = t^{-1}·(−ξ + M₀) is H^n-null by translation invariance and euclideanHausdorffMeasure_smul₀.
4. Every y ∈ σ^{-1}(M) lies in σ^{-1}(M₀) or equals G_j(v), where σ(y) = F_j(v).

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); sha256sum snapshot project/GMT/Ch08/Contract.lean vs workspace Contract.lean/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `rg/grep 'euclideanHausdorffMeasure_smul₀|euclideanHausdorffMeasure_homothety_image|Isometry.euclideanHausdorffMeasure_image|notation.*μHE' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `grep 'MeasurableEmbedding.lintegral_map|lintegral_map_equiv|MeasurableEmbedding.integrable_map_iff|integrable_smul_measure|ae_of_ae_map|absolutelyContinuous_smul|NullMeasurableSet.preimage|restrict_restrict|ae_restrict_of_ae_restrict_of_subset|setIntegral_eq_integral_of_forall_compl_eq_zero' mathlib/Mathlib/MeasureTheory`
- `grep 'comap_mulLeft_nhdsGT_zero|map_comap_of_surjective|tendsto_map'_iff|image_inter_preimage|image_smul' mathlib/Mathlib/{Topology/Algebra/Order/Field.lean,Order/Filter/Map.lean,Order/Filter/Tendsto.lean,Data/Set/Image.lean,Algebra/Group/Pointwise/Set/Scalar.lean}`
- `grep 'def CountablyRectifiable|CountablyRectifiable.mono|def blowUpMap|def HasWeightedApproximateTangentSpaceAt' simongmt Chapter03/Rectifiable.lean; grep 'structure Varifold' Chapter08/Varifold.lean`
- `grep -rn 'blowUpMap|HasWeightedApproximateTangentSpaceAt' simongmt (found Chapter04/WeightedBlowUp.lean map_inverse_blowUp_carrier, Chapter04/TangentDensity.lean hausdorff_blowUp_image / blowUp_image_inter_closedBall; #check shows they are NOT in GMT.Ch08.Submission's import closure)`
- `python dag.json scan of lean_statement/lean_name for blowUpMap/HasWeightedApproximateTangentSpaceAt/CountablyRectifiable/rescaledMeasure; grep -rl 'intcpt_ri_' run nodes + dag.json (no match)`
- `lake env lean Test/Assembly.lean (4 child stubs + comparator-form targets + parent proof, no sorry in parent); lake env lean Test/Children.lean and Test/Full.lean (#print axioms: propext, Classical.choice, Quot.sound only)`
- `python3 -I lean_contract.validate_lean_statement on all 4 lean_statements (all OK)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/QuasiMeasurePreserving.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/AbsolutelyContinuous.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Algebra/Order/Field.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Order/Filter/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Order/Filter/Tendsto.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Data/Set/Image.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Algebra/Group/Pointwise/Set/Scalar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/WeightedBlowUp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-rescaled-integral-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-rescaled-integral-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-08.txt`
- `/tmp/ri-decomp-1xT8jT/Test/Assembly.lean`
- `/tmp/ri-decomp-1xT8jT/Test/Children.lean`
- `/tmp/ri-decomp-1xT8jT/Test/Full.lean`

The snapshot is project 63436ae6 with Mathlib 25730c7c. Its Contract is byte-identical to the workspace Contract and Submission.

Every Mathlib lemma the children and the parent assembly need exists in the snapshot and is in the import closure of GMT.Ch08.Submission:
- euclideanHausdorffMeasure_smul₀ and Isometry.euclideanHausdorffMeasure_image, which hold for arbitrary sets;
- Measure.restrict_apply/map_apply/restrict_restrict;
- setIntegral_eq_integral_of_forall_compl_eq_zero, which has no integrability hypothesis;
- MeasurableEmbedding.lintegral_map/integrable_map_iff, integrable_smul_measure, absolutelyContinuous_smul, ae_of_ae_map, NullMeasurableSet.preimage;
- comap_mulLeft_nhdsGT_zero, map_comap_of_surjective, tendsto_map'_iff, image_inter_preimage, image_smul.

SimonGMT supplies CountablyRectifiable (with .mono), blowUpMap and HasWeightedApproximateTangentSpaceAt (Chapter03/Rectifiable.lean). The analogous Chapter04 blow-up scaling lemmas are not imported by Submission, so the child proofs avoid them. No accepted DAG declaration has a matching frozen type, so nothing is reused. The new intcpt_ri_* names are unreserved.

In the scratch copy:
- all 4 child types elaborate in comparator form;
- the parent assembles from them with no sorry of its own;
- full Lean proofs of all 4 children compile;
- every declaration depends only on propext, Classical.choice and Quot.sound.
