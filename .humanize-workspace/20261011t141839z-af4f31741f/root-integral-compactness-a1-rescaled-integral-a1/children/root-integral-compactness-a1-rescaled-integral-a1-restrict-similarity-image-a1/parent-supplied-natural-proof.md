# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1.rescaled_integral-a1`
- Child DAG node: `root.integral_compactness-a1.rescaled_integral-a1.restrict_similarity_image-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation. H^n := μHE[n] on ℝ^N = Euclidean N. It is a Borel measure, and its value on an arbitrary set is the outer-measure value. Put σ(y) := ξ + t·y and c := ENNReal.ofReal(t^n). Fix an arbitrary set A ⊆ ℝ^N.

1. σ is continuous, being a constant plus a scalar multiple of the identity. Hence it is Borel measurable.

2. Scaling of arbitrary sets. We claim H^n(σ(S)) = c·H^n(S) for every S ⊆ ℝ^N.
   - Write σ(S) = τ(t·S), where τ(z) := ξ + z and t·S := {t·s : s ∈ S} is the pointwise dilate (Set.image_smul, Set.image_image).
   - τ is an isometry of ℝ^N (isometry_add_left ξ). So H^n(τ(X)) = H^n(X) for every X ⊆ ℝ^N (Isometry.euclideanHausdorffMeasure_image).
   - Since t ≠ 0, H^n(t·S) = ‖t‖₊^n • H^n(S) for every S (MeasureTheory.Measure.euclideanHausdorffMeasure_smul₀).
   - Since t > 0, the ℝ≥0-scalar ‖t‖₊^n acts on [0,∞] as multiplication by ENNReal.ofReal(t^n) = c (ENNReal.smul_def, ENNReal.ofReal_coe_nnreal, NNReal.coe_pow, coe_nnnorm, Real.norm_of_nonneg).
   - Therefore H^n(σ(S)) = H^n(τ(t·S)) = H^n(t·S) = c·H^n(S).

3. Evaluate both measures on a Borel set B ⊆ ℝ^N.
   - Left side: (H^n⌞σ(A))(B) = H^n(B ∩ σ(A)) by Measure.restrict_apply. This needs only B to be measurable; A is arbitrary.
   - Right side: (c • σ_#(H^n⌞A))(B) = c·(H^n⌞A)(σ^{-1}(B)), by Measure.smul_apply and Measure.map_apply (σ and B are measurable).
   - This equals c·H^n(σ^{-1}(B) ∩ A), by Measure.restrict_apply for the measurable set σ^{-1}(B).

4. Set identity: B ∩ σ(A) = σ(A) ∩ B = σ(A ∩ σ^{-1}(B)) = σ(σ^{-1}(B) ∩ A). The middle equality is Set.image_inter_preimage, which holds for every map.

5. Apply step 4, then step 2 with S := σ^{-1}(B) ∩ A: H^n(B ∩ σ(A)) = H^n(σ(σ^{-1}(B) ∩ A)) = c·H^n(σ^{-1}(B) ∩ A). By step 3, the two measures agree on every Borel set B.

6. Two measures on ℝ^N that agree on all measurable sets are equal (Measure.ext). Hence (μHE[n]).restrict (σ '' A) = ENNReal.ofReal(t^n) • ((μHE[n]).restrict A).map σ. ∎

## Key steps

1. σ = (ξ + ·) ∘ (t • ·). Translation invariance (an isometry) and euclideanHausdorffMeasure_smul₀ give H^n(σ(S)) = t^n·H^n(S) for every set S.
2. For Borel B, (H^n⌞σ(A))(B) = H^n(B ∩ σ(A)) and (t^n·σ_#(H^n⌞A))(B) = t^n·H^n(σ^{-1}(B) ∩ A).
3. Since B ∩ σ(A) = σ(σ^{-1}(B) ∩ A), the scaling identity makes the two values equal. Conclude by Measure.ext.

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
