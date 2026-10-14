# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.area_formula-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.area_formula-a1.bochner_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 7 of the parent proof ('Let μ_J := (H^m⌞B).withDensity(ofReal∘J). By step 6 with g := 1_T … H^m⌞G(B) is the image of μ_J (carried by B) under G|_B. MeasurableEmbedding.integral_map … and integral_withDensity_eq_integral_smul …; both identities hold for arbitrary f'), with general measures μ, ν in place of H^m. Notation: ι : B → ℝ^d is the inclusion of the subtype B, ρ(v) := ofReal(J(v)) = (J(v))₊ viewed in [0, ∞] (ofReal r is by definition the coercion of r.toNNReal), and ν_J := ν.withDensity ρ.

1. (Measurable embeddings.) ι is a measurable embedding because B is Borel (Mathlib MeasurableEmbedding.subtype_coe). The map e := G|_B : B → ℝ^P is a measurable embedding by the Lusin–Souslin theorem, since B is a Borel subset of the Polish space ℝ^d and G is continuous and injective on B (Mathlib ContinuousOn.measurableEmbedding).

2. (A measure on B.) Let ν′ := comap_ι ν_J, the measure on B with ν′(S) = ν_J(ι(S)) for Borel S ⊆ B (MeasurableEmbedding.comap_apply).

3. (Claim: map_e ν′ = μ⌞G(B).) Let T ⊆ ℝ^P be Borel and put S_T := B ∩ G^{-1}(T) = ι(e^{-1}(T)). Since e is measurable, e^{-1}(T) is Borel in B, so S_T is Borel in ℝ^d (ι is a measurable embedding). Then
 map_e ν′(T) = ν′(e^{-1}(T)) = ν_J(S_T) = ∫⁻_{S_T} ρ dν (Mathlib withDensity_apply).
 On the other side, μ⌞G(B)(T) = ∫⁻_{G(B)} 1_T dμ (Mathlib lintegral_indicator_one), and the hypothesis with g := 1_T gives ∫⁻_{G(B)} 1_T dμ = ∫⁻_B ρ(v) · 1_T(G(v)) dν(v). For v ∈ B, ρ(v) · 1_T(G(v)) = 1_{S_T}(v) · ρ(v), so ∫⁻_B ρ(v) · 1_T(G(v)) dν(v) = ∫⁻_B 1_{S_T} ρ dν = ∫⁻_{S_T ∩ B} ρ dν = ∫⁻_{S_T} ρ dν (S_T and B are Borel and S_T ⊆ B; Mathlib lintegral_indicator). So the two measures agree on every Borel set, hence map_e ν′ = μ⌞G(B).

4. (Transport of the Bochner integral.) Let f : ℝ^P → ℝ be arbitrary. Because e and ι are measurable embeddings, Mathlib MeasurableEmbedding.integral_map applies to arbitrary integrands (integrability and the values are transported together, non-integrable sides being 0). Hence
 ∫_{G(B)} f dμ = ∫ f d(map_e ν′) = ∫_B f(e(x)) dν′(x) = ∫_B (f ∘ G)(ι(x)) dν′(x) = ∫ (f ∘ G) d(map_ι ν′),
 and map_ι ν′ = map_ι(comap_ι ν_J) = ν_J⌞B (Mathlib map_comap_subtype_coe, B Borel). So ∫_{G(B)} f dμ = ∫_B f(G(v)) dν_J(v).

5. (Removing the density.) ν_J = ν.withDensity(v ↦ (J(v)).toNNReal) with v ↦ (J(v)).toNNReal measurable, so for the Borel set B and the arbitrary integrand f ∘ G, Mathlib setIntegral_withDensity_eq_setIntegral_smul₀ gives ∫_B f(G(v)) dν_J(v) = ∫_B (J(v)).toNNReal • f(G(v)) dν(v). Since J ≥ 0, (J(v)).toNNReal = J(v) as a real number, so the integrand is J(v) · f(G(v)).

6. Steps 4 and 5 give ∫_{G(B)} f dμ = ∫_B J(v) · f(G(v)) dν(v). ∎

## Key steps

1. G|_B (Lusin–Souslin) and the inclusion B ↪ ℝ^d are measurable embeddings.
2. Testing the lintegral identity with g := 1_T shows that μ⌞G(B) is the image under G|_B of ν.withDensity(ofReal ∘ J) restricted to B.
3. MeasurableEmbedding.integral_map transports the Bochner integral of an arbitrary f to ∫_B f∘G d(ν.withDensity(ofReal ∘ J)).
4. setIntegral_withDensity_eq_setIntegral_smul₀ with J ≥ 0 turns this into ∫_B J·(f∘G) dν.

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; python3 read of <snapshot>/project/lake-manifest.json`
- `sha256sum <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n 'lemma LocallyLipschitzOn.exists_lipschitzOnWith_of_compact|theorem ContDiffAt.exists_lipschitzOnWith \{|lemma isSigmaCompact_iff_sigmaCompactSpace|protected theorem IsOpen.locallyCompactSpace|theorem LipschitzOnWith.extend_finite_dimension|theorem posDef_gram_of_linearIndependent|theorem det_pos \[|theorem Orthonormal.inner_right_fintype|theorem normDet_sq_eq_det_gram|theorem normDet_comp \(|theorem basisFun_apply|theorem measurable_extend|theorem ContinuousOn.measurableEmbedding|theorem MeasurableSet.image_of_continuousOn_injOn|theorem lintegral_iUnion \[|theorem setLIntegral_congr \{|theorem map_comap_subtype_coe|theorem setIntegral_withDensity_eq_setIntegral_smul₀ \{|theorem withDensity_apply \(|theorem measurable_fderiv :' <snapshot>/mathlib/Mathlib`
- `rg -n 'mem_span_range_iff_exists_fun' / 'euclideanHausdorffMeasure_eq_volume' / 'theorem _root_.MeasurableEmbedding.integral_map' / "theorem ae_restrict_iff' " <snapshot>/mathlib/Mathlib`
- `rg -n 'area_formula|Cauchy-Binet|Cauchy–Binet|cauchyBinet' <snapshot>/mathlib/Mathlib (no match)`
- `rg -n 'theorem weighted_area_formula_volume_of_injective_derivative|theorem areaJacobianAt_eq_normDet|theorem measurable_areaJacobianAt|theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn|^def CountablyRectifiable|theorem countablyRectifiable_iUnion|theorem HasApproximateTangentSpaceAt.unique' .lake/packages/simongmt/Poincare/SimonGMT`
- `Lean probe after import GMT.Ch07.Submission: #check @LinearMap.normDet, @Poincare.SimonGMT.Chapter02.weighted_area_formula_of_injective_derivative, @Matrix.PosSemidef, @gramSchmidtNormed (unknown); @ContinuousOn.measurableEmbedding, @LipschitzOnWith.extend_finite_dimension, @Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn, @integral_withDensity_eq_integral_smul, @MeasurableEmbedding.integral_map, @ContDiffOn.exists_lipschitzOnWith, EuclideanSpace.euclideanHausdorffMeasure_eq_volume (available)`
- `for c in <1647 ref tips>: git show $c:GMT/Ch07/Submission.lean | head -20 | grep import (19 tips add Chapter02.AreaLipschitz, 4 add Chapter02.WeightedArea, incl. accepted c2cf4bd9 and 8a6855aa)`
- `python3 scans of dag.json (902→974 nodes): status and frozen types of the selected node, its 4 dependencies, the diffeo_pushforward rectifiable_area_formula / image_tangent_transport and carrier_area_formula subtrees; regex scan for EuclideanSpace.single|Matrix.det|withDensity|∑' i, ∫⁻|CountablyRectifiable _ (_ '' _); lean_name lookup of the 6 new codim1_lura_* names (no hits); scan of nodes/*/decomposition*.json (no hits)`
- `git grep -l codim1_lura <1738 unique ref tips> -- 'GMT/*.lean' (no match)`
- `git show c2cf4bd9:GMT/Ch07/Submission.lean (accepted dpf_raf_piece_area_formula_gram proof); read nodes/…rectifiab-d698709751/decomposition-v1.json and nodes/…reg-5d8d9c70c5/decomposition-v1.json (reuse-entry format)`
- `git show bfe4427f:GMT/Ch07/Submission.lean + '#print axioms Submission.dpf_itt_ae_of_ae_pieces' (/tmp/af-split/v2/AccAe.lean)`
- `lean -DautoImplicit=false /tmp/af-split/proto/{C1Image,GramChain,GramChainNoImport,GramArea,Glue,Split,Bochner,AePieces}.lean; /tmp/af-split/v1/{Types,Assembly,Combined}.lean; /tmp/af-split/v2/{Types,Combined}.lean (LEAN_PATH = .lake/build/lib/lean + .lake/packages/*/.lake/build/lib/lean)`
- `sed -n 540,640p verifier/gmt-compare.py (contract_scope, child_modules)`
- `independent reviewer subagent in /tmp/af-review: recompiled Combined.lean, byte-compared types with dag.json, instance checks (Inst.lean), Combined2.lean with dpf_itt_ae_of_ae_pieces, GramChainWA.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaFormula.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-3e52779924/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-3e52779924/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-rectifiab-d698709751/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-5d8d9c70c5/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-image-tan-6d6197c93d/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/af-split/v2/Types.lean`
- `/tmp/af-split/v2/Combined.lean`
- `/tmp/af-split/v2/AccAe.lean`
- `/tmp/af-split/v1/Assembly.lean`
- `/tmp/af-split/proto/C1Image.lean`
- `/tmp/af-split/proto/GramChain.lean`
- `/tmp/af-split/proto/GramChainNoImport.lean`
- `/tmp/af-split/proto/GramArea.lean`
- `/tmp/af-split/proto/Glue.lean`
- `/tmp/af-split/proto/Split.lean`
- `/tmp/af-split/proto/Bochner.lean`
- `/tmp/af-split/proto/AePieces.lean`
- `/tmp/af-review/Inst.lean`
- `/tmp/af-review/Combined2.lean`

Pins match.
- Snapshot manifest: project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib.
- Snapshot lake-manifest: simongmt 2b366308, equal to .lake/packages/simongmt.
- Snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).

Library (what exists). Snapshot Mathlib has every fact the children use:
- LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (Topology/Algebra/MetricSpace/Lipschitz.lean:58) and ContDiffAt.exists_lipschitzOnWith (Analysis/Calculus/ContDiff/RCLike.lean:131);
- isSigmaCompact_iff_sigmaCompactSpace (Topology/Compactness/SigmaCompact.lean:174) and IsOpen.locallyCompactSpace (LocallyCompact.lean:224);
- LipschitzOnWith.extend_finite_dimension (Normed/Module/FiniteDimension.lean:207);
- Matrix.posDef_gram_of_linearIndependent (InnerProductSpace/GramMatrix.lean:109) and Matrix.PosDef.det_pos (Matrix/PosDef.lean:549);
- Submodule.mem_span_range_iff_exists_fun (Finsupp/LinearCombination.lean:379) and Orthonormal.inner_right_fintype (Orthonormal.lean:129);
- LinearMap.normDet_sq_eq_det_gram (NormDet.lean:303) and EuclideanSpace.basisFun_apply (PiL2.lean:806);
- measurable_fderiv (FDeriv/Measurable.lean:378) and MeasurableEmbedding.measurable_extend (MeasurableSpace/Embedding.lean:105);
- MeasurableSet.image_of_continuousOn_injOn and ContinuousOn.measurableEmbedding (Polish/Basic.lean:821, 865);
- setLIntegral_congr and lintegral_iUnion (Lebesgue/Basic.lean:281, 597);
- map_comap_subtype_coe and ae_restrict_iff' (Measure/Restrict.lean:934, 629);
- withDensity_apply (WithDensity.lean:44) and setIntegral_withDensity_eq_setIntegral_smul₀ (Bochner/ContinuousLinearMap.lean:323);
- MeasurableEmbedding.integral_map (Bochner/Basic.lean:1093);
- EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean:187).
SimonGMT 2b366308 provides:
- weighted_area_formula_volume_of_injective_derivative (Chapter02/WeightedArea.lean:120);
- areaJacobianAt_eq_normDet (Area.lean:35) and measurable_areaJacobianAt (AreaApproximation.lean:44);
- euclideanHausdorffMeasure_image_le_of_lipschitzOn (Lipschitz.lean:216);
- CountablyRectifiable and countablyRectifiable_iUnion (Chapter03/Rectifiable.lean:34, 76), and HasApproximateTangentSpaceAt.unique (:232).

Library (what is missing).
- The snapshot Mathlib has no general area formula and no Cauchy–Binet (rg: no match).
- After import GMT.Ch07.Submission, LinearMap.normDet, Matrix.posDef_gram_of_linearIndependent and the Chapter02 area lemmas are unknown. The child statements therefore use Matrix.det Gram forms.
- Proofs may add import Poincare.SimonGMT.Chapter02.WeightedArea, as the accepted candidate 8a6855aa does; c2cf4bd9 adds Chapter02.AreaLipschitz.

DAG.
- Reused: accepted dpf_itt_ae_of_ae_pieces, byte-identical type; a fresh compile of bfe4427f gives propext, Classical.choice and Quot.sound.
- Not reusable because their types differ (self-maps of ℝ^P, an Integrable hypothesis, or a set-function hypothesis): the accepted dpf_raf_lintegral_image_eq_tsum_pieces, dpf_raf_piece_area_formula_gram and dpfir_integral_eq_of_area_lintegral, and the open codim1_zsl_ga_integral_transfer.
- The six new codim1_lura_* names occur in no dag.json node (974), in no stored decomposition, and in no GMT/*.lean at any of 1738 ref tips.

Lean.
- v2/Types.lean elaborates all 7 child types in the comparator's contract scope.
- v2/Combined.lean proves the 6 new children using only standard axioms. It also proves the exact frozen parent type from them plus the 4 dependencies and dpf_itt_ae_of_ae_pieces, stubbed with their dag.json types.
- #print axioms lists only those 5 stubs plus propext, Classical.choice and Quot.sound.
