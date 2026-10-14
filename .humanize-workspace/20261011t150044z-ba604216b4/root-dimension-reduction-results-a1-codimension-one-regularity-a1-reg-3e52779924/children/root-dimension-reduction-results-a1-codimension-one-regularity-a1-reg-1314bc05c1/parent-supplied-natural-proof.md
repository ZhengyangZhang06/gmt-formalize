# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.area_formula-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.area_formula-a1.borel_glue-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent proof (definition of J: 'F_i restricted to B_i is a measurable embedding (Mathlib ContinuousOn.measurableEmbedding) … ψ_i := (F_i|_{B_i})^{-1} : A_i → B_i is Borel … J(v) := j_i(ψ_i(v)) for v ∈ A_i and J(v) := 0 for v ∉ ⋃_i A_i; this is well defined because the A_i are disjoint'), stated for arbitrary Borel weights h_i ≥ 0.

1. (Lusin–Souslin.) Fix i. ℝ^m is a Polish space, B_i is Borel, F_i is continuous on B_i and injective on B_i. By the Lusin–Souslin theorem the restriction e_i := F_i|_{B_i} : B_i → ℝ^d is a measurable embedding (Mathlib ContinuousOn.measurableEmbedding): it is injective, Borel measurable, and maps Borel subsets of B_i onto Borel subsets of ℝ^d. Its range is A_i := F_i(B_i).

2. (The glued function on one piece.) Define J_i : ℝ^d → ℝ by J_i(v) := h_i(e_i^{-1}(v)) for v ∈ A_i and J_i(v) := 0 for v ∉ A_i; in Lean, J_i := Function.extend e_i (h_i ∘ val) 0. J_i is Borel because e_i is a measurable embedding and h_i ∘ val and the constant 0 are measurable (Mathlib MeasurableEmbedding.measurable_extend: for v in the Borel range the value is (h_i ∘ val ∘ e_i^{-1})(v), where e_i^{-1} : A_i → B_i is measurable, and outside the range it is 0). Moreover J_i(F_i(b)) = h_i(b) for b ∈ B_i (injectivity of e_i, Function.Injective.extend_apply), and J_i(v) = 0 for v ∉ A_i (Function.extend_apply').

3. (Gluing.) Define J : ℝ^d → ℝ by J(v) := (Σ_{i∈ℕ} ofReal(J_i(v))).toReal, the countable sum being taken in [0, ∞]. Each v ↦ ofReal(J_i(v)) is measurable, a countable sum of measurable [0, ∞]-valued functions is measurable, and toReal : [0, ∞] → ℝ is measurable; so J is Borel. J(v) ≥ 0 for every v because toReal takes values in [0, ∞).

4. (Values on the pieces.) Let i ∈ ℕ and b ∈ B_i, and put v := F_i(b) ∈ A_i. For j ≠ i, v ∉ A_j because A_i ∩ A_j = ∅, so J_j(v) = 0 by step 2 and ofReal(J_j(v)) = 0. Hence the sum in step 3 has the single possibly nonzero term ofReal(J_i(v)) = ofReal(h_i(b)) (tsum_eq_single), and J(v) = toReal(ofReal(h_i(b))) = h_i(b) because h_i(b) ≥ 0. ∎

## Key steps

1. Lusin–Souslin: e_i := F_i|_{B_i} is a measurable embedding with Borel range A_i = F_i(B_i).
2. J_i := extend e_i (h_i ∘ val) 0 is Borel, equals h_i ∘ e_i^{-1} on A_i and 0 off A_i.
3. J := (Σ_i ofReal ∘ J_i).toReal is Borel and nonnegative.
4. By disjointness only the i-th term survives at F_i(b), so J(F_i(b)) = h_i(b) because h_i(b) ≥ 0.

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
