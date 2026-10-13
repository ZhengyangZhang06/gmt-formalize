# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.area_formula-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.area_formula-a1.gram_area-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the Notation paragraph of the parent proof (normDet Λ := (det[⟨Λe_k, Λe_l⟩])^{1/2} and SimonGMT areaJacobianAt f a = normDet Df(a)), its step 4 (measurability of b ↦ normDet D(·)(b) via SimonGMT measurable_areaJacobianAt) and its step 6(a) (the injective area formula SimonGMT weighted_area_formula_of_injective_derivative with finrank ℝ^m = m and an arbitrary weight), isolated for a single map f. Notation: e_k := EuclideanSpace.single k 1; (e_k)_{k<m} is the standard orthonormal basis of ℝ^m (Mathlib EuclideanSpace.basisFun, whose k-th vector is EuclideanSpace.single k 1 by EuclideanSpace.basisFun_apply). For a linear map T : ℝ^m → ℝ^P, normDet T ≥ 0 is Mathlib's LinearMap.normDet, and SimonGMT defines areaJacobianAt f x := normDet(Df(x)) (areaJacobianAt_eq_normDet).

1. (Jf = areaJacobianAt f.) Let x ∈ ℝ^m and T := Df(x). Mathlib LinearMap.normDet_sq_eq_det_gram, applied to T and the orthonormal basis (e_k) of ℝ^m, gives normDet(T)² = det Gram(Te_0, …, Te_{m−1}), where Gram(v) = Matrix.gram ℝ v = Matrix.of (k, l ↦ ⟨v_k, v_l⟩) and the coercion ℝ → ℝ is the identity. So normDet(T)² = det[⟨Te_k, Te_l⟩]. As normDet(T) ≥ 0, normDet(T) = (normDet(T)²)^{1/2} = (det[⟨Te_k, Te_l⟩])^{1/2}. Hence Jf(x) = normDet(Df(x)) = areaJacobianAt f x for every x ∈ ℝ^m (not only on s).

2. (Proof of (i).) SimonGMT Chapter02 measurable_areaJacobianAt states that x ↦ areaJacobianAt f x is measurable for every f between finite-dimensional real inner product spaces. By step 1 the functions Jf and areaJacobianAt f are equal, so Jf is Borel measurable. (Alternatively: Df is Borel by Mathlib measurable_fderiv, and T ↦ (det[⟨Te_k, Te_l⟩])^{1/2} is continuous on the space of linear maps, as a composition of evaluations, inner products, a polynomial determinant and the square root.)

3. (The injective area formula.) SimonGMT Chapter02 weighted_area_formula_volume_of_injective_derivative (Simon (3.5) for an injective regular parametrization in arbitrary codimension) states: if E, F are finite-dimensional real inner product spaces with their Borel σ-algebras, s ⊆ E is Borel, f : E → F is differentiable at every x ∈ s with Df(x) injective, f is injective on s, and g : F → [0, ∞] is arbitrary, then ∫⁻_{f(s)} g dμHE[finrank ℝ E] = ∫⁻_s ofReal(areaJacobianAt f x) · g(f(x)) dλ_E(x), with λ_E = volume on E. Apply it with E := ℝ^m, F := ℝ^P and the given s, f, g. Since finrank ℝ ℝ^m = m (finrank_euclideanSpace_fin), the measure on the left is μHE[m] = H^m.

4. (Proof of (ii).) By step 1 the integrands ofReal(areaJacobianAt f x) · g(f(x)) and ofReal(Jf(x)) · g(f(x)) agree at every x, so the right side of step 3 equals ∫⁻_s ofReal(Jf(x)) · g(f(x)) dλ(x). This is (ii). ∎

Lean remark: the proof uses SimonGMT's Chapter02 area modules; Submission.lean may add `import Poincare.SimonGMT.Chapter02.WeightedArea` (which also brings Mathlib's NormDet). The statement itself needs no extra import.

## Key steps

1. normDet_sq_eq_det_gram with the standard orthonormal basis EuclideanSpace.single k 1 gives Jf(x) = normDet Df(x) = areaJacobianAt f x for every x.
2. measurable_areaJacobianAt gives Borel measurability of Jf: conclusion (i).
3. SimonGMT's weighted injective area formula with finrank ℝ^m = m gives ∫⁻_{f(s)} g dH^m = ∫⁻_s ofReal(areaJacobianAt f x) g(f x) dλ for arbitrary g.
4. Replacing areaJacobianAt f by Jf pointwise gives conclusion (ii).

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
