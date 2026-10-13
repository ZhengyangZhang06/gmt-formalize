# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.pushforward_enorm_aemeasurable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝ^k = Eucl k = EuclideanSpace ℝ (Fin k); NVector(ℝ^k, n) is the space of n-vectors (continuous linear functionals on n-covectors) with the operator norm; L_# = nVectorPushforward n L.

This is the measurability claim of step 4 of the parent proof (hJ is a.e.-measurable since h, L and ξ are and (A, w) ↦ ‖A_#w‖ is continuous).

1. (Joint continuity.) The map Π : L(ℝ^P, ℝ^Q) × NVector(ℝ^P, n) → NVector(ℝ^Q, n), Π(T, w) := nVectorPushforward n T w = w ∘ covectorPullback n T, is continuous: T ↦ covectorPullback n T = ContinuousAlternatingMap.compContinuousLinearMapCLM T is continuous (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM, composed with continuous_fst), and composition of continuous linear maps is jointly continuous (Continuous.clm_comp with continuous_snd).
2. (Composition.) x ↦ (L(x), ξ(x)) is μ-a.e. strongly measurable (AEStronglyMeasurable.prodMk), hence so is x ↦ Π(L(x), ξ(x)) (Continuous.comp_aestronglyMeasurable). The norm is continuous, so (T, w) ↦ ‖Π(T, w)‖ is continuous (Continuous.norm; if instance unification between ContinuousLinearMap.hasOpNorm and SeminormedAddGroup.toNorm needs help, state the codomain type explicitly, e.g. Continuous.norm (E := NVector (Eucl Q) n)), and x ↦ ‖L(x)_#ξ(x)‖ is μ-a.e. strongly measurable, hence μ-a.e. measurable; therefore x ↦ ENNReal.ofReal ‖L(x)_#ξ(x)‖ is μ-a.e. measurable (AEMeasurable.ennreal_ofReal).
3. (Extended norm.) For every v, ‖v‖ₑ = ENNReal.ofReal ‖v‖ (ofReal_norm), so x ↦ ‖L(x)_#ξ(x)‖ₑ equals the function of step 2 pointwise and is μ-a.e. measurable (AEMeasurable.congr with the pointwise identity). ∎

## Key steps

1. (T, w) ↦ w ∘ covectorPullback n T is jointly continuous (continuous_compContinuousLinearMapCLM, Continuous.clm_comp).
2. Compose with the a.e. strongly measurable pair (L, ξ) and the continuous norm.
3. ‖v‖ₑ = ofReal ‖v‖ gives a.e.-measurability of the extended norm.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `python3 json read of nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1/parent-child-handoff.json and nodes/root-lipschitz-pushforward-im-a1/decomposition-v1.json (frozen parent and uncle statements)`
- `python3 scan of dag.json lean_name fields for collisions with lpf_raf_* (none)`
- `contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') from verifier/gmt-compare.py to build the exact child scope; lean_contract.validate_lean_statement on all 8 child statements`
- `grep -n '^theorem|^def' simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean (weighted_area_formula_lipschitzOn_fiberSum, aemeasurable_weightedAreaFiberSum_lipschitzOn, ae_fderivWithin_eq_of_lipschitz_extension, exists_lipschitz_extension_finiteDimensional, areaJacobianWithin)`
- `grep -rn 'def weightedAreaFiberSum|def areaFiber|def areaJacobianAt' simongmt/Poincare/SimonGMT`
- `sed -n 1,140p simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean (NVector, covectorPullback, nVectorPushforward, simpleNVector, nVectorPushforward_simple)`
- `grep -n '^theorem|^def' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (CountablyRectifiable, HasWeightedApproximateTangentSpaceAt, HasWeightedApproximateTangentSpaceAt.unique)`
- `grep -n '^theorem' simongmt/Poincare/SimonGMT/Chapter02/{Lipschitz,LipschitzMeasurability}.lean (euclideanHausdorffMeasure_image_le_of_lipschitzOn)`
- `grep -n 'def normDet|normDet_sq_eq_det_gram|normDet_comp|ContinuousLinearMap.normDet_sq' mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `grep -rn 'euclideanHausdorffMeasure_eq_volume|euclideanHausdorffMeasure_def|hausdorffMeasure_image_le' mathlib/Mathlib`
- `grep -rn 'continuous_compContinuousLinearMapCLM|compContinuousLinearMapCLM' mathlib/Mathlib`
- `grep -rn 'MeasurableSet.image_of_continuousOn_injOn|ContinuousOn.measurable_piecewise|nullMeasurableSet_restrict|countable_cover_nhdsWithin|def gram|basisFun_apply|locallyLipschitzOn' mathlib/Mathlib`
- `sed -n 320,445p book/chapter-03.txt (Simon Ch. 3 §2, 2.1–2.6 printed area-formula proof)`
- `lake env lean Scratch/Probe1.lean Scratch/Probe2.lean Scratch/Probe3.lean Scratch/Probe4.lean (child scope: LinearMap.normDet, Matrix.gram and AreaDomain lemmas absent from the frozen closure but present after importing Poincare.SimonGMT.Chapter02.AreaDomain; Real.sqrt, Matrix.det, EuclideanSpace.single, simpleNVector, nVectorPushforward, euclideanHausdorffMeasure_image_le_of_lipschitzOn, continuous_compContinuousLinearMapCLM available; NormSMulClass ℝ (NVector ..) not synthesized)`
- `lake env lean Scratch/Stmts.lean (all 8 child statements elaborate in the comparator child scope, only sorry warnings)`
- `lake env lean Scratch/Assembly.lean (frozen parent type from 4 uncle stubs + children; Assembly.parent has no sorry)`
- `lake env lean Scratch/K1.lean ... Scratch/K8.lean (K1,K3,K5,K8 fully proved; K2 from K1; K4 from K2,K3; K6 from K3,K5; K7 from K2,K4)`
- `lake env lean Scratch/Axioms.lean (#print axioms of the SimonGMT area-formula lemmas: propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/lakefile.toml`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaMultiplicity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/LipschitzMeasurability.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/raf_scratch/Scratch/Stmts.lean`
- `/tmp/raf_scratch/Scratch/Assembly.lean`
- `/tmp/raf_scratch/Scratch/K1.lean`
- `/tmp/raf_scratch/Scratch/K2.lean`
- `/tmp/raf_scratch/Scratch/K3.lean`
- `/tmp/raf_scratch/Scratch/K4.lean`
- `/tmp/raf_scratch/Scratch/K5.lean`
- `/tmp/raf_scratch/Scratch/K6.lean`
- `/tmp/raf_scratch/Scratch/K7.lean`
- `/tmp/raf_scratch/Scratch/K8.lean`
- `/tmp/raf_scratch/Scratch/Axioms.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c, with SimonGMT pinned at 2b36630. The frozen child scope (import GMT.Ch06.Submission plus the replayed namespace GMT.Ch06 and its opens) provides:
- simpleNVector, nVectorPushforward and nVectorPushforward_simple;
- IsRectifiableTriple, HasWeightedApproximateTangentSpaceAt and its .unique;
- SimonGMT Ch02 Lipschitz, including euclideanHausdorffMeasure_image_le_of_lipschitzOn;
- Mathlib's continuous_compContinuousLinearMapCLM, μHE = volume on Eucl n, Real.sqrt, Matrix.det and EuclideanSpace.single.

It does not provide LinearMap.normDet, Matrix.gram or the SimonGMT Ch02 AreaDomain area formula. Child statements therefore use Gram-determinant Jacobians √det(⟨T e_i, T e_j⟩). The local_lipschitz_area proof imports Poincare.SimonGMT.Chapter02.AreaDomain, which transitively brings in NormDet and changes no frozen type. Through that import it bridges to:
- weighted_area_formula_lipschitzOn_fiberSum and aemeasurable_weightedAreaFiberSum_lipschitzOn;
- ae_fderivWithin_eq_of_lipschitz_extension;
- LinearMap.normDet_sq_eq_det_gram.
All of these use standard axioms only.

No SimonGMT or Mathlib declaration states the rectifiable area formula, its chart decomposition or the n-vector Jacobian identity, so these are the new children.

Scratch Lean checks in the exact comparator scope:
- all 8 statements elaborate and validate;
- the frozen parent follows from the 4 uncles plus children K1, K6, K7, K8;
- every child is proved from its declared siblings (K1, K3, K5, K8 outright).

No lpf_raf_* name collides with dag.json.
