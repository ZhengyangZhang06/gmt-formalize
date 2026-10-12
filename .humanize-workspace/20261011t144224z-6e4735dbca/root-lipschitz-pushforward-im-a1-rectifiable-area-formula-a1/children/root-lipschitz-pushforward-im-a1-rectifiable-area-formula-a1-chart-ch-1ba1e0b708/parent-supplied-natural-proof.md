# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.chart_change_of_variables-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝ^k = Eucl k = EuclideanSpace ℝ (Fin k) with inner product ⟨·,·⟩ and norm |·|; Hⁿ = μHE[n] (Mathlib's Euclidean-normalized n-dimensional Hausdorff measure); Lⁿ = volume on ℝⁿ, and Hⁿ = Lⁿ on ℝⁿ (EuclideanSpace.euclideanHausdorffMeasure_eq_volume). e_i = EuclideanSpace.single i 1 (i : Fin n) is the standard orthonormal basis of ℝⁿ. For a linear map T : ℝⁿ → ℝ^k, JT := √det(⟨T e_i, T e_j⟩)_{i,j} (Gram-determinant Jacobian); for a map φ, Jφ(w) := J(fderiv ℝ φ w). For B ⊆ X, a map f and a weight h ≥ 0, the fibre sum is N_B(y) := Σ_{x ∈ B, f(x) = y} h(x), the unordered sum in [0,∞] (∑' over the subtype {x // x ∈ B ∧ f x = y}). c-antilipschitz on Ω means c|w − w′| ≤ |Φ(w) − Φ(w′)| for all w, w′ ∈ Ω.

This is step 4 of the parent proof (area formula for the injective Lipschitz chart Φ_j, transferring integrals over A_j to D_j, with the null-measurability of D_j and the a.e.-measurability of g∘Φ_j from step 1), for a single chart.

1. Φ is injective on Ω (if Φ(w) = Φ(w′) then c|w − w′| ≤ 0) and continuous on Ω (Lipschitz on Ω).
2. (Borel preimages.) For every Borel B ⊆ ℝ^P, Ω ∩ Φ⁻¹(B) is Borel: the map Φ̃ := Ω.piecewise Φ 0 (Φ on Ω, 0 off Ω) is Borel measurable (ContinuousOn.measurable_piecewise, Φ continuous on the measurable set Ω, the constant continuous on Ωᶜ), and Ω ∩ Φ⁻¹(B) = Ω ∩ Φ̃⁻¹(B).
3. (First conclusion.) Choose a Borel B ⊆ A with Hⁿ(A ∖ B) = 0 (NullMeasurableSet.exists_measurable_subset_ae_eq). Then D = (Ω ∩ Φ⁻¹(B)) ∪ (Ω ∩ Φ⁻¹(A ∖ B)); the first set is Borel by step 2 and the second is Lⁿ-null by the sibling lemma chart_preimage_null (with Z := A ∖ B). Hence D is Lⁿ-null-measurable.
4. (Second conclusion.) Choose a measurable g′ with g = g′ Hⁿ⌞A-a.e. Since A is null-measurable, Hⁿ⌞A(E) = Hⁿ(E ∩ A) for every E (Measure.restrict_apply₀'), so Z′ := {x : g(x) ≠ g′(x)} ∩ A is Hⁿ-null, and by chart_preimage_null Lⁿ(Ω ∩ Φ⁻¹(Z′)) = 0. For w ∈ D outside Ω ∩ Φ⁻¹(Z′) we have Φ(w) ∈ A and g(Φ(w)) = g′(Φ(w)). Since Lⁿ⌞D-a.e. w lies in D (D null-measurable, ae_restrict_mem₀) and outside the null set Ω ∩ Φ⁻¹(Z′) (ae_restrict_of_ae), g∘Φ = g′∘Φ Lⁿ⌞D-a.e. Moreover Φ is a.e.-measurable for Lⁿ⌞Ω (ContinuousOn.aemeasurable), hence for Lⁿ⌞D (D ⊆ Ω), so g′∘Φ is a.e.-measurable for Lⁿ⌞D (Measurable.comp_aemeasurable) and so is g∘Φ (AEMeasurable.congr).
5. (Area formula for Φ on D.) Φ is Lipschitz on Ω, hence locally Lipschitz on Ω (at each point use the neighbourhood Ω itself, self_mem_nhdsWithin). Apply the sibling lemma local_lipschitz_area with Q := P, the open set Ω, D ⊆ Ω (null-measurable by step 3), u := Φ and weight w ↦ g(Φ(w)) (a.e.-measurable by step 4): ∫_D g(Φ(w))·JΦ(w) dLⁿ(w) = ∫_{ℝ^P} N dHⁿ with N(y) := Σ_{w ∈ D, Φ(w) = y} g(Φ(w)).
6. (Fibres.) N = 1_A·g pointwise. If y ∈ A, then y = Φ(w₀) for some w₀ ∈ Ω (A ⊆ Φ(Ω)); w₀ ∈ D and, by injectivity of Φ on Ω, the fibre {w ∈ D : Φ(w) = y} is exactly {w₀}, so N(y) = g(Φ(w₀)) = g(y) (tsum_eq_single). If y ∉ A, no w ∈ D satisfies Φ(w) = y because Φ(w) ∈ A for w ∈ D; the fibre is empty and N(y) = 0.
7. (Third conclusion.) ∫ N dHⁿ = ∫ 1_A·g dHⁿ = ∫_A g dHⁿ (lintegral_indicator₀, A null-measurable). With step 5, ∫_A g dHⁿ = ∫_D g(Φ(w))·JΦ(w) dLⁿ(w). ∎

## Key steps

1. Φ is injective and continuous on Ω; Ω ∩ Φ⁻¹(Borel) is Borel (ContinuousOn.measurable_piecewise).
2. D = Borel part ∪ preimage of an Hⁿ-null set, null by chart_preimage_null: D is Lⁿ-null-measurable.
3. g∘Φ = g′∘Φ a.e. on D (g′ measurable) using chart_preimage_null on {g ≠ g′} ∩ A: a.e.-measurability.
4. local_lipschitz_area for u := Φ, weight g∘Φ on D ⊆ Ω.
5. By injectivity the fibre sum equals the indicator 1_A g; lintegral_indicator₀ gives ∫_A g dHⁿ.

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
