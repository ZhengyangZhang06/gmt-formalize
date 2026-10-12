# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.local_lipschitz_area-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝ^k = Eucl k = EuclideanSpace ℝ (Fin k) with inner product ⟨·,·⟩ and norm |·|; Hⁿ = μHE[n] (Mathlib's Euclidean-normalized n-dimensional Hausdorff measure); Lⁿ = volume on ℝⁿ, and Hⁿ = Lⁿ on ℝⁿ (EuclideanSpace.euclideanHausdorffMeasure_eq_volume). e_i = EuclideanSpace.single i 1 (i : Fin n) is the standard orthonormal basis of ℝⁿ. For a linear map T : ℝⁿ → ℝ^k, JT := √det(⟨T e_i, T e_j⟩)_{i,j} (Gram-determinant Jacobian); for a map φ, Jφ(w) := J(fderiv ℝ φ w). For B ⊆ X, a map f and a weight h ≥ 0, the fibre sum is N_B(y) := Σ_{x ∈ B, f(x) = y} h(x), the unordered sum in [0,∞] (∑' over the subtype {x // x ∈ B ∧ f x = y}). c-antilipschitz on Ω means c|w − w′| ≤ |Φ(w) − Φ(w′)| for all w, w′ ∈ Ω.

This is step 5 of the parent proof (area formula for u_j = f∘Φ_j with measurability, via a countable cover by balls on which u_j is Lipschitz) for a general locally Lipschitz u; it is also the engine of step 4. Add `import Poincare.SimonGMT.Chapter02.AreaDomain` to the Submission header (or to a new file under GMT/Ch06/ that the Submission imports); it transitively imports Mathlib.Analysis.InnerProductSpace.NormDet, so LinearMap.normDet and Matrix.gram become available. Adding this import was checked to leave all Contract definitions and all frozen statement types unchanged (the comparator only byte-checks the Contract and Lake files). Do not re-prove the Euclidean area formula: use the SimonGMT theorems cited below.

1. (Jacobian normalization.) For every linear T : ℝⁿ → ℝ^Q, normDet(T) = JT. Indeed (e_i) is the orthonormal basis EuclideanSpace.basisFun (EuclideanSpace.basisFun_apply: its i-th vector is EuclideanSpace.single i 1), so LinearMap.normDet_sq_eq_det_gram gives normDet(T)² = det(Matrix.gram ℝ (T e_·)) = det(⟨T e_i, T e_j⟩)_{i,j} (Matrix.gram is Matrix.of fun i j => ⟪v i, v j⟫); since normDet(T) ≥ 0 (LinearMap.normDet_nonneg), normDet(T) = √(normDet(T)²) = JT.
2. (Countable Lipschitz cover.) For each x ∈ Ω, local Lipschitzness gives K_x ≥ 0 and t_x ∈ 𝓝[Ω] x with u K_x-Lipschitz on t_x; as Ω is open, 𝓝[Ω] x = 𝓝 x (IsOpen.nhdsWithin_eq), so there is r_x > 0 with ball(x, r_x) ⊆ t_x ∩ Ω. These balls cover Ω and ℝⁿ is second countable, so a countable S ⊆ Ω satisfies Ω ⊆ ⋃_{x ∈ S} ball(x, r_x) (TopologicalSpace.countable_cover_nhdsWithin). If S = ∅ then Ω = ∅ and D = ∅: every fibre is empty, N ≡ 0 (measurable) and both integrals vanish. Otherwise write S = {s_0, s_1, …} (Set.Countable.exists_eq_range) and put V_m := ball(s_m, r_{s_m}): V_m is open, V_m ⊆ Ω, u is K_m-Lipschitz on V_m (K_m := K_{s_m}), and Ω ⊆ ⋃_m V_m.
3. (Disjoint pieces.) Let V′_m := V_m ∖ ⋃_{l<m} V_l (disjointed V): Borel, pairwise disjoint, V′_m ⊆ V_m and ⋃_m V′_m = ⋃_m V_m (iUnion_disjointed). Put D_m := D ∩ V′_m. Then D_m ⊆ D, D_m ⊆ V_m, the D_m are pairwise disjoint, each D_m is Lⁿ-null-measurable, and D ⊆ ⋃_m D_m because D ⊆ Ω ⊆ ⋃_m V′_m.
4. (Area formula on one piece.) Fix m. u is K_m-Lipschitz on D_m ⊆ V_m, D_m is null-measurable, and w is a.e.-measurable for Lⁿ⌞D_m (AEMeasurable.mono_set, D_m ⊆ D). The weighted area formula for Lipschitz maps on measurable subsets of ℝⁿ (Simon Ch. 2 (3.5); SimonGMT Poincare.SimonGMT.Chapter02.weighted_area_formula_lipschitzOn_fiberSum with E = ℝⁿ, F = ℝ^Q, finrank ℝ ℝⁿ = n by finrank_euclideanSpace_fin) and its measurability companion (aemeasurable_weightedAreaFiberSum_lipschitzOn) state that N_m(y) := Σ_{x ∈ D_m, u(x) = y} w(x) (which is weightedAreaFiberSum D_m u w y by definition) is Hⁿ-a.e. measurable and ∫ N_m dHⁿ = ∫_{D_m} normDet(fderivWithin ℝ u D_m x)·w(x) dLⁿ(x) (the integrand is ENNReal.ofReal (areaJacobianWithin u D_m x) * w x).
5. (Within-derivative versus derivative.) Let g_m be a global Lipschitz extension of u|V_m (exists_lipschitz_extension_finiteDimensional), so u = g_m on V_m. By ae_fderivWithin_eq_of_lipschitz_extension (applied to D_m, with u = g_m on D_m), fderivWithin ℝ u D_m x = fderiv ℝ g_m x for Lⁿ⌞D_m-a.e. x. For x ∈ D_m ⊆ V_m, u and g_m agree on the open neighbourhood V_m of x, so fderiv ℝ u x = fderiv ℝ g_m x (Filter.EventuallyEq.fderiv_eq). Hence for Lⁿ⌞D_m-a.e. x, normDet(fderivWithin ℝ u D_m x) = normDet(fderiv ℝ u x) = Ju(x) by step 1, and therefore ∫_{D_m} w·Ju dLⁿ = ∫ N_m dHⁿ (lintegral_congr_ae and commutativity of multiplication).
6. (Gluing.) Apply the sibling lemma fiber_sum_glue with X = ℝⁿ, μ = Lⁿ, Y = ℝ^Q, ν = Hⁿ, map u, weight h := w, integrand F(x) := w(x)·ofReal(Ju(x)), A := D, Z := ∅ and B := (D_m)_m: (a)–(c) and (d) D ⊆ ∅ ∪ ⋃_m D_m hold by step 3, (e) Lⁿ(∅) = 0, (f) Hⁿ(u(∅)) = Hⁿ(∅) = 0, and (g) holds by steps 4–5. Its conclusions are exactly the two claims. ∎

## Key steps

1. normDet T = √det Gram(T e_i) (LinearMap.normDet_sq_eq_det_gram with EuclideanSpace.basisFun).
2. Countable cover of Ω by balls V_m ⊆ Ω on which u is Lipschitz (countable_cover_nhdsWithin); empty case trivial.
3. Disjoint null-measurable pieces D_m = D ∩ disjointed V m covering D.
4. SimonGMT weighted_area_formula_lipschitzOn_fiberSum and aemeasurable_weightedAreaFiberSum_lipschitzOn on each D_m.
5. fderivWithin u D_m = fderiv u a.e. on D_m via a Lipschitz extension (ae_fderivWithin_eq_of_lipschitz_extension, EventuallyEq.fderiv_eq).
6. Glue the pieces with fiber_sum_glue (Z = ∅).

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
