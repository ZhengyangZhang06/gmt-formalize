# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.countably_rectifiable_c1_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions used below. ℝ^P = EuclideanSpace ℝ (Fin P) with inner product ⟨·,·⟩ and norm |·|; Hⁿ = μHE[n] (Mathlib's Euclidean-normalized n-dimensional Hausdorff measure; on ℝⁿ it equals Lebesgue measure Lⁿ = volume, it is invariant under isometries and translations and scales by λⁿ under x ↦ λx). An n-covector α is a continuous alternating n-linear map (ℝ^P)ⁿ → ℝ with the operator norm ‖α‖ (least C with |α(u₁,…,u_n)| ≤ C Π|u_i|); an n-vector is a continuous linear functional on n-covectors with the operator norm; simpleNVector v is the n-vector α ↦ α(v₁,…,v_n), so |simpleNVector v (α)| ≤ ‖α‖ Π|v_i|; for a linear map A, A_# w := nVectorPushforward n A w = w ∘ A^#, where A^#α = α(A·,…,A·), it is linear in w and A_#(simpleNVector v) = simpleNVector(A v) (`nVectorPushforward_simple`). A map Φ is c-antilipschitz on Ω if c|w − w′| ≤ |Φ(w) − Φ(w′)| for all w, w′ ∈ Ω.

This is Simon Ch. 3, Lemma 1.2, “only if” part (printed proof adapted), used in Step 1 of the parent proof (Remark 1.3). Let M be countably n-rectifiable: M ⊆ M₀ ∪ ⋃_{j≥1} F_j(ℝⁿ) with Hⁿ(M₀) = 0 and F_j : ℝⁿ → ℝ^P Lipschitz (Definition 1.1).

1. Fix j. Apply the sibling lemma lipschitz_c1_immersion_pieces to u := F_j and Ω := ℝⁿ (open; F_j is Lipschitz, hence locally Lipschitz): we get C¹ maps G_{j,k} : ℝⁿ → ℝ^P, open O_{j,k} with G_{j,k} antilipschitz on O_{j,k}, and Borel E_{j,k} ⊆ O_{j,k} with F_j = G_{j,k} on E_{j,k}, such that Lⁿ-a.e. w at which F_j is differentiable with injective derivative lies in ⋃_k E_{j,k}.

2. Decompose ℝⁿ = N_j ∪ C_j ∪ R_j, where N_j := {w : F_j not differentiable at w}, C_j := {w : F_j differentiable at w, DF_j(w) not injective}, R_j := {w : F_j differentiable at w, DF_j(w) injective}. These sets are Borel (the differentiability set is Borel and w ↦ fderiv F_j w is Borel measurable, Mathlib `measurable_fderiv`). By Rademacher's theorem Lⁿ(N_j) = 0, and by step 1 Lⁿ(R_j ∖ ⋃_k E_{j,k}) = 0.

3. Hⁿ(F_j(N_j ∪ (R_j ∖ ⋃_k E_{j,k}))) = 0: F_j is Lipschitz with constant Λ_j, so Hⁿ(F_j(Z)) ≤ Λ_jⁿ Hⁿ(Z) = Λ_jⁿ Lⁿ(Z) = 0 for every Lⁿ-null Z ⊆ ℝⁿ (on ℝⁿ, Hⁿ = μHE[n] = Lⁿ).

4. Hⁿ(F_j(C_j)) = 0, by the area formula (Simon: “by the area formula Lⁿ{x : JG_ij = 0} …”). In Lean this is directly SimonGMT `area_image_compl_regularSet_eq_zero` (Chapter02/AreaLipschitz.lean: critical and non-differentiability images of a Lipschitz map are Hⁿ-null). Mathematically: for the Lipschitz map F_j on the Borel set C_j, Simon Ch. 2 (3.4) (SimonGMT `area_formula_lipschitzOn_multiplicity`) gives ∫_{ℝ^P} #(C_j ∩ F_j⁻¹(y)) dHⁿ(y) = ∫_{C_j} JF_j dLⁿ, where JF_j(w) = √det(DF_j(w)* DF_j(w)) (Jacobian of the within derivative, which agrees a.e. on C_j with DF_j). For w ∈ C_j, DF_j(w)*DF_j(w) is singular, so JF_j = 0 a.e. on C_j and the right side is 0. F_j(C_j) is Hⁿ-null-measurable (C_j is a countable union of bounded Borel sets of finite measure and F_j is Lipschitz; SimonGMT `nullMeasurableSet_image_of_lipschitzOn`), and the multiplicity is ≥ 1 on F_j(C_j), so Hⁿ(F_j(C_j)) = ∫ 1_{F_j(C_j)} dHⁿ ≤ ∫ #(C_j ∩ F_j⁻¹(y)) dHⁿ(y) = 0.

5. For w ∈ E_{j,k}, F_j(w) = G_{j,k}(w) ∈ G_{j,k}(O_{j,k}). Hence F_j(ℝⁿ) ⊆ F_j(N_j ∪ (R_j ∖ ⋃_k E_{j,k})) ∪ F_j(C_j) ∪ ⋃_k G_{j,k}(O_{j,k}).

6. (Lipschitz bound by shrinking.) Each open O_{j,k} is the union of the countably many open balls B with rational centre and rational radius and closure B ⊆ O_{j,k}. On such B, ‖DG_{j,k}‖ is bounded on the compact convex set closure B, so by the mean value inequality G_{j,k} is Lipschitz on B (constant sup_{closure B}‖DG_{j,k}‖); and G_{j,k} is antilipschitz on B ⊆ O_{j,k} with the constant of O_{j,k}. Enumerate all triples (j, k, B) as l = 0, 1, 2, … (pad with Ω_l := ∅ if needed) and set Φ_l := G_{j,k}, Ω_l := B. Then each Ω_l is open, Φ_l is C¹ (`ContDiff ℝ 1`), Lipschitz and antilipschitz on Ω_l, and ⋃_l Φ_l(Ω_l) = ⋃_{j,k} G_{j,k}(O_{j,k}).

7. By steps 3–6, M ∖ ⋃_l Φ_l(Ω_l) ⊆ M₀ ∪ ⋃_j [F_j(N_j ∪ (R_j ∖ ⋃_k E_{j,k})) ∪ F_j(C_j)], a countable union of Hⁿ-null sets. Hence Hⁿ(M ∖ ⋃_l Φ_l(Ω_l)) = 0. ∎ (When n > P every set in ℝ^P is Hⁿ-null and the statement is immediate; the proof above also covers it.)

## Key steps

1. Write M ⊆ M₀ ∪ ⋃_j F_j(ℝⁿ) with F_j Lipschitz and apply lipschitz_c1_immersion_pieces to each F_j on ℝⁿ.
2. Images of the non-differentiability set and of the uncovered regular set are Hⁿ-null (Rademacher, Lipschitz image bound).
3. The image of the critical set is Hⁿ-null by the area formula (Jacobian 0 there).
4. On E_{j,k}, F_j = G_{j,k}, so F_j(ℝⁿ) is covered up to null sets by the antilipschitz C¹ pieces G_{j,k}(O_{j,k}).
5. Shrink each O_{j,k} to rational balls with compact closure inside to make the charts Lipschitz too; enumerate.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp workspace GMT/Ch06/Contract.lean against snapshot project/GMT/Ch06/Contract.lean and GMT/Ch06/Submission.lean (all identical)`
- `python3 listing of lean_name fields in dag.json (only GMT.Ch06.main_theorem and its 12 children reserved; no lpf_* names)`
- `contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') from verifier/gmt-compare.py to generate the exact child scope; lean_contract.validate_lean_statement on all 11 child statements`
- `rg -n 'μHE' mathlib/Mathlib (Geometry/Euclidean/Volume/Measure.lean: euclideanHausdorffMeasure_def, euclideanHausdorffMeasure_zero, euclideanHausdorffMeasure_smul₀, EuclideanSpace.euclideanHausdorffMeasure_eq_volume)`
- `rg -n 'theorem IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero|theorem ae_eq_zero_of_integral_contDiff_smul_eq_zero' mathlib/Mathlib`
- `rg -n 'theorem measurable_fderiv' mathlib/Mathlib`
- `rg -n 'theorem hausdorffMeasure_of_dimH_lt' mathlib/Mathlib`
- `rg -n 'theorem abs_volumeForm_apply_le|normDet_sq_eq_det_gram|theorem map_linearDependent|theorem LipschitzOnWith.extend_pi' mathlib/Mathlib`
- `rg -n -i 'hadamard.s inequality|det_le_prod|abs_det_le' mathlib/Mathlib (no packaged Hadamard inequality besides Orientation.abs_volumeForm_apply_le)`
- `grep -n '^theorem|^def' simongmt/Poincare/SimonGMT/Chapter03/{Rectifiable,SubmanifoldCover,Differential}.lean`
- `grep -n '^theorem' simongmt/Poincare/SimonGMT/Chapter02/{Lipschitz,AreaDomain,AreaLipschitz,AreaNoninjective,AreaCompletion,AreaMultiplicity,LipschitzMeasurability,WhitneyExtension,WhitneyCover}.lean`
- `grep -n 'simon_theorem_3_6' simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean; grep -n '^theorem' Chapter01/Lusin.lean Chapter01/GeneralDifferentiation.lean`
- `ls simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02 | grep -i whitney (WhitneyCover/Jet/Partition built; WhitneyExtension.olean absent)`
- `lake env lean Scratch/Probe*.lean (#print GeometricCurrentOn.support/zeroRegion/VanishesOn, TestFormOn, IsTestForm, TestFormOnConverges, simpleNVector, covectorPullback; #synth Norm (NVector (Eucl 3) 2) = ContinuousLinearMap.hasOpNorm; Norm (Covector (Eucl 3) 2) = ContinuousAlternatingMap.instNormedAddCommGroup.toNorm; MeasureSpace (Eucl 3) = measureSpaceOfInnerProductSpace; Chapter02.IsSimonSubmanifold not in child scope; LinearMap.range needs (fderiv ℝ Φ w).toLinearMap)`
- `lake env lean Scratch/Stmts.lean (11 child statements in comparator child scope; only sorry warnings)`
- `lake env lean Scratch/Assembly.lean (parent from lpf_tangential_differential_exists, lpf_pushforward_is_current, lpf_pushforward_integrality; #print axioms)`
- `grep -n 'Lemma|Theorem|Remark' book/chapter-03.txt; sed -n 1,445p book/chapter-03.txt; sed -n 160,270p and 900,1000p book/chapter-02.txt; sed -n 740,900p book/chapter-06.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/HausdorffDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/Orientation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaMultiplicity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/lpim_scratch/Scratch/scope_prefix.txt`
- `/tmp/lpim_scratch/Scratch/Stmts.lean`
- `/tmp/lpim_scratch/Scratch/Assembly.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 Contract, byte-identical to the workspace Contract and Submission. Only GMT.Ch06.main_theorem and its 12 children are reserved in the DAG, so the bare lpf_* names are free.

The child scope (import GMT.Ch06.Submission plus the replayed namespace and opens) gives the contract notions and SimonGMT Ch01 Densities, Ch03 Rectifiable (HasWeightedApproximateTangentSpaceAt, blowUpMap, CountablyRectifiable, .unique) and Ch06 (NVector, simpleNVector, nVectorPushforward, nVectorPushforward_simple, TestFormOn, GeometricCurrentOn, support). Chapter02.IsSimonSubmanifold is not in scope, so C¹ pieces are stated as C¹ maps that are antilipschitz on open sets.

Instance checks:
- NVector carries the operator norm over the ContinuousAlternatingMap norm, so ‖simpleNVector v‖² is the Gram determinant and ‖L_#ξ‖ is the area Jacobian.
- volume on Eucl n is measureSpaceOfInnerProductSpace, and μHE[n] = volume there.
- μHE[0] = μH[0].

Mathlib provides the fundamental lemma (IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero), measurable_fderiv, hausdorffMeasure_of_dimH_lt, Hadamard via Orientation.abs_volumeForm_apply_le, normDet_sq_eq_det_gram, AlternatingMap.map_linearDependent and LipschitzOnWith.extend_pi.

SimonGMT provides Rademacher, Lipschitz image bounds and image measurability (Ch02/Lipschitz). It provides the full Euclidean area formula with fibre sums and its a.e.-measurability (Ch02/AreaDomain: weighted_area_formula_lipschitzOn_fiberSum, aemeasurable_weightedAreaFiberSum_lipschitzOn, ae_fderivWithin_eq_of_lipschitz_extension) and null critical images (Ch02/AreaLipschitz: area_image_compl_regularSet_eq_zero). It also provides the upper density theorem (Ch01 simon_theorem_3_6), Lusin (Ch01/Lusin), and the C¹-cover-to-rectifiable direction (Ch03/SubmanifoldCover).

SimonGMT does not provide:
- Lemma 1.2 ⇒, Theorem 1.6/1.9 existence, or the rectifiable area formula; these are the new children.
- A packaged C¹ approximation theorem: Whitney machinery exists in Ch02/WhitneyExtension.lean, but that file is not built.

All 11 child statements pass the lexical validator and elaborate in the comparator child scope. The parent assembly from 3 children is kernel-checked with the standard axioms only. These checks do not certify the analytic proofs.
