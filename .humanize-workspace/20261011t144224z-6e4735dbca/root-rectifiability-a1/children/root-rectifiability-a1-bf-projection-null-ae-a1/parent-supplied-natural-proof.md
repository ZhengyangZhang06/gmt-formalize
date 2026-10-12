# Parent-supplied natural-language proof

- Parent DAG node: `root.rectifiability-a1`
- Child DAG node: `root.rectifiability-a1.bf_projection_null_ae-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: P. Mattila, Geometry of Sets and Measures in Euclidean Spaces, Theorem 18.1: the Besicovitch-Federer projection theorem, direction 'purely unrectifiable ⇒ almost all projections null'. We follow the proof of Theorem 1.2 ('only if' part) in R. Hovila, E. Järvenpää, M. Järvenpää and F. Ledrappier, Geom. Dedicata 161 (2012), arXiv:1104.3453, which combines its Lemmas 2.2-2.4. Here it is applied to the family of linear maps L_v, v ∈ (ℝ^N)^k (the k×N matrices with rows v₁, …, v_k). Simon states the projection theorem as Ch. 3, 3.6 without proof ([Fed69, 3.3.13]).
 The ingredients are: the sibling bf_cone_density (Lemma 2.2 there: E_{1,δ} is null); the sibling bf_trichotomy (Lemma 2.4 there); the sibling density_comparison (first part of Lemma 2.3 there: E_{2,δ} has null image); and Eilenberg's inequality (second part of Lemma 2.3 there; Simon Ch. 2, 1.8(ii)), which is proved in step 3(c).

Notation: k := m + 1, Hᵏ := μHE[k], L_v(x) := (⟨v₁,x⟩, …, ⟨v_k,x⟩), and ‖L_v‖ is its operator norm. Lᵏ := volume on ℝᵏ, which equals Hᵏ = μHE[k] on ℝᵏ (Mathlib InnerProductSpace.euclideanHausdorffMeasure_eq_volume; kernel-checked as v2_glue_volume). ℒ := volume on (ℝ^N)^k, the product of the Lebesgue measures. For any S ⊆ ℝ^N and every v, Hᵏ(L_v(S)) ≤ ‖L_v‖ᵏHᵏ(S) (Lipschitz image bound; SimonGMT euclideanHausdorffMeasure_image_le_of_lipschitzOn).

1. Reduction to σ-compact E. μ_E := Hᵏ⌞E is a finite Borel measure on ℝ^N, hence inner regular. So there are compact K₁ ⊆ K₂ ⊆ ⋯ ⊆ E with Hᵏ(E∖⋃_iK_i) = 0. Put E′ := ⋃_iK_i. It is σ-compact and Borel, Hᵏ(E′) < ∞, and E′ is purely k-unrectifiable as a subset of E. For every v, Lᵏ(L_v(E)) ≤ Lᵏ(L_v(E′)) + ‖L_v‖ᵏHᵏ(E∖E′) = Lᵏ(L_v(E′)). So it suffices to treat E′; from now on write E for E′, which is σ-compact.

2. A full-measure set of v. For l ∈ ℕ put δ_l := 1/(l + 1). By the sibling bf_trichotomy with δ := δ_l, there are ℒ-null sets 𝒩_l such that for v ∉ 𝒩_l and Hᵏ-a.e. a ∈ E, at least one of (T1)_l, (T2), (T3)_l holds, where:
 (T1)_l: for every η > 0 there is s ∈ (0,1) with Hᵏ(E ∩ X_v(a,r,s)) ≤ η(rs)ᵏ for all r ∈ (0,δ_l);
 (T2): dimensionalUpperDensity ν_v k univ (L_va) = ∞, with ν_v := (L_v)_#(Hᵏ⌞E);
 (T3)_l: some x ∈ E with x ≠ a and |x − a| < δ_l has L_vx = L_va.
 Let 𝒩 := ⋃_l𝒩_l, an ℒ-null set, and fix v ∉ 𝒩. Taking the countable union of the exceptional null sets, there is Z ⊆ E with Hᵏ(Z) = 0 such that every a ∈ E∖Z satisfies, for every l, (T1)_l or (T2) or (T3)_l.

3. Splitting E. Let E₁^{(l)} := {a ∈ E : (T1)_l}, E₂ := {a ∈ E : (T2)} and E₃ := {a ∈ E : (T3)_l holds for every l}. If a ∈ E∖Z lies neither in E₂ nor in E₃, then (T3)_l fails for some l, so a ∈ E₁^{(l)}. Hence E ⊆ Z ∪ ⋃_lE₁^{(l)} ∪ E₂ ∪ E₃, and L_v(E) ⊆ L_v(Z) ∪ ⋃_lL_v(E₁^{(l)}) ∪ L_v(E₂) ∪ L_v(E₃).
 (a) E₁^{(l)} is exactly the set E₁ of the sibling bf_cone_density for this E, this v and δ := δ_l; its hypotheses hold because E is purely k-unrectifiable. So Hᵏ(E₁^{(l)}) = 0 and Lᵏ(L_v(E₁^{(l)})) ≤ ‖L_v‖ᵏ·0 = 0. Likewise Lᵏ(L_v(Z)) = 0.
 (b) L_v(E₂) ⊆ Y := {y ∈ ℝᵏ : dimensionalUpperDensity ν_v k univ y = ∞}. Apply the sibling density_comparison in ℝᵏ with ν := ν_v, A := Y, V := ℝᵏ and t := ∞. It gives ∞·Hᵏ(Y) ≤ ν_v(ℝᵏ) = Hᵏ(E) < ∞, so Hᵏ(Y) = 0, i.e. Lᵏ(Y) = 0 (kernel-checked as v2_glue_infinite_density).
 (c) Eilenberg's inequality. If a ∈ E₃, the fibre E ∩ L_v^{−1}(L_va) contains, for every l, a point x ≠ a with |x − a| < δ_l, so it is infinite. Hence L_v(E₃) ⊆ Y₃ := {y : #(E ∩ L_v^{−1}(y)) = ∞}.
 For i ∈ ℕ let 𝒬_i be the partition of ℝ^N into half-open dyadic cubes of side 2^{−i}, and let N_i(y) := #{Q ∈ 𝒬_i : y ∈ L_v(E ∩ Q)}. A half-open cube is a countable union of closed cubes, so each E ∩ Q is σ-compact; hence L_v(E ∩ Q) is σ-compact and Borel, and N_i is Borel.
 Each cube of 𝒬_{i+1} lies in exactly one cube of 𝒬_i, so N_i ≤ N_{i+1}. Moreover N_i(y) ↑ #(E ∩ L_v^{−1}(y)) as i → ∞, because finitely many distinct points of the fibre lie in distinct cubes of 𝒬_i once √N·2^{−i} is smaller than their minimal distance.
 By monotone convergence, the Lipschitz image bound, and additivity of Hᵏ on the Borel partition {E ∩ Q : Q ∈ 𝒬_i} of E,
 ∫#(E ∩ L_v^{−1}(y))dLᵏ(y) = lim_iΣ_{Q∈𝒬_i}Lᵏ(L_v(E ∩ Q)) ≤ lim_iΣ_{Q∈𝒬_i}‖L_v‖ᵏHᵏ(E ∩ Q) = ‖L_v‖ᵏHᵏ(E) < ∞.
 Hence Lᵏ(Y₃) = 0, and so Lᵏ(L_v(E₃)) = 0.
 Therefore Lᵏ(L_v(E)) = 0 for every v ∉ 𝒩, i.e. for ℒ-a.e. v. ∎

## Key steps

1. Reduce to σ-compact E by inner regularity; the remaining null part has a null image under every Lipschitz map L_v.
2. Apply bf_trichotomy with δ = 1/(l+1) for every l: for a.e. v, a.e. a ∈ E satisfies, for each l, (T1)_l, (T2) or (T3)_l.
3. Points satisfying some (T1)_l form Hᵏ-null sets by bf_cone_density, so their images are null.
4. Points satisfying (T2) map into the infinite-density set of the finite measure (L_v)_#(Hᵏ⌞E), which is null by density_comparison.
5. Points satisfying (T3)_l for all l have infinite fibres, whose images are null by Eilenberg's inequality (dyadic cubes and monotone convergence).
6. Hence Lᵏ(L_v(E)) = 0 for a.e. v.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean workspaces/gmt-ch06/GMT/Ch06/Contract.lean; cmp Contract.lean Submission.lean (all identical)`
- `rg -n 'theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt|theorem MeasurableSet.image_of_continuousOn_injOn|theorem measurePreserving_homeomorphUnitSphereProd|theorem ae_tendsto_average_norm_sub|theorem exists_disjoint_subfamily_covering_enlargement|theorem haarMeasure_unique|theorem addHaar_image_linearMap' local-references/197bdd4b88278494/mathlib/Mathlib`
- `rg -n 'euclideanHausdorffMeasure_eq_volume|LipschitzOnWith.extend_real|contDiff_convolution_right|LipschitzWith.ae_differentiableAt|toSphere_apply_univ :|theorem ae_tendsto_measure_inter_div|theorem hausdorffMeasure_apply|measure_toMeasurable_inter|hausdorffMeasure_smul₀' local-references/197bdd4b88278494/mathlib/Mathlib`
- `rg -c 'Besicovitch.Federer|purely unrectifiable|PurelyUnrectifiable|Mickle' local-references/197bdd4b88278494/mathlib/Mathlib (no match)`
- `grep -n '^theorem\|^def' simongmt Chapter03/{Rectifiable,SubmanifoldCover}.lean, Chapter02/{AreaLipschitz,AreaCritical,Area,AreaBranches,Lipschitz,BV,WhitneyExtension}.lean, Chapter01/{DensityComparison,HausdorffDensityBounds,HausdorffContentDensity,Lusin,Densities,RadonPolarRepresentation,VectorFunctionalEnvelope}.lean, Chapter06/{Mass,FormsDuality,Currents}.lean`
- `grep -n 'def massOn|def massAdmissibleOn|def covectorEuclideanNorm|abbrev SimonMultiIndex|def HasWeightedApproximateTangentSpaceAt|def PurelyUnrectifiable|def CountablyRectifiable' simongmt Chapter06/Mass.lean, Chapter06/FormsDuality.lean, Chapter03/Rectifiable.lean`
- `sed -n chapter-02.txt 140,330 (Ch.2 1.5-1.8); chapter-03.txt 1,560 (Ch.3 §1 and §3); chapter-06.txt 560,720 and 2130,2300 (2.34-2.37, 8.1)`
- `lake build GMT.Ch06.Submission (scratch /tmp/rect_a1_v2_check, frozen commit d8d46c9, pinned packages lake-packages-25730c7c)`
- `lake env lean Scratch/V2_Names.lean and Scratch/V2_Names2.lean (#check and #print axioms of every cited Mathlib/SimonGMT declaration)`
- `lake env lean Scratch/V2_Challenge.lean (12 child statements generated with verifier/gmt-compare.py contract_scope/child_modules; 0 errors)`
- `lake env lean Scratch/Assembly.lean, Scratch/C4fromC3.lean, Scratch/C5Check.lean, Scratch/V2_Glue.lean (#print axioms)`
- `python3 lean_name collision scan of dag.json and nodes/*/decomposition-v*.json (86 DAG names; no rectifiability_* or mickle_* collision)`
- `python3 audit of nodes/root-rectifiability-a1/decomposition-v1.json and decomposition-audit-v1.json (accepted and rejected children, required changes)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaBranches.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/HausdorffDensityBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/HausdorffContentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonPolarRepresentation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/VectorFunctionalEnvelope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1/decomposition-audit-v1.json`
- `/tmp/rect_a1_v2_check/Scratch/V2_Challenge.lean`
- `/tmp/rect_a1_v2_check/Scratch/V2_Names.lean`
- `/tmp/rect_a1_v2_check/Scratch/V2_Names2.lean`
- `/tmp/rect_a1_v2_check/Scratch/V2_Glue.lean`
- `/tmp/rect_a1_v2_check/Scratch/Assembly.lean`
- `/tmp/rect_a1_v2_check/Scratch/C4fromC3.lean`
- `/tmp/rect_a1_v2_check/Scratch/C5Check.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 contract; it is byte-identical to the workspace Contract and Submission. The pinned Mathlib has no Besicovitch-Federer, purely-unrectifiable or Mickle-Radó result (rg: no match), and SimonGMT has neither BV compactness (Chapter02/BV.lean proves only closure statements) nor the rectifiable-to-C¹ cover (SubmanifoldCover.lean proves only the converse). This confirms the three gaps the v1 audit identified. The pinned libraries do contain every ingredient that the rewritten proofs cite. Mathlib: exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (Jacobian.lean:255), MeasurableSet.image_of_continuousOn_injOn (Polish/Basic.lean:821), LipschitzWith.ae_differentiableAt (Rademacher.lean:385), Measure.measurePreserving_homeomorphUnitSphereProd and toSphere_apply_univ (HaarToSphere.lean), IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub and ae_tendsto_measure_inter_div (DensityTheorem.lean), Besicovitch.ae_tendsto_measure_inter_div, Vitali.exists_disjoint_subfamily_covering_enlargement, Measure.haarMeasure_unique, Measure.addHaar_image_linearMap, hausdorffMeasure_apply, Measure.hausdorffMeasure_smul₀, InnerProductSpace.euclideanHausdorffMeasure_eq_volume, LipschitzOnWith.extend_real, HasCompactSupport.contDiff_convolution_right and hasFDerivAt_convolution_right. SimonGMT: weighted_area_formula_lipschitz_injOn, area_image_criticalSet_eq_zero, linear_area_formula, euclideanHausdorffMeasure_image_le_of_lipschitzOn, simon_theorem_3_3, simon_theorem_3_6, IsBorelRegularOuterMeasure.simon_theorem_1_17, measurable_rectifiable_purelyUnrectifiable_decomposition, countablyRectifiable_range, simon_theorem_4_14_caratheodory and simon_theorem_4_14_positive_envelope. #print axioms gives [propext, Classical.choice, Quot.sound] for all of them. In the scratch build of the frozen project, all 12 child statements elaborate in the comparator's exact child scope (0 errors). Re-run with standard axioms only: the parent assembly from mass_measure_representation, mass_measure_rectifiable and orientation, the C4-from-C3 reduction, the C5 proof, and the glue lemmas v2_glue_rows, v2_glue_volume and v2_glue_infinite_density. The product-measure instance on Fin (m+1) → Eucl N was confirmed by rfl. No proposed lean_name collides with the 86 names in dag.json. These checks certify the statements, the assembly, the glue and the library inputs, not the new analytic proofs; three independent referees reviewed those (all ACCEPT after the minor fixes, which were applied).
