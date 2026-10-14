# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`
- Child DAG node: `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.lusin_covector-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4(a) of the parent proof, which cites Lusin's theorem (Simon Ch. 1, 1.17). Lusin's continuity theorem is not in the pinned Mathlib, which has only the Lusin–Souslin and Lusin separation theorems. So the standard proof is given, in the compact, vector-valued form used by the parent.
Notation: Λ := Covector (Euclid P) n is a finite-dimensional real normed space, hence a separable metric space with a countable basis of open sets. Give Λ its Borel σ-algebra.
1. (Measurable modification.) Since f is μ-a.e. strongly measurable, there is a strongly measurable f' with f = f' μ-a.e. f' is a pointwise limit of simple functions with values in the metrizable space Λ, so it is Borel measurable. The set {f ≠ f'} is μ-null, so it lies in a measurable μ-null set Z (exists_measurable_superset_of_null). Put A₀ := A ∖ Z. Then A₀ ⊆ A is measurable, μ(A ∖ A₀) ≤ μ(Z) = 0, and f = f' on A₀.
2. (Inner regularity.) ν := μ.restrict A₀ is a finite Borel measure on ℝ^P, since ν(ℝ^P) = μ(A₀) ≤ μ(A) < ∞. ℝ^P is a Polish space, so ν is inner regular by compact sets (Ulam's theorem; in Mathlib, finite measures on completely metrizable second-countable spaces are InnerRegular, see MeasureTheory/Measure/RegularityCompacts.lean). Hence for every measurable B ⊆ A₀ and η > 0 there is a compact C ⊆ B with μ(B ∖ C) = ν(B ∖ C) < η.
3. (Compact pieces.) Let (O_k)_{k∈ℕ} be a countable basis of the topology of Λ, and S_k := f'^{-1}(O_k), which is measurable. By step 2 choose compact sets C_k ⊆ A₀ ∩ S_k and D_k ⊆ A₀ ∖ S_k with
 μ((A₀ ∩ S_k) ∖ C_k) < ε·2^{−k−3} and μ((A₀ ∖ S_k) ∖ D_k) < ε·2^{−k−3}.
 Let E_k := C_k ∪ D_k, a compact subset of A₀. Since A₀ ∖ E_k ⊆ ((A₀ ∩ S_k) ∖ C_k) ∪ ((A₀ ∖ S_k) ∖ D_k), μ(A₀ ∖ E_k) < ε·2^{−k−2}.
4. (The compact set.) K := ⋂_k E_k is closed and contained in the compact set E_0, so K is compact, and K ⊆ A₀ ⊆ A. As A ∖ K ⊆ (A ∖ A₀) ∪ ⋃_k (A₀ ∖ E_k), countable subadditivity gives μ(A ∖ K) ≤ 0 + Σ_k ε·2^{−k−2} = ε/2 < ε.
5. (Continuity.) Fix k.
 - If x ∈ K and f'(x) ∈ O_k, then x ∈ S_k, so x ∉ D_k because D_k ∩ S_k = ∅.
 - Conversely, if x ∈ K ∖ D_k, then x ∈ E_k ∖ D_k ⊆ C_k ⊆ S_k.
 Hence K ∩ f'^{-1}(O_k) = K ∖ D_k, which is relatively open in K because D_k is closed. Since (O_k) is a basis, the restriction f'|_K is continuous (IsTopologicalBasis.continuous_iff on the subtype K). As f = f' on K ⊆ A₀, f is continuous on K, i.e. ContinuousOn f K.

## Key steps

1. Replace f by a Borel modification f' and remove a measurable null set Z: A₀ = A ∖ Z.
2. μ restricted to A₀ is a finite Borel measure on the Polish space ℝ^P, hence inner regular by compact sets.
3. For a countable basis (O_k) of Λⁿ, choose compact C_k ⊆ A₀ ∩ f'^{-1}O_k and D_k ⊆ A₀ ∖ f'^{-1}O_k with defects < ε·2^{−k−3}.
4. K = ⋂_k (C_k ∪ D_k) is compact, K ⊆ A, and μ(A ∖ K) ≤ ε/2.
5. K ∩ f'^{-1}O_k = K ∖ D_k is relatively open in K, so f = f' is continuous on K.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n -i lusin <snapshot>/mathlib/Mathlib (also -l)`
- `rg -n 'TietzeExtension' <snapshot>/mathlib/Mathlib (Topology/TietzeExtension.lean, Analysis/Complex/Tietze.lean)`
- `rg -n 'exists_hasCompactSupport_integral_sub_le|exists_hasCompactSupport_eLpNorm_sub_le' <snapshot>/mathlib/Mathlib`
- `rg -n 'dist_normed_convolution_le|convolution_tendsto_right' <snapshot>/mathlib/Mathlib`
- `rg -n 'instance.*Regular|InnerRegularCompactLTTop' Mathlib/MeasureTheory/Measure/Regular.lean Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`
- `sed -n 1,80p Mathlib/MeasureTheory/Measure/Support.lean | rg 'def|theorem|lemma' (Measure.support, mem_support_iff_forall)`
- `rg -n 'exists_cthickening_subset_open|closure_eq_iInter_thickening|cthickening_eq_iInter_thickening' Mathlib/Topology/MetricSpace/Thickening.lean`
- `rg -n 'le_of_forall_nnreal_lt|le_of_forall_pos_le_add' Mathlib/Basic/ENNReal`
- `rg -n 'integral_indicator_one|integral_withDensity_eq_integral_smul|withDensity_absolutelyContinuous|exists_measurable_superset_of_null|AbsolutelyContinuous.ae_le|comp_aestronglyMeasurable₂|image_eq_zero_of_notMem_tsupport' <snapshot>/mathlib/Mathlib`
- `rg -n 'covectorEuclideanNorm' lake-packages-25730c7c/simongmt/Poincare/SimonGMT; rg -n '^(theorem|lemma|def|abbrev) ' Chapter06/{WedgeForms,FormsDuality,GeometricPointProduct,Representation}.lean`
- `grep -rln FormsDuality simongmt (not imported by the Ch07 contract)`
- `grep dor_ims_{unitOrientation_dual,action_eq_integral,massOn_le_measure,lusin_continuousOn,smooth_unit_approx,measure_le_massOn,support_of_massOn_eq} in dag.json, simongmt/Poincare, GMT/, mathlib/Mathlib (no match)`
- `lake env lean /tmp/imrep-ms-decomp/Parent.lean; Children.lean; Sanity.lean; C2Check.lean; C4Skeleton.lean; final/Final.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-imrep-mass-formula-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-support-eq-measure-support-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-vanish-off-support-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/TietzeExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Complex/Tietze.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/tmp/imrep-ms-decomp/final/Final.lean`
- `/tmp/imrep-ms-decomp/final/statements.json`
- `/tmp/imrep-ms-decomp/C2Check.lean`
- `/tmp/imrep-ms-decomp/Sanity.lean`
- `/tmp/imrep-ms-decomp/C4Skeleton.lean`

Snapshot: project b4d606d, mathlib 25730c7c. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

Reusable facts found:
- SimonGMT Chapter06/Mass.lean: covectorEuclideanNorm, massAdmissibleOn, GeometricCurrentOn.massOn and le_massOn.
- Chapter06/CurrentLocalEquality.lean: VanishesOn, zeroRegion and support (spt T = U ∖ zeroRegion).
- Chapter06/FormsDuality.lean: wedgeCovectors and wedgeCovectors_apply_det give the coordinate covectors dx^I and the frame covector δ_τ used in the Cauchy–Binet child. The module is not imported by the Ch07 contract, so it must be imported in Submission.
- Mathlib: Measure.mem_support_iff_forall; finite measures on completely metrizable spaces are InnerRegular (RegularityCompacts.lean); Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure.
- Mathlib Tietze: ContinuousMap.exists_restrict_eq with RCLike.instTietzeExtensionTVS for finite-dimensional real spaces.
- Mathlib bump functions: ContDiffBump.dist_normed_convolution_le and convolution_tendsto_right_of_continuous.
- Mathlib Integrable.exists_hasCompactSupport_integral_sub_le (not needed on the chosen route).
- Mathlib measure and topology API: IsCompact.exists_cthickening_subset_open, tendsto_measure_iUnion_atTop, tendsto_measure_iInter_atTop, ENNReal.le_of_forall_nnreal_lt, integral_withDensity_eq_integral_smul, integral_indicator_one, Continuous.comp_aestronglyMeasurable₂ (with isBoundedBilinearMap_apply.continuous).

Not available:
- Lusin's continuity theorem. Only Lusin–Souslin and Lusin separation are present (Polish/Basic.lean), so it becomes the child lusin_covector.
- The mass formula M_W(T) = μ_T(W) for the contract's Euclidean coefficient norm. Chapter06/Representation.lean has only the assumed comass MassRepresentation field.
- A Cauchy–Binet / exterior-power coefficient expansion for continuous alternating maps.

Lean checks:
- All seven exact child types elaborate in the comparator scope, and `exact Submission.X` closes each.
- The parent assembly from C3, C4 and C5 type-checks, with sorryAx only from the stubs.
- C2 and C5 are fully proved with propext, Classical.choice and Quot.sound only.
- C3 is proved from the C1 and C2 types.
- C4 is proved from the types of C1, C2, Lusin and the smooth approximation.
- The seven dor_ims_* names have no matches anywhere.
