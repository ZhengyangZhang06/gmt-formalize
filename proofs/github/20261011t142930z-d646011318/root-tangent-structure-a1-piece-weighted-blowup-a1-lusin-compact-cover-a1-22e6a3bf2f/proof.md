# Parent-supplied natural-language proof

- Parent DAG node: `root.tangent_structure-a1.piece_weighted_blowup-a1`
- Child DAG node: `root.tangent_structure-a1.piece_weighted_blowup-a1.lusin_compact_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent proof (construction of the Lusin pieces), stated for an arbitrary measure and an arbitrary finite-measure set. In the parent's application A = M ∩ F(C) already has finite Hⁿ-measure (step 2 of the parent proof: Hⁿ(F(C)) ≤ κⁿLⁿ(C) < ∞), so the truncation {θ̃ ≥ 1/q} used there only to obtain finiteness is not needed; the truncation to closed balls B_q(0), which gives compactness, is kept. Lusin's theorem is Simon Ch. 1, 1.17. No errata apply.

Notation. E := Ambient n ℓ (a finite-dimensional normed space, so closed bounded sets are compact), B_q(0) := closed ball of radius q about 0, μ⌞S := μ restricted to S.

1. Borel core of A. Since A is μ-null-measurable, there is a Borel set A' ⊆ A with A' = A μ-almost everywhere (Mathlib NullMeasurableSet.exists_measurable_subset_ae_eq); in particular μ(A ∖ A') = 0.

2. Borel version of g. Since g is a.e.-strongly measurable for μ⌞A, there is a strongly measurable, hence Borel measurable, g̃: E → ℝ with g = g̃ μ⌞A-almost everywhere (AEStronglyMeasurable.mk). The set {y : g(y) ≠ g̃(y)} is therefore μ⌞A-null; let S be its measurable hull with respect to μ⌞A (toMeasurable): S is Borel, contains {g ≠ g̃}, and (μ⌞A)(S) = 0.

3. μ(A' ∩ S) = 0. The set A' ∩ S is Borel and contained in A (A' ⊆ A), so μ(A' ∩ S) = μ((A' ∩ S) ∩ A) = (μ⌞A)(A' ∩ S) ≤ (μ⌞A)(S) = 0.

4. The good set. Let A'' := A' ∖ S. Then A'' is Borel, A'' ⊆ A, and g(y) = g̃(y) for every y ∈ A'' (because y ∉ S ⊇ {g ≠ g̃}). Moreover A ∖ A'' ⊆ (A ∖ A') ∪ (A' ∩ S): a point of A not in A'' either is not in A' or lies in A' ∩ S. By steps 1 and 3, μ(A ∖ A'') = 0.

5. Lusin pieces. Fix q, m ∈ ℕ and put B_q := A'' ∩ B_q(0), a Borel set with μ(B_q) ≤ μ(A) < ∞. The restricted measure ν_q := μ⌞B_q is a finite Borel measure on the metric space E, hence weakly regular (Mathlib WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure); in particular, for every Borel set S' and every δ > 0 there is a closed F ⊆ S' with ν_q(S' ∖ F) < δ (MeasurableSet.exists_isClosed_sdiff_lt). This is exactly the regularity hypothesis of Lusin's theorem in the form SimonGMT Chapter01.exists_isClosed_continuousOn_of_measurable, which we apply to the measure ν_q, the Borel set B_q (ν_q(B_q) < ∞), the Borel function g̃ and ε := 1/(m + 1) > 0: there is a closed set C_{q,m} ⊆ B_q with ν_q(B_q ∖ C_{q,m}) < 1/(m + 1) such that g̃ restricted to C_{q,m} is continuous. Since B_q ∖ C_{q,m} is Borel and contained in B_q, ν_q(B_q ∖ C_{q,m}) = μ(B_q ∖ C_{q,m}); thus μ(B_q ∖ C_{q,m}) < 1/(m + 1).

6. Properties of the pieces. C_{q,m} is closed and contained in the compact ball B_q(0), hence compact. C_{q,m} ⊆ B_q ⊆ A'' ⊆ A. Since g = g̃ on A'' ⊇ C_{q,m}, the restriction of g to C_{q,m} coincides with that of g̃, so g restricted to C_{q,m} is continuous.

7. Covering. For each q ∈ ℕ and every m ∈ ℕ, μ(B_q ∖ ⋃_{m'} C_{q,m'}) ≤ μ(B_q ∖ C_{q,m}) < 1/(m + 1); letting m → ∞ gives μ(B_q ∖ ⋃_{m'} C_{q,m'}) = 0. Now let y ∈ A ∖ ⋃_{q,m} C_{q,m}. If y ∉ A'', then y ∈ A ∖ A''. If y ∈ A'', choose q ∈ ℕ with q ≥ |y|; then y ∈ B_q and y ∉ ⋃_{m} C_{q,m}. Hence A ∖ ⋃_{q,m} C_{q,m} ⊆ (A ∖ A'') ∪ ⋃_{q∈ℕ} (B_q ∖ ⋃_m C_{q,m}), a countable union of μ-null sets (step 4 and the first sentence of this step), so μ(A ∖ ⋃_{q,m} C_{q,m}) = 0.

8. Indexing by ℕ. For k ∈ ℕ let K_k := C_{q,m} with (q, m) := Nat.unpair k. Each K_k is one of the sets C_{q,m}, so it is compact, contained in A, and g restricted to K_k is continuous (step 6). Every C_{q,m} equals K_{Nat.pair q m} because Nat.unpair (Nat.pair q m) = (q, m); hence ⋃_{q,m} C_{q,m} ⊆ ⋃_k K_k and μ(A ∖ ⋃_k K_k) ≤ μ(A ∖ ⋃_{q,m} C_{q,m}) = 0. ∎

Implementation note (not part of the mathematical argument): during the decomposition the following Lean proof of exactly the frozen statement was compiled without errors, placed in the frozen contract scope (after `open MeasureTheory Metric Set Filter Topology`, `open scoped ENNReal ContDiff CompactlySupported`, inside `namespace GMT.Ch04`, `noncomputable section`, `open RectifiableVarifold`, and `namespace Submission`) of a file importing `GMT.Ch04.Submission`, `Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace`, `Poincare.SimonGMT.Chapter01.DensityComparison`, `Poincare.SimonGMT.Chapter01.Lusin` and `Poincare.SimonGMT.Chapter02.AreaLiteral` (pinned Lean v4.35.0-rc3, Mathlib 25730c7c, SimonGMT 2b36630); `#print axioms` reports only propext, Classical.choice and Quot.sound. It follows the numbered argument above and may be reused verbatim.

```lean
theorem ts_pwb_lusin_compact_cover : ∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (A : Set (Ambient n ℓ)) (g : Ambient n ℓ → ℝ), NullMeasurableSet A μ → μ A ≠ ⊤ → AEStronglyMeasurable g (μ.restrict A) → ∃ K : ℕ → Set (Ambient n ℓ), (∀ k, IsCompact (K k) ∧ K k ⊆ A ∧ ContinuousOn g (K k)) ∧ μ (A \ ⋃ k, K k) = 0 := by
  intro n ℓ μ A g hA hAfin hg
  obtain ⟨A', hA'A, hA'm, hA'eq⟩ := hA.exists_measurable_subset_ae_eq
  have hdiff1 : μ (A \ A') = 0 := (ae_eq_set.1 hA'eq).2
  set g' := hg.mk g with hg'_def
  have hg'm : Measurable g' := hg.stronglyMeasurable_mk.measurable
  have hgg' : g =ᵐ[μ.restrict A] g' := hg.ae_eq_mk
  set S := toMeasurable (μ.restrict A) {y | g y ≠ g' y} with hS_def
  have hSm : MeasurableSet S := measurableSet_toMeasurable _ _
  have hS0 : μ.restrict A S = 0 := by
    rw [hS_def, measure_toMeasurable]
    exact hgg'
  have hsub : {y | g y ≠ g' y} ⊆ S := subset_toMeasurable _ _
  have hA'S : μ (A' ∩ S) = 0 := by
    have h1 : μ.restrict A (A' ∩ S) = μ (A' ∩ S) := by
      rw [Measure.restrict_apply (hA'm.inter hSm)]
      congr 1
      ext y
      simp only [mem_inter_iff]
      constructor
      · rintro ⟨h, -⟩
        exact h
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, h2⟩, hA'A h1⟩
    rw [← h1]
    exact measure_mono_null inter_subset_right hS0
  set A'' := A' \ S with hA''_def
  have hA''m : MeasurableSet A'' := hA'm.diff hSm
  have hA''A : A'' ⊆ A := sdiff_subset.trans hA'A
  have hgeq : ∀ y ∈ A'', g y = g' y := fun y hy ↦ by
    by_contra h
    exact hy.2 (hsub h)
  have hAA'' : μ (A \ A'') = 0 := by
    refine measure_mono_null (t := (A \ A') ∪ (A' ∩ S)) ?_ (measure_union_null hdiff1 hA'S)
    intro y ⟨hyA, hy⟩
    by_cases h : y ∈ A'
    · exact Or.inr ⟨h, by
        by_contra hS
        exact hy ⟨h, hS⟩⟩
    · exact Or.inl ⟨hyA, h⟩
  have hpiece : ∀ q m : ℕ, ∃ Cqm : Set (Ambient n ℓ),
      Cqm ⊆ A'' ∩ closedBall 0 q ∧ IsClosed Cqm ∧
        μ ((A'' ∩ closedBall 0 q) \ Cqm) < ((m : ℝ≥0∞) + 1)⁻¹ ∧ ContinuousOn g' Cqm := by
    intro q m
    set B := A'' ∩ closedBall (0 : Ambient n ℓ) q with hB_def
    have hBm : MeasurableSet B := hA''m.inter measurableSet_closedBall
    have : IsFiniteMeasure (μ.restrict B) := isFiniteMeasure_restrict.2
      (ne_top_of_le_ne_top hAfin (measure_mono (inter_subset_left.trans hA''A)))
    obtain ⟨Cqm, hCB, hCc, hCsmall, hCcont⟩ :=
      Poincare.SimonGMT.Chapter01.exists_isClosed_continuousOn_of_measurable (μ.restrict B)
        (fun S hS hSfin δ hδ ↦ hS.exists_isClosed_sdiff_lt hSfin hδ) hBm (measure_ne_top _ _)
        hg'm (ε := ((m : ℝ≥0∞) + 1)⁻¹) (by simp)
    refine ⟨Cqm, hCB, hCc, ?_, hCcont⟩
    rwa [Measure.restrict_apply (hBm.diff hCc.measurableSet),
      inter_eq_left.2 sdiff_subset] at hCsmall
  choose Cf hCsub hCclosed hCsmall hCcont using hpiece
  refine ⟨fun k ↦ Cf (Nat.unpair k).1 (Nat.unpair k).2, fun k ↦ ⟨?_, ?_, ?_⟩, ?_⟩
  · exact (isCompact_closedBall (0 : Ambient n ℓ) _).of_isClosed_subset (hCclosed _ _)
      ((hCsub _ _).trans inter_subset_right)
  · exact (hCsub _ _).trans (inter_subset_left.trans hA''A)
  · exact (hCcont _ _).congr fun y hy ↦ hgeq y (hCsub _ _ hy).1
  · have hq : ∀ q : ℕ, μ ((A'' ∩ closedBall 0 q) \ ⋃ m, Cf q m) = 0 := by
      intro q
      refine le_antisymm (le_of_forall_pos_le_add fun ε hε ↦ ?_) bot_le
      obtain ⟨m, hm⟩ := ENNReal.exists_inv_nat_lt hε.ne'
      rw [zero_add]
      calc μ ((A'' ∩ closedBall 0 q) \ ⋃ m, Cf q m) ≤ μ ((A'' ∩ closedBall 0 q) \ Cf q m) :=
            measure_mono (sdiff_subset_sdiff_right (subset_iUnion _ m))
        _ ≤ ((m : ℝ≥0∞) + 1)⁻¹ := (hCsmall q m).le
        _ ≤ (m : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
        _ ≤ ε := hm.le
    refine measure_mono_null (t := (A \ A'') ∪ ⋃ q : ℕ, ((A'' ∩ closedBall 0 q) \ ⋃ m, Cf q m))
      ?_ (measure_union_null hAA'' (measure_iUnion_null hq))
    intro y ⟨hyA, hy⟩
    by_cases h : y ∈ A''
    · right
      obtain ⟨q, hq⟩ := exists_nat_ge ‖y‖
      refine mem_iUnion.2 ⟨q, ⟨h, by simpa using hq⟩, ?_⟩
      intro hyU
      obtain ⟨m, hm⟩ := mem_iUnion.1 hyU
      exact hy (mem_iUnion.2 ⟨Nat.pair q m, by simpa using hm⟩)
    · exact Or.inl ⟨hyA, h⟩
```

## Key steps

1. Borel A' ⊆ A with μ(A ∖ A') = 0; Borel g̃ = g μ⌞A-a.e.; Borel S ⊇ {g ≠ g̃} with (μ⌞A)(S) = 0
2. μ(A' ∩ S) = (μ⌞A)(A' ∩ S) = 0, so A'' := A' ∖ S is Borel, g = g̃ on A'', and μ(A ∖ A'') = 0
3. For q, m: μ⌞(A'' ∩ B_q(0)) is a finite, hence weakly regular, Borel measure; Lusin's theorem gives closed C_{q,m} ⊆ A'' ∩ B_q(0) with μ-defect < 1/(m+1) and g̃ continuous on C_{q,m}
4. C_{q,m} is compact (closed and bounded), lies in A, and g = g̃ is continuous on it
5. A ∖ ⋃ C_{q,m} ⊆ (A ∖ A'') ∪ ⋃_q (A'' ∩ B_q(0) ∖ ⋃_m C_{q,m}) is μ-null; reindex by Nat.unpair

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json`
- `sha256sum GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean <snapshot>/project/GMT/Ch04/Contract.lean`
- `git -C .lake/packages/simongmt rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD`
- `python3: list dag.json nodes (id, status, lean_name, lean_statement) for name-collision and reuse checks`
- `grep -rn 'theorem ae_dimensionalUpperDensity_eq_zero_outside|theorem measure_toOuterMeasure_isBorelRegular|theorem simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure|theorem exists_isClosed_continuousOn_of_measurable|theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn|def dimensionalUpperDensity|def realUnitBallVolume' .lake/packages/simongmt/Poincare/`
- `grep -rn 'def IsOpenSigmaFinite|def IsCaratheodoryMeasurable|realUnitBallVolume_pos|realUnitBallVolume_ne_top' .lake/packages/simongmt/Poincare/SimonGMT`
- `rg -n 'theorem ae_tendsto_measure_inter_div|theorem integral_withDensity_eq_integral_toReal_smul₀|theorem ae_restrict_mem₀|exists_isClosed_sdiff_lt|euclideanHausdorffMeasure_eq_volume' <snapshot>/mathlib/Mathlib`
- `rg -n 'measure_eq_zero_iff_ae_notMem|ae_all_iff|ae_restrict_of_ae|isFiniteMeasure_restrict|aestronglyMeasurable_iUnion_iff|of_pseudoMetrizableSpace_of_isFiniteMeasure|exists_measurable_subset_ae_eq|tendsto_of_liminf_eq_limsup|ofReal_le_enorm' <snapshot>/mathlib/Mathlib`
- `rg -n 'integral_inter_add_sdiff|setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|IntegrableOn.of_ae_sdiff_eq_zero|Integrable.mul_bdd|IntegrableOn.of_bound|norm_setIntegral_le_of_norm_le_const|setIntegral_indicator|lt_inv_mul_iff₀|bounded_above_of_compact_support' <snapshot>/mathlib/Mathlib`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/pwb-decomp/olean/GMT/Ch04/Submission.olean`
- `python3 /tmp/pwb-decomp/scripts/gen.py (verifier gmt-compare.child_modules + lean_contract.validate_lean_statement); lean /tmp/pwb-decomp/gen/Challenge_*.lean`
- `lean /tmp/pwb-decomp/inst/Plain.lean and /tmp/pwb-decomp/inst/WithImports.lean (pp.all) then diff`
- `lean /tmp/pwb-decomp/asm/Assembly.lean (parent from sorry'd children and sibling)`
- `lean /tmp/pwb-decomp/probe/Full.lean and /tmp/pwb-decomp/out/Verify.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-weighted-blowup-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-weighted-blowup-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-weighted-blowup-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-density-blowup-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Normed/Group/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean`
- `/tmp/pwb-decomp/gen/Challenge_ts_pwb_pair_weight_integral.lean`
- `/tmp/pwb-decomp/gen/Challenge_ts_pwb_upper_density_vanish_ae.lean`
- `/tmp/pwb-decomp/gen/Challenge_ts_pwb_lusin_compact_cover.lean`
- `/tmp/pwb-decomp/gen/Challenge_ts_pwb_density_points_of_image_ae.lean`
- `/tmp/pwb-decomp/gen/Challenge_ts_pwb_blowup_at_good_point.lean`
- `/tmp/pwb-decomp/inst/Plain.lean`
- `/tmp/pwb-decomp/inst/WithImports.lean`
- `/tmp/pwb-decomp/asm/Assembly.lean`
- `/tmp/pwb-decomp/probe/Full.lean`
- `/tmp/pwb-decomp/out/Verify.lean`

Snapshot and pins:
- The snapshot contract, the workspace Contract.lean and the workspace Submission.lean are byte-identical (sha256 6e58e5dd…0f4770b).
- simongmt is at the pinned 2b3663083f3fe399b6296fb8eaee52169170e197 and mathlib at 25730c7c759d108ef87ab70af2342a196760f79d, as in the manifest.

Library results used by the children (each exists with the stated meaning; every child built on them prints only propext, Classical.choice, Quot.sound):
- SimonGMT (Chapter01/02): ae_dimensionalUpperDensity_eq_zero_outside (Simon 1.3.6), measure_toOuterMeasure_isBorelRegular, realUnitBallVolume_pos and realUnitBallVolume_ne_top, dimensionalDensityQuotient (closed balls), exists_isClosed_continuousOn_of_measurable (Lusin 1.17), euclideanHausdorffMeasure_image_le_of_lipschitzOn, simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure.
- Mathlib snapshot: Besicovitch.ae_tendsto_measure_inter_div, integral_withDensity_eq_integral_toReal_smul₀, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure, MeasurableSet.exists_isClosed_sdiff_lt, NullMeasurableSet.exists_measurable_subset_ae_eq, aestronglyMeasurable_iUnion_iff, ae_restrict_mem₀, tendsto_of_liminf_eq_limsup, integral_inter_add_sdiff, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, IntegrableOn.of_ae_sdiff_eq_zero, norm_setIntegral_le_of_norm_le_const.
- The Mathlib snapshot has no Lusin theorem, so the SimonGMT one is used.
- No existing DAG declaration matches any child type. The accepted lusin_compact_exhaustion_of_measurable concerns volume on ℝⁿ.

Elaboration checks:
- All five child types elaborate in comparator-generated challenge files.
- They are unchanged (pp.all byte-identical) when the implementation imports are added.
- The parent's frozen type is proved from them plus the sibling (Assembly.lean).
- All five children are fully proved (Full.lean, Verify.lean).
