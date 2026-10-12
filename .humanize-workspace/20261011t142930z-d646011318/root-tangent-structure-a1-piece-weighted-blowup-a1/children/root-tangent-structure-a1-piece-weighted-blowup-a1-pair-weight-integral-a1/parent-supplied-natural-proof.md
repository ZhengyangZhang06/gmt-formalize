# Parent-supplied natural-language proof

- Parent DAG node: `root.tangent_structure-a1.piece_weighted_blowup-a1`
- Child DAG node: `root.tangent_structure-a1.piece_weighted_blowup-a1.pair_weight_integral-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 of the parent proof (Simon Ch. 4, 1.1: μ_V = Hⁿ⌞θ), with all details filled in. No errata apply.

Notation. E := Ambient n ℓ, Hⁿ := μHE[n] on E, B_k(0) := closed ball of radius k about 0, ofReal(s) := max(s, 0) ∈ [0, ∞) for s ∈ ℝ, μ := (mk a).weight, M := a.M, θ := a.θ.

1. Unfolding the weight. By definition (mk a).weight = Quot.lift (b ↦ pairWeight n b.M b.θ) _ (Quot.mk _ a), and Quot.lift applied to Quot.mk a reduces definitionally to the lifted function at a. Hence μ = pairWeight n M θ = (Hⁿ⌞M).withDensity ρ with ρ(y) := ofReal(θ(y)) ∈ [0, ∞).

2. θ is a.e.-strongly measurable for Hⁿ⌞M. Every y ∈ E lies in B_k(0) for every k ∈ ℕ with k ≥ |y|, so M = ⋃_{k∈ℕ} (M ∩ B_k(0)). For each k the ball B_k(0) is compact, so by admissibility θ is Hⁿ-integrable on M ∩ B_k(0); in particular θ is a.e.-strongly measurable for Hⁿ⌞(M ∩ B_k(0)). A function that is a.e.-strongly measurable for the restrictions of a measure to each of countably many sets is a.e.-strongly measurable for the restriction to their union (Mathlib aestronglyMeasurable_iUnion_iff). Hence θ is a.e.-strongly measurable, in particular a.e.-measurable, for Hⁿ⌞M; therefore ρ = ofReal ∘ θ is a.e.-measurable for Hⁿ⌞M (ofReal is measurable), and ρ(y) < ∞ for every y.

3. Proof of (i). Let K ⊆ E be compact; K is closed, hence Borel. By the formula for withDensity on measurable sets (withDensity_apply) and Measure.restrict_restrict, μ(K) = ∫⁻_K ρ d(Hⁿ⌞M) = ∫⁻_{K∩M} ofReal(θ) dHⁿ. Since ofReal(s) ≤ |s| for every real s, μ(K) ≤ ∫⁻_{K∩M} |θ| dHⁿ, and the right side is finite because θ is Hⁿ-integrable on M ∩ K = K ∩ M (admissibility with the compact set K). Thus μ(K) < ∞ for every compact K, i.e. μ is finite on compact sets.

4. A general identity. For a measure ν, a ν-a.e.-measurable density ρ: E → [0, ∞] with ρ < ∞ ν-a.e., and an arbitrary function h: E → ℝ, one has ∫ h d(ν.withDensity ρ) = ∫ ρ(y).toReal·h(y) dν(y) (Mathlib integral_withDensity_eq_integral_toReal_smul₀). This identity includes the fact that h is ν.withDensity ρ-integrable if and only if (ρ.toReal)·h is ν-integrable, so it is also valid when both Bochner integrals are 0 by the non-integrability convention.

5. Proof of (ii). Let g: E → ℝ be arbitrary. By step 1 and step 4 with ν := Hⁿ⌞M and the density ρ = ofReal ∘ θ (admissible by step 2): ∫ g dμ = ∫ (ofReal θ(y)).toReal·g(y) d(Hⁿ⌞M)(y).

6. Since M is Hⁿ-null-measurable, Hⁿ⌞M-almost every y lies in M (Mathlib ae_restrict_mem₀). For y ∈ M we have θ(y) > 0, hence (ofReal θ(y)).toReal = θ(y). So the integrands (ofReal θ(y)).toReal·g(y) and θ(y)·g(y) agree Hⁿ⌞M-almost everywhere, and their integrals with respect to Hⁿ⌞M coincide (integral_congr_ae). Therefore ∫ g dμ = ∫_M θ(y)·g(y) dHⁿ(y), which is (ii). ∎

Implementation note (not part of the mathematical argument): during the decomposition the following Lean proof of exactly the frozen statement was compiled without errors, placed in the frozen contract scope (after `open MeasureTheory Metric Set Filter Topology`, `open scoped ENNReal ContDiff CompactlySupported`, inside `namespace GMT.Ch04`, `noncomputable section`, `open RectifiableVarifold`, and `namespace Submission`) of a file importing `GMT.Ch04.Submission`, `Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace`, `Poincare.SimonGMT.Chapter01.DensityComparison`, `Poincare.SimonGMT.Chapter01.Lusin` and `Poincare.SimonGMT.Chapter02.AreaLiteral` (pinned Lean v4.35.0-rc3, Mathlib 25730c7c, SimonGMT 2b36630); `#print axioms` reports only propext, Classical.choice and Quot.sound. It follows the numbered argument above and may be reused verbatim.

```lean
theorem ts_pwb_pair_weight_integral : ∀ (n ℓ : ℕ) (a : RectifiablePair n ℓ), IsFiniteMeasureOnCompacts (mk a).weight ∧ ∀ g : Ambient n ℓ → ℝ, ∫ y, g y ∂(mk a).weight = ∫ y in a.M, a.θ y * g y ∂μHE[n] := by
  intro n ℓ a
  have hM := a.isRectifiablePair.measurable
  have hθ : AEStronglyMeasurable a.θ ((μHE[n] : Measure (Ambient n ℓ)).restrict a.M) := by
    have hU : a.M = ⋃ k : ℕ, a.M ∩ closedBall (0 : Ambient n ℓ) k := by
      ext y
      simp only [mem_iUnion, mem_inter_iff, mem_closedBall, dist_zero_right]
      constructor
      · intro hy
        obtain ⟨k, hk⟩ := exists_nat_ge ‖y‖
        exact ⟨k, hy, hk⟩
      · rintro ⟨k, hy, -⟩
        exact hy
    rw [hU, aestronglyMeasurable_iUnion_iff]
    intro k
    exact (a.isRectifiablePair.locallyIntegrable _ (isCompact_closedBall _ _)).aestronglyMeasurable
  have hw : (mk a).weight = ((μHE[n] : Measure (Ambient n ℓ)).restrict a.M).withDensity
      (fun x ↦ ENNReal.ofReal (a.θ x)) := rfl
  refine ⟨⟨fun K hK ↦ ?_⟩, fun g ↦ ?_⟩
  · rw [hw, withDensity_apply _ hK.measurableSet, Measure.restrict_restrict hK.measurableSet]
    have hint := a.isRectifiablePair.locallyIntegrable K hK
    rw [inter_comm] at hint
    calc ∫⁻ x in K ∩ a.M, ENNReal.ofReal (a.θ x) ∂μHE[n]
        ≤ ∫⁻ x in K ∩ a.M, ‖a.θ x‖ₑ ∂μHE[n] := lintegral_mono fun x ↦ Real.ofReal_le_enorm _
      _ < ⊤ := hint.2
  · rw [hw, integral_withDensity_eq_integral_toReal_smul₀
      (f := fun x ↦ ENNReal.ofReal (a.θ x))
      (ENNReal.measurable_ofReal.comp_aemeasurable hθ.aemeasurable)
      (Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem₀ hM] with y hy
    simp [ENNReal.toReal_ofReal (a.isRectifiablePair.pos y hy).le]
```

## Key steps

1. (mk a).weight is definitionally (Hⁿ⌞M).withDensity(ofReal ∘ θ)
2. θ is a.e.-strongly measurable for Hⁿ⌞M: M = ⋃_k (M ∩ B_k(0)) and θ is integrable on each M ∩ B_k(0)
3. For compact K: μ(K) = ∫⁻_{K∩M} ofReal θ dHⁿ ≤ ∫⁻_{M∩K} |θ| dHⁿ < ∞
4. ∫ g d(ν.withDensity ρ) = ∫ ρ.toReal·g dν for every g (integral_withDensity_eq_integral_toReal_smul₀)
5. Hⁿ⌞M-a.e. y lies in M, where (ofReal θ(y)).toReal = θ(y); conclude ∫ g dμ = ∫_M θg dHⁿ

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
