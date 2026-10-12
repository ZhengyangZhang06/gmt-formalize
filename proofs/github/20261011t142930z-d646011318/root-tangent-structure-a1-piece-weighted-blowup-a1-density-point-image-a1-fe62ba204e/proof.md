# Parent-supplied natural-language proof

- Parent DAG node: `root.tangent_structure-a1.piece_weighted_blowup-a1`
- Child DAG node: `root.tangent_structure-a1.piece_weighted_blowup-a1.density_point_image-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the parent proof (density points; Lebesgue density theorem and the Lipschitz image estimate). No errata apply.

Notation. ℝⁿ := EuclideanSpace ℝ (Fin n) with Lebesgue measure Lⁿ = volume; E := Ambient n ℓ; Hⁿ := μHE[n] on E; B_r(w) := closed ball; for w ∈ ℝⁿ let q_w(r) := Lⁿ(C ∩ B_r(w))/Lⁿ(B_r(w)) ∈ [0, ∞].

1. Lebesgue density theorem. ℝⁿ is a finite-dimensional normed space, so it has the Besicovitch covering property, and Lⁿ is locally finite. By Mathlib Besicovitch.ae_tendsto_measure_inter_div (with the measure Lⁿ and the set C), for Lⁿ⌞C-almost every w, q_w(r) → 1 as r ↓ 0.

2. The non-density points are Lⁿ-null. Let P := {w ∈ ℝⁿ : q_w(r) does not tend to 1 as r ↓ 0} and Z := P ∩ C. Step 1 says (Lⁿ⌞C)(P) = 0. Since C is Borel, (Lⁿ⌞C)(P) = Lⁿ(P ∩ C) (Measure.restrict_apply'), so Lⁿ(Z) = 0.

3. Their image is Hⁿ-null. Let κ ≥ 0 be a Lipschitz constant of F. By the Lipschitz image estimate for Hausdorff measure (Simon Ch. 2, 1.8(i); SimonGMT Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn, applied to F, which is κ-Lipschitz on Z), Hⁿ(F(Z)) ≤ κⁿ·μHE[n](Z), where μHE[n] on ℝⁿ equals Lⁿ (Mathlib EuclideanSpace.euclideanHausdorffMeasure_eq_volume). Hence Hⁿ(F(Z)) ≤ κⁿ·Lⁿ(Z) = 0.

4. Conclusion. Suppose x ∈ E violates the conclusion, i.e. there is w ∈ C with F(w) = x such that q_w(r) does not tend to 1. Then w ∈ P ∩ C = Z, so x = F(w) ∈ F(Z). Hence the set of points violating the conclusion is contained in the Hⁿ-null set F(Z) (it need not be measurable; it is contained in a null set), and the conclusion holds for Hⁿ-almost every x ∈ E. ∎

Implementation note (not part of the mathematical argument): during the decomposition the following Lean proof of exactly the frozen statement was compiled without errors, placed in the frozen contract scope (after `open MeasureTheory Metric Set Filter Topology`, `open scoped ENNReal ContDiff CompactlySupported`, inside `namespace GMT.Ch04`, `noncomputable section`, `open RectifiableVarifold`, and `namespace Submission`) of a file importing `GMT.Ch04.Submission`, `Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace`, `Poincare.SimonGMT.Chapter01.DensityComparison`, `Poincare.SimonGMT.Chapter01.Lusin` and `Poincare.SimonGMT.Chapter02.AreaLiteral` (pinned Lean v4.35.0-rc3, Mathlib 25730c7c, SimonGMT 2b36630); `#print axioms` reports only propext, Classical.choice and Quot.sound. It follows the numbered argument above and may be reused verbatim.

```lean
theorem ts_pwb_density_points_of_image_ae : ∀ (n ℓ : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → Ambient n ℓ), MeasurableSet C → (∃ K : NNReal, LipschitzWith K F) → ∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)), ∀ w ∈ C, F w = x → Tendsto (fun r : ℝ ↦ volume (C ∩ closedBall w r) / volume (closedBall w r)) (𝓝[>] 0) (𝓝 1) := by
  intro n ℓ C F hC ⟨κ, hF⟩
  set Z : Set (EuclideanSpace ℝ (Fin n)) := {w | ¬ Tendsto (fun r : ℝ ↦ volume (C ∩ closedBall w r) / volume (closedBall w r)) (𝓝[>] 0) (𝓝 1)} ∩ C with hZ
  have hZ0 : volume Z = 0 := by
    have h := Besicovitch.ae_tendsto_measure_inter_div (volume : Measure (EuclideanSpace ℝ (Fin n))) C
    rw [ae_iff, Measure.restrict_apply' hC] at h
    exact h
  have hFZ : (μHE[n] : Measure (Ambient n ℓ)) (F '' Z) = 0 := by
    have h1 := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
      (A := Z) n (hF.lipschitzOnWith (s := Z))
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hZ0, mul_zero] at h1
    exact le_antisymm h1 bot_le
  rw [ae_iff]
  refine measure_mono_null ?_ hFZ
  intro x hx
  simp only [not_forall, mem_ofPred_eq] at hx
  obtain ⟨w, hwC, hFw, hnt⟩ := hx
  exact ⟨w, ⟨hnt, hwC⟩, hFw⟩
```

## Key steps

1. Lebesgue density theorem (Besicovitch.ae_tendsto_measure_inter_div): Lⁿ⌞C-a.e. w is a density point of C
2. Z := non-density points of C satisfies Lⁿ(Z) = (Lⁿ⌞C)(non-density points) = 0 since C is Borel
3. Lipschitz image estimate with μHE[n] = Lⁿ on ℝⁿ: Hⁿ(F(Z)) ≤ κⁿLⁿ(Z) = 0
4. Every x violating the conclusion lies in F(Z), so the conclusion holds Hⁿ-a.e.

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
