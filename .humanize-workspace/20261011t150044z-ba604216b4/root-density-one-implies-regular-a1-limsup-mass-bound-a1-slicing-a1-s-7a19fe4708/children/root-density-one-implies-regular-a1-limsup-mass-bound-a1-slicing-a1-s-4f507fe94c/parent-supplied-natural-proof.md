# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.slice_imreps-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.slice_imreps-a1.coarea_ae_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 1 of the parent proof (transfer of null sets to slices, via (G3) with φ = 1_Z and lintegral_eq_zero_iff'), stated for an abstract co-area identity.

1. Null hull. Let N := {x : ¬p(x)}. The hypothesis ∀ᵐ x ∂μ, p x says μ(N) = 0 (ae_iff). Let Z := toMeasurable μ N. Then Z is Borel (measurableSet_toMeasurable), N ⊆ Z (subset_toMeasurable) and μ(Z) = μ(N) = 0 (measure_toMeasurable).
2. Co-area with an indicator. φ := 1_Z (Z.indicator 1) is Borel and [0, ∞]-valued (measurable_one.indicator). By the co-area hypothesis, F(t) := ∫ 1_Z dν_t is a.e.-measurable on ℝ and ∫_ℝ F(t) dt = ∫ w·1_Z dμ.
3. The right side vanishes. Since μ(Z) = 0, μ-a.e. x lies outside Z (measure_eq_zero_iff_ae_notMem), and for such x, w(x)·1_Z(x) = w(x)·0 = 0. So w·1_Z = 0 μ-a.e., and ∫ w·1_Z dμ = ∫ 0 dμ = 0 (lintegral_congr_ae, lintegral_zero).
4. Hence ∫_ℝ F(t) dt = 0. As F is a.e.-measurable, lintegral_eq_zero_iff' gives F = 0 Lebesgue-a.e. on ℝ.
5. Fix t with F(t) = 0. Since Z is measurable, F(t) = ∫ 1_Z dν_t = ν_t(Z) (lintegral_indicator_one). So ν_t(Z) = 0, i.e. ν_t-a.e. x satisfies x ∉ Z (measure_eq_zero_iff_ae_notMem).
6. For such x we have x ∉ N, because N ⊆ Z; that is, p(x) holds (by contradiction: ¬p(x) would give x ∈ N ⊆ Z).
7. Combining 4–6: for Lebesgue-a.e. t, p(x) holds for ν_t-a.e. x. ∎
[Lean hints (all verified to exist at mathlib 25730c7c): measurableSet_toMeasurable, subset_toMeasurable, measure_toMeasurable, ae_iff, measure_eq_zero_iff_ae_notMem, lintegral_congr_ae, lintegral_zero, lintegral_eq_zero_iff', lintegral_indicator_one. The hypothesis is only used with φ = Z.indicator 1. w need not be measurable.]

Lean reference implementation (kernel-checked during this decomposition against GMT.Ch07.Submission, Lean v4.35.0-rc3, Mathlib 25730c7c, as a single declaration placed after the contract's `noncomputable section … end` inside `namespace GMT.Ch07` with the contract's opens and only `import GMT.Ch07.Submission`; #print axioms gives propext, Classical.choice, Quot.sound; no warnings):
theorem Submission.dor_lmbsf_si_coarea_ae_transfer : ∀ (P : ℕ) (μ : Measure (Euclid P)) (ν : ℝ → Measure (Euclid P)) (w : Euclid P → ℝ≥0∞) (p : Euclid P → Prop), (∀ φ : Euclid P → ℝ≥0∞, Measurable φ → AEMeasurable (fun t => ∫⁻ x, φ x ∂(ν t)) ∧ ∫⁻ t, ∫⁻ x, φ x ∂(ν t) = ∫⁻ x, w x * φ x ∂μ) → (∀ᵐ x ∂μ, p x) → ∀ᵐ t, ∀ᵐ x ∂(ν t), p x := by
  intro P μ ν w p hco hp
  set Z := toMeasurable μ {x | ¬ p x} with hZ
  have hZm : MeasurableSet Z := measurableSet_toMeasurable _ _
  have hμZ : μ Z = 0 := by rw [hZ, measure_toMeasurable]; exact ae_iff.mp hp
  obtain ⟨hae, heq⟩ := hco (Z.indicator 1) (measurable_one.indicator hZm)
  have hzero : ∫⁻ x, w x * Z.indicator 1 x ∂μ = 0 := by
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    have : ∀ᵐ x ∂μ, x ∉ Z := measure_eq_zero_iff_ae_notMem.mp hμZ
    filter_upwards [this] with x hx
    simp [indicator_of_notMem hx]
  rw [hzero, lintegral_eq_zero_iff' hae] at heq
  filter_upwards [heq] with t ht
  have hνZ : ν t Z = 0 := by
    have := ht
    simp only [Pi.zero_apply] at this
    rwa [lintegral_indicator_one hZm] at this
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hνZ] with x hx
  by_contra hpx
  exact hx (subset_toMeasurable μ {x | ¬ p x} hpx)

## Key steps

1. Take the Borel μ-null hull Z := toMeasurable μ {¬p} ⊇ {¬p}.
2. Apply the co-area identity to φ = 1_Z: ∫_ℝ ν_t(Z) dt = ∫ w·1_Z dμ = 0 because 1_Z = 0 μ-a.e.
3. By lintegral_eq_zero_iff' (a.e.-measurability is part of the hypothesis), ν_t(Z) = 0 for a.e. t.
4. For such t, ν_t-a.e. x lies outside Z ⊇ {¬p}, so p(x) holds.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical); cat manifest.json`
- `rg -n 'theorem alternatizeUncurryFin_add|theorem alternatizeUncurryFin_smul|lemma norm_alternatizeUncurryFin_le' <snapshot>/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `rg -n 'def IsBoundedBilinearMap.toContinuousLinearMap|theorem isBoundedBilinearMap_comp' <snapshot>/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `rg -n 'theorem integral_eq_lintegral_pos_part_sub_lintegral_neg_part|theorem integrable_toReal_of_lintegral_ne_top|theorem integral_toReal' <snapshot>/mathlib/Mathlib/MeasureTheory`
- `rg -n exists_thickening_subset_open <snapshot>/mathlib/Mathlib; rg -n CompactExhaustion <snapshot>/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `rg -n -i 'coarea|co-area' <snapshot>/project/GMT (only the Ch02 CoareaFormula Prop definition; no signed co-area or slice lemma)`
- `rg -ln 'coarea|Coarea' simongmt/Poincare/SimonGMT; rg -n 'alternatizeUncurryFin|IsUnitOrientationOf' simongmt/Poincare/SimonGMT (no slice-orientation, a.e.-transfer or signed co-area lemma)`
- `grep -n HasApproximateTangentSpaceAt simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (definition line 102; .unique line 232 has no extra hypotheses)`
- `grep -n 'abbrev Covector|abbrev DifferentialForm|def IsTestForm' Chapter06/Forms.lean; grep -n 'testFormOnSubmodule|abbrev TestFormOn' Chapter06/Currents.lean`
- `dag.json scans: IsUnitOrientationOf with norm bounds (accepted unit_orientation_norm_le_one, rsd_mw_wlm_orient_opNorm_le_one, imsupp_unit_orientation_ne_zero_norm_le_one); lean_name census (no dor_lmbsf_si_*); cross-branch reuse precedent over nodes/*/decomposition-v*.json`
- `git show 533617d27b3a:GMT/Ch07/Submission.lean and 0325970d8b47:GMT/Ch07/Submission.lean (accepted proofs of the reused declarations)`
- `python3 -I verifier lean_contract.validate_lean_statement and gmt-compare.child_modules on the six statements; lake env lean on the challenge files and on /tmp/dor-si-decomp/{C15,C2,C3,C4,Assembly2,E2E2}.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-7a19fe4708/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-7a19fe4708/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-first-variation-mass-bound-a1-o-90c59096a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-measure-unique-a1-orie-c3a822a8f5/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-a685b45291/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/dor-si-decomp/Assembly2.lean`
- `/tmp/dor-si-decomp/E2E2.lean`

The snapshot (project b4d606d, mathlib 25730c7c) Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

No existing declaration covers null-set transfer to co-area slices, the signed co-area identity, the compact-exhaustion a.e. swap, or the slice orientation field. The snapshot project has only a Ch02 CoareaFormula Prop definition, and simongmt has no such lemmas. So four fresh dor_lmbsf_si_* names are used, none present in the DAG.

Step 0(b) is already covered by two comparator-accepted declarations with byte-identical types, which are reused, following the DAG's cross-branch reuse precedent:
- fvmb_imrep_ae_unitOrientation_approxTangentPlane (commit 533617d);
- unit_orientation_norm_le_one (commit 0325970).

Mathlib supplies everything else, including:
- alternatizeUncurryFin_add/_smul, norm_alternatizeUncurryFin_le;
- IsBoundedBilinearMap.toContinuousLinearMap, isBoundedBilinearMap_comp;
- integral_eq_lintegral_pos_part_sub_lintegral_neg_part, integrable_toReal_of_lintegral_ne_top, integral_toReal;
- IsCompact.exists_thickening_subset_open;
- simongmt HasApproximateTangentSpaceAt.unique.

The TopologicalSpace instance on Covector →L (Euclid →L Covector) fails to synthesize, so slice_orientation_field avoids smulRightL.

Lean checks:
- All six child types validate and elaborate in the comparator scope.
- The four new children have kernel-checked proofs with standard axioms.
- The parent's exact frozen type follows from the six children and the sibling dor_lmbsf_interior_product_orientation using only propext, Classical.choice and Quot.sound.
