# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.slice_imreps-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.slice_imreps-a1.ae_forall_compact-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent Step 0(d) (compact exhaustion K_1 ⊆ K_2 ⊆ … of U, every compact K ⊆ U lies in some K_i) and Step 2, third bullet (for t ∈ G₁ and compact K ⊆ U take K ⊆ K_i), with the countable intersection of Step 2, second bullet.

1. Exhausting compacts. For i ∈ ℕ let T_i := thickening (1/(i+1)) Uᶜ = {y : ∃ z ∉ U, dist(y, z) < 1/(i+1)} (open; empty when U = ℝ^P), and K_i := B̄(0, i) ∖ T_i. K_i is a closed subset of the compact ball B̄(0, i), hence compact ((isCompact_closedBall 0 (i : ℝ)).diff isOpen_thickening).
2. K_i ⊆ U. Let x ∈ K_i and suppose x ∉ U. Since 1/(i+1) > 0, Uᶜ ⊆ T_i (self_subset_thickening), so x ∈ T_i, contradicting x ∈ K_i. Hence x ∈ U.
3. Every compact K ⊆ U lies in some K_i. Since K is compact, U is open and K ⊆ U, there is δ > 0 with thickening δ K ⊆ U (IsCompact.exists_thickening_subset_open). K is bounded, so K ⊆ B̄(0, R) for some R (IsCompact.isBounded, Bornology.IsBounded.subset_closedBall). Choose i₁ ∈ ℕ with R ≤ i₁ (exists_nat_ge) and i₂ ∈ ℕ with 1/(i₂+1) < δ (exists_nat_one_div_lt); let i := max(i₁, i₂). Let x ∈ K.
   (a) x ∈ B̄(0, i), since B̄(0, R) ⊆ B̄(0, i₁) ⊆ B̄(0, i).
   (b) x ∉ T_i: otherwise there is y ∉ U with dist(x, y) < 1/(i+1) ≤ 1/(i₂+1) < δ (mem_thickening_iff). Then dist(y, x) < δ with x ∈ K, so y ∈ thickening δ K ⊆ U, a contradiction.
   Hence K ⊆ K_i.
4. Countable intersection. By hypothesis and steps 1–2, for each i, F_t(K_i) ≠ ∞ for a.e. t. Since ℕ is countable, for a.e. t this holds for all i simultaneously (ae_all_iff).
5. Fix such a t and a compact K ⊆ U. By step 3 choose i with K ⊆ K_i. By monotonicity F_t(K) ≤ F_t(K_i) < ∞, so F_t(K) ≠ ∞ (ne_top_of_le_ne_top). ∎
[Lean hints (verified names at mathlib 25730c7c): isCompact_closedBall, IsCompact.diff, isOpen_thickening, self_subset_thickening, IsCompact.exists_thickening_subset_open, IsCompact.isBounded, Bornology.IsBounded.subset_closedBall, exists_nat_ge, exists_nat_one_div_lt, closedBall_subset_closedBall, mem_thickening_iff, dist_comm, ae_all_iff, ne_top_of_le_ne_top. Monotone (F t) applied to K ⊆ K_i gives F t K ≤ F t K_i.]

Lean reference implementation (kernel-checked during this decomposition against GMT.Ch07.Submission, Lean v4.35.0-rc3, Mathlib 25730c7c, as a single declaration placed after the contract's `noncomputable section … end` inside `namespace GMT.Ch07` with the contract's opens and only `import GMT.Ch07.Submission`; #print axioms gives propext, Classical.choice, Quot.sound; no warnings):
theorem Submission.dor_lmbsf_si_ae_forall_compact : ∀ (P : ℕ) (U : Set (Euclid P)) (F : ℝ → Set (Euclid P) → ℝ≥0∞), IsOpen U → (∀ t, Monotone (F t)) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∀ᵐ t, F t K ≠ ∞) → ∀ᵐ t, ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → F t K ≠ ∞ := by
  intro P U F hU hmono hK
  let Kn : ℕ → Set (Euclid P) := fun i => closedBall 0 i \ thickening (1 / ((i : ℝ) + 1)) Uᶜ
  have hKc : ∀ i, IsCompact (Kn i) := fun i =>
    (isCompact_closedBall 0 (i : ℝ)).diff isOpen_thickening
  have hKU : ∀ i, Kn i ⊆ U := by
    intro i x hx
    by_contra hxU
    exact hx.2 (self_subset_thickening (by positivity) _ hxU)
  have hcover : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ i, K ⊆ Kn i := by
    intro K hKc' hKU'
    obtain ⟨δ, hδ, hδK⟩ := hKc'.exists_thickening_subset_open hU hKU'
    obtain ⟨R, hR⟩ := hKc'.isBounded.subset_closedBall 0
    obtain ⟨i₁, hi₁⟩ := exists_nat_ge R
    obtain ⟨i₂, hi₂⟩ := exists_nat_one_div_lt hδ
    refine ⟨max i₁ i₂, fun x hx => ⟨?_, ?_⟩⟩
    · exact closedBall_subset_closedBall (hi₁.trans (by exact_mod_cast le_max_left i₁ i₂)) (hR hx)
    · intro hxt
      rw [mem_thickening_iff] at hxt
      obtain ⟨y, hyU, hxy⟩ := hxt
      have hlt : (1 : ℝ) / ((max i₁ i₂ : ℕ) + 1) ≤ 1 / ((i₂ : ℝ) + 1) := by
        gcongr; exact_mod_cast le_max_right i₁ i₂
      have hy : y ∈ thickening δ K := by
        rw [mem_thickening_iff]
        exact ⟨x, hx, by rw [dist_comm]; linarith⟩
      exact hyU (hδK hy)
  have hall : ∀ᵐ t, ∀ i, F t (Kn i) ≠ ∞ := ae_all_iff.mpr fun i => hK _ (hKc i) (hKU i)
  filter_upwards [hall] with t ht K hKc' hKU'
  obtain ⟨i, hi⟩ := hcover K hKc' hKU'
  exact ne_top_of_le_ne_top (ht i) (hmono t hi)

## Key steps

1. K_i := B̄(0,i) ∖ thickening(1/(i+1)) Uᶜ is compact and contained in U.
2. Every compact K ⊆ U lies in some K_i (positive margin δ from IsCompact.exists_thickening_subset_open, plus boundedness).
3. ae_all_iff over i ∈ ℕ: for a.e. t, F_t(K_i) ≠ ∞ for all i.
4. Monotonicity transfers finiteness from K_i to any compact K ⊆ K_i.

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
