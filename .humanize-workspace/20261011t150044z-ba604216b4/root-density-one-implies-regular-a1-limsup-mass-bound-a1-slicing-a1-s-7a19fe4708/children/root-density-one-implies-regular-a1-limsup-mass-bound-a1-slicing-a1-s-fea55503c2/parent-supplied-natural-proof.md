# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.slice_imreps-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.slice_imreps-a1.slice_orientation_field-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent Step 3 (definition of ξ̃ = ξ₀ ∘ (ν♭∧·), its strong measurability via the continuous map Ξ(ζ, v) = ζ ∘L (α ↦ v♭∧α) on MultiVector P (n+1) × ℝ^P, and the linearity identity |g|·ξ̃(α) = ξ₀(g♭∧α)), together with the bound ‖v♭∧α‖ ≤ (n+1)|v|‖α‖ of parent Step 7.

1. The wedge pairing is bilinear. Let B(v, α) := v♭∧α = alternatizeUncurryFin((innerSL ℝ v).smulRight α) for (v, α) ∈ ℝ^P × Covector(ℝ^P, n). B is additive and ℝ-homogeneous in v and in α. Indeed innerSL ℝ is linear in v (map_add, map_smul); c ↦ c.smulRight α and α ↦ c.smulRight α are linear (check after ext y: (c.smulRight α) y = c(y) • α, then add_smul / smul_add / smul_smul); and alternatizeUncurryFin is additive and homogeneous (ContinuousAlternatingMap.alternatizeUncurryFin_add, alternatizeUncurryFin_smul). In Lean: rewrite with ← alternatizeUncurryFin_add / ← alternatizeUncurryFin_smul, then congr 1, ext y, simp [add_smul, smul_smul].
2. The wedge bound. For all v, α: ‖v♭∧α‖ ≤ (n+1)·‖(innerSL ℝ v).smulRight α‖ = (n+1)·‖innerSL ℝ v‖·‖α‖ = (n+1)·|v|·‖α‖ (ContinuousAlternatingMap.norm_alternatizeUncurryFin_le, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm).
3. Steps 1–2 make B a bounded bilinear map (IsBoundedBilinearMap ℝ B, with bound constant n+1 > 0: ‖B(v, α)‖ ≤ (n+1)·|v|·‖α‖). Let A := B.toContinuousLinearMap : ℝ^P →L[ℝ] (Covector n →L[ℝ] Covector (n+1)) (IsBoundedBilinearMap.toContinuousLinearMap), so A(v)(α) = v♭∧α (definitionally, by rfl).
   [Lean warning: do not build A with ContinuousLinearMap.smulRightL or ContinuousLinearMap.compL: the instance TopologicalSpace (Covector (Euclid P) n →L[ℝ] Euclid P →L[ℝ] Covector (Euclid P) n) fails to synthesize. The route of step 3 (an IsBoundedBilinearMap structure written field by field: add_left, smul_left, add_right, smul_right, bound) is verified to work.]
4. Ξ is continuous. Define Ξ : MultiVector P (n+1) × ℝ^P → MultiVector P n by Ξ(ζ₀, v) := ζ₀ ∘L A(v). Composition (f, h) ↦ f ∘L h is bounded bilinear (isBoundedBilinearMap_comp), hence continuous, and p ↦ (p.1, A(p.2)) is continuous (continuous_fst.prodMk (A.continuous.comp continuous_snd)). So Ξ is continuous.
5. Definition and measurability of ζ'. ν(x) := |g(x)|⁻¹ g(x) is Borel (hg.norm.inv.smul hg), hence strongly measurable (Measurable.stronglyMeasurable; ℝ^P is second countable). Then x ↦ (ζ(x), ν(x)) is strongly measurable (StronglyMeasurable.prodMk), and ζ'(x) := Ξ(ζ(x), ν(x)) is strongly measurable (Continuous.comp_stronglyMeasurable).
6. (a) holds by definition: ζ'(x)(α) = ζ(x)(A(ν(x))(α)) = ζ(x)(ν(x)♭∧α).
7. (b). If g(x) = 0: the left side is 0·ζ'(x)(α) = 0, and A(0) = 0 (map_zero), so the right side is ζ(x)(0) = 0. If g(x) ≠ 0: by linearity of A and of ζ(x), ζ'(x)(α) = ζ(x)(A(|g(x)|⁻¹ • g(x))(α)) = |g(x)|⁻¹ · ζ(x)(A(g(x))(α)) (map_smul, smul_apply, smul_eq_mul); multiplying by |g(x)| and using |g(x)|·|g(x)|⁻¹ = 1 (mul_inv_cancel₀, norm_ne_zero_iff) gives (b).
8. (c). With β := g(x)♭∧α = A(g(x))(α): |ζ(x)(β)| ≤ ‖ζ(x)‖·‖β‖ (ContinuousLinearMap.le_opNorm) ≤ ‖ζ(x)‖·(n+1)·|g(x)|·‖α‖ by step 2; rearrange (ring). ∎

Lean reference implementation (kernel-checked during this decomposition against GMT.Ch07.Submission, Lean v4.35.0-rc3, Mathlib 25730c7c, as a single declaration placed after the contract's `noncomputable section … end` inside `namespace GMT.Ch07` with the contract's opens and only `import GMT.Ch07.Submission`; #print axioms gives propext, Classical.choice, Quot.sound; no warnings):
theorem Submission.dor_lmbsf_si_slice_orientation_field : ∀ (P n : ℕ) (ζ : Euclid P → MultiVector P (n + 1)) (g : Euclid P → Euclid P), StronglyMeasurable ζ → Measurable g → ∃ ζ' : Euclid P → MultiVector P n, StronglyMeasurable ζ' ∧ (∀ x (α : Covector (Euclid P) n), ζ' x α = ζ x (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (‖g x‖⁻¹ • g x)).smulRight α))) ∧ (∀ x (α : Covector (Euclid P) n), ‖g x‖ * ζ' x α = ζ x (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (g x)).smulRight α))) ∧ ∀ x (α : Covector (Euclid P) n), |ζ x (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (g x)).smulRight α))| ≤ ((n : ℝ) + 1) * ‖ζ x‖ * ‖g x‖ * ‖α‖ := by
  intro P n ζ g hζ hg
  let B : Euclid P × Covector (Euclid P) n → Covector (Euclid P) (n + 1) := fun p =>
    ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ p.1).smulRight p.2)
  have hBnorm : ∀ v α, ‖B (v, α)‖ ≤ ((n : ℝ) + 1) * (‖v‖ * ‖α‖) := by
    intro v α
    refine (ContinuousAlternatingMap.norm_alternatizeUncurryFin_le _).trans ?_
    rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
  have hB : IsBoundedBilinearMap ℝ B :=
    { add_left := fun v w α => by
        simp only [B, map_add, ← ContinuousAlternatingMap.alternatizeUncurryFin_add]
        congr 1
        ext y
        simp [add_smul]
      smul_left := fun c v α => by
        simp only [B, map_smul, ← ContinuousAlternatingMap.alternatizeUncurryFin_smul]
        congr 1
        ext y
        simp [smul_smul]
      add_right := fun v α β => by
        simp only [B, ← ContinuousAlternatingMap.alternatizeUncurryFin_add]
        congr 1
        ext y
        simp
      smul_right := fun c v α => by
        simp only [B, ← ContinuousAlternatingMap.alternatizeUncurryFin_smul]
        congr 1
        ext y
        simp [smul_smul, mul_comm]
      bound := ⟨(n : ℝ) + 1, by positivity, fun v α => by
        have := hBnorm v α
        linarith [mul_assoc ((n : ℝ) + 1) ‖v‖ ‖α‖]⟩ }
  let A : Euclid P →L[ℝ] Covector (Euclid P) n →L[ℝ] Covector (Euclid P) (n + 1) :=
    hB.toContinuousLinearMap
  have hA : ∀ v α, A v α = ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ v).smulRight α) := by
    intro v α; rfl
  let Ξ : MultiVector P (n + 1) × Euclid P → MultiVector P n := fun p => p.1.comp (A p.2)
  have hΞ : Continuous Ξ :=
    isBoundedBilinearMap_comp.continuous.comp (continuous_fst.prodMk (A.continuous.comp continuous_snd))
  have hv : Measurable fun x => ‖g x‖⁻¹ • g x := (hg.norm.inv).smul hg
  refine ⟨fun x => Ξ (ζ x, ‖g x‖⁻¹ • g x), hΞ.comp_stronglyMeasurable (hζ.prodMk hv.stronglyMeasurable), ?_, ?_, ?_⟩
  · intro x α; rfl
  · intro x α
    show ‖g x‖ * ζ x (A (‖g x‖⁻¹ • g x) α) = ζ x (A (g x) α)
    by_cases hgx : g x = 0
    · simp [hgx]
    · rw [map_smul, smul_apply, map_smul, smul_eq_mul, ← mul_assoc,
        mul_inv_cancel₀ (norm_ne_zero_iff.mpr hgx), one_mul]
  · intro x α
    have h1 := (ζ x).le_opNorm (A (g x) α)
    have h2 : ‖A (g x) α‖ ≤ ((n : ℝ) + 1) * (‖g x‖ * ‖α‖) := hBnorm (g x) α
    rw [← hA, ← Real.norm_eq_abs]
    calc ‖ζ x (A (g x) α)‖ ≤ ‖ζ x‖ * ‖A (g x) α‖ := h1
      _ ≤ ‖ζ x‖ * (((n : ℝ) + 1) * (‖g x‖ * ‖α‖)) := by gcongr
      _ = _ := by ring

## Key steps

1. B(v, α) = alternatizeUncurryFin((innerSL ℝ v).smulRight α) is bilinear with ‖B(v,α)‖ ≤ (n+1)|v|‖α‖ (norm_alternatizeUncurryFin_le, norm_smulRight_apply, innerSL_apply_norm).
2. A := IsBoundedBilinearMap.toContinuousLinearMap B : ℝ^P →L (Λⁿ →L Λⁿ⁺¹), avoiding smulRightL (its nested CLM type fails instance synthesis).
3. Ξ(ζ₀, v) = ζ₀ ∘L A(v) is continuous (isBoundedBilinearMap_comp); ζ'(x) := Ξ(ζ(x), |g(x)|⁻¹g(x)) is strongly measurable (prodMk + Continuous.comp_stronglyMeasurable).
4. (a) by definition; (b) by linearity of A and ζ(x), with the case g(x) = 0 trivial; (c) from le_opNorm and the wedge bound.

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
