# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.slice_imreps-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.slice_imreps-a1.coarea_signed_integral-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent Step 7, bullet 'Co-area' (apply (G3) to q̃⁺ and q̃⁻ and subtract the two finite identities; real integrals from lintegrals by integral_eq_lintegral_pos_part_sub_lintegral_neg_part / integral_toReal), and the measurability/integrability argument of parent Step 6, stated for an abstract co-area identity.

1. Positive and negative parts. Put q⁺(x) := ofReal(q(x)) and q⁻(x) := ofReal(−q(x)) in [0, ∞]. Both are Borel (Measurable.ennreal_ofReal applied to q and −q), and so is |q| = ‖q‖ₑ (Measurable.enorm). For real r, ofReal(r) ≤ ofReal|r| = ‖r‖ₑ and ofReal(−r) ≤ ofReal|r| = ‖r‖ₑ (ofReal_norm, Real.norm_eq_abs, le_abs_self, neg_le_abs); hence q⁺ ≤ ‖q‖ₑ and q⁻ ≤ ‖q‖ₑ pointwise.
2. Co-area for the three nonnegative functions. Apply the hypothesis to φ = q⁺, q⁻ and ‖q‖ₑ. With F^±(t) := ∫ q^± dν_t and A(t) := ∫ ‖q‖ₑ dν_t, the functions F⁺, F⁻, A are a.e.-measurable on ℝ and
   ∫_ℝ F^± dt = ∫ w·q^± dμ ≤ ∫ w·‖q‖ₑ dμ < ∞ (lintegral_mono with mul_le_mul_right of step 1),  ∫_ℝ A dt = ∫ w·‖q‖ₑ dμ < ∞.
3. Integrability on a.e. slice. By ae_lt_top' (A a.e.-measurable, ∫ A < ∞), A(t) < ∞ for a.e. t. For such t, q is ν_t-integrable: it is Borel (hence a.e.-strongly measurable) and has finite integral ∫ ‖q‖ₑ dν_t = A(t) < ∞. For these t, integral_eq_lintegral_pos_part_sub_lintegral_neg_part gives ∫ q dν_t = F⁺(t).toReal − F⁻(t).toReal. Hence t ↦ ∫ q dν_t agrees Lebesgue-a.e. with G(t) := F⁺(t).toReal − F⁻(t).toReal.
4. Integrability in t and value of the left side. F^± are a.e.-measurable with finite lintegral, so t ↦ F^±(t).toReal are Lebesgue integrable (integrable_toReal_of_lintegral_ne_top), and ∫_ℝ F^±(t).toReal dt = (∫_ℝ F^± dt).toReal (integral_toReal, using F^± < ∞ a.e. from ae_lt_top'). Hence G is integrable, t ↦ ∫ q dν_t is integrable (Integrable.congr with step 3), and by integral_congr_ae, integral_sub and step 2:
   ∫_ℝ (∫ q dν_t) dt = ∫_ℝ G = (∫ w·q⁺ dμ).toReal − (∫ w·q⁻ dμ).toReal.
5. The right side is a Bochner integral of an integrable function. Let h(x) := w̄(x)·q(x). It is Borel (ENNReal measurable toReal composed with w, times q). Pointwise ‖h(x)‖ₑ = ‖w̄(x)‖ₑ·‖q(x)‖ₑ (enorm_mul) and ‖w̄(x)‖ₑ = ofReal(w̄(x)) ≤ w(x) (Real.enorm_eq_ofReal with toReal ≥ 0, ENNReal.ofReal_toReal_le). Hence ∫ ‖h‖ₑ dμ ≤ ∫ w·‖q‖ₑ dμ < ∞, h is μ-integrable, and ∫ h dμ = (∫ ofReal(h) dμ).toReal − (∫ ofReal(−h) dμ).toReal (integral_eq_lintegral_pos_part_sub_lintegral_neg_part).
6. Pointwise comparison. Since w·‖q‖ₑ is Borel with finite integral, w(x)·‖q(x)‖ₑ < ∞ for μ-a.e. x (ae_lt_top). Claim: at every such x and for every real r with |r| ≤ |q(x)|, ofReal(w̄(x)·r) = w(x)·ofReal(r).
   (a) If w(x) < ∞: ofReal(w̄(x)·r) = ofReal(w̄(x))·ofReal(r) (ENNReal.ofReal_mul, as w̄(x) ≥ 0) = w(x)·ofReal(r) (ENNReal.ofReal_toReal).
   (b) If w(x) = ∞: q(x) = 0, since otherwise ‖q(x)‖ₑ ≠ 0 and w(x)·‖q(x)‖ₑ = ∞·‖q(x)‖ₑ = ∞ (ENNReal.top_mul), contradicting finiteness. Then |r| ≤ 0 forces r = 0, and both sides equal 0.
7. Applying step 6 with r = q(x) and with r = −q(x) (note −h(x) = w̄(x)·(−q(x)), mul_neg) gives ofReal(h) = w·q⁺ and ofReal(−h) = w·q⁻ μ-a.e. So by lintegral_congr_ae, ∫ ofReal(h) dμ = ∫ w·q⁺ dμ and ∫ ofReal(−h) dμ = ∫ w·q⁻ dμ, and by step 5,
   ∫ w̄·q dμ = (∫ w·q⁺ dμ).toReal − (∫ w·q⁻ dμ).toReal.
8. Steps 4 and 7 give ∫_ℝ (∫ q dν_t) dt = ∫ w̄·q dμ, and step 4 gives the integrability claim. ∎
[Lean hints (verified names at mathlib 25730c7c): Measurable.ennreal_ofReal, Measurable.enorm, ofReal_norm, ae_lt_top', ae_lt_top, integral_eq_lintegral_pos_part_sub_lintegral_neg_part, integrable_toReal_of_lintegral_ne_top, integral_toReal, integral_congr_ae, integral_sub, Integrable.sub, Integrable.congr, Measurable.ennreal_toReal, enorm_mul, Real.enorm_eq_ofReal, ENNReal.ofReal_toReal_le, ENNReal.ofReal_mul, ENNReal.ofReal_toReal, ENNReal.top_mul. At this Mathlib revision the ordered-semiring monotonicity lemmas are mul_le_mul_right (h : b ≤ c) a : a * b ≤ a * c and mul_le_mul_left (h : b ≤ c) a : b * a ≤ c * a (the primed names mul_le_mul_left'/mul_le_mul_right' no longer exist). An integrable real function is a pair (AEStronglyMeasurable, HasFiniteIntegral) and HasFiniteIntegral f μ unfolds to ∫⁻ ‖f‖ₑ ∂μ < ∞.]

Lean reference implementation (kernel-checked during this decomposition against GMT.Ch07.Submission, Lean v4.35.0-rc3, Mathlib 25730c7c, as a single declaration placed after the contract's `noncomputable section … end` inside `namespace GMT.Ch07` with the contract's opens and only `import GMT.Ch07.Submission`; #print axioms gives propext, Classical.choice, Quot.sound; no warnings):
theorem Submission.dor_lmbsf_si_coarea_signed_integral : ∀ (P : ℕ) (μ : Measure (Euclid P)) (ν : ℝ → Measure (Euclid P)) (w : Euclid P → ℝ≥0∞) (q : Euclid P → ℝ), (∀ φ : Euclid P → ℝ≥0∞, Measurable φ → AEMeasurable (fun t => ∫⁻ x, φ x ∂(ν t)) ∧ ∫⁻ t, ∫⁻ x, φ x ∂(ν t) = ∫⁻ x, w x * φ x ∂μ) → Measurable w → Measurable q → ∫⁻ x, w x * ‖q x‖ₑ ∂μ ≠ ∞ → Integrable (fun t => ∫ x, q x ∂(ν t)) ∧ ∫ t, ∫ x, q x ∂(ν t) = ∫ x, (w x).toReal * q x ∂μ := by
  intro P μ ν w q hco hw hq hfin
  have hqp : Measurable fun x => ENNReal.ofReal (q x) := hq.ennreal_ofReal
  have hqn : Measurable fun x => ENNReal.ofReal (-q x) := hq.neg.ennreal_ofReal
  have hle_p : ∀ x, ENNReal.ofReal (q x) ≤ ‖q x‖ₑ := fun x => by
    rw [← ofReal_norm, Real.norm_eq_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hle_n : ∀ x, ENNReal.ofReal (-q x) ≤ ‖q x‖ₑ := fun x => by
    rw [← ofReal_norm, Real.norm_eq_abs]; exact ENNReal.ofReal_le_ofReal (neg_le_abs _)
  obtain ⟨haeP, heqP⟩ := hco _ hqp
  obtain ⟨haeN, heqN⟩ := hco _ hqn
  obtain ⟨haeA, heqA⟩ := hco _ hq.enorm
  have hfinP : ∫⁻ t, ∫⁻ x, ENNReal.ofReal (q x) ∂(ν t) ≠ ∞ := by
    rw [heqP]; exact ne_top_of_le_ne_top hfin (lintegral_mono fun x => mul_le_mul_right (hle_p x) _)
  have hfinN : ∫⁻ t, ∫⁻ x, ENNReal.ofReal (-q x) ∂(ν t) ≠ ∞ := by
    rw [heqN]; exact ne_top_of_le_ne_top hfin (lintegral_mono fun x => mul_le_mul_right (hle_n x) _)
  have hfinA : ∫⁻ t, ∫⁻ x, ‖q x‖ₑ ∂(ν t) ≠ ∞ := by rw [heqA]; exact hfin
  have hint : ∀ᵐ t, Integrable q (ν t) := by
    filter_upwards [ae_lt_top' haeA hfinA] with t ht
    exact ⟨hq.aestronglyMeasurable, ht⟩
  have hrepr : (fun t => ∫ x, q x ∂(ν t)) =ᵐ[volume] fun t =>
      (∫⁻ x, ENNReal.ofReal (q x) ∂(ν t)).toReal - (∫⁻ x, ENNReal.ofReal (-q x) ∂(ν t)).toReal := by
    filter_upwards [hint] with t ht
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part ht
  have hIP : Integrable (fun t => (∫⁻ x, ENNReal.ofReal (q x) ∂(ν t)).toReal) :=
    integrable_toReal_of_lintegral_ne_top haeP hfinP
  have hIN : Integrable (fun t => (∫⁻ x, ENNReal.ofReal (-q x) ∂(ν t)).toReal) :=
    integrable_toReal_of_lintegral_ne_top haeN hfinN
  refine ⟨(hIP.sub hIN).congr hrepr.symm, ?_⟩
  rw [integral_congr_ae hrepr, integral_sub hIP hIN, integral_toReal haeP (ae_lt_top' haeP hfinP),
    integral_toReal haeN (ae_lt_top' haeN hfinN), heqP, heqN]
  have hh : Integrable (fun x => (w x).toReal * q x) μ := by
    refine ⟨(hw.ennreal_toReal.mul hq).aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hfin.lt_top
    rw [enorm_mul]
    gcongr
    rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal_le
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hh]
  have hnull : ∀ᵐ x ∂μ, w x * ‖q x‖ₑ < ∞ := ae_lt_top (hw.mul hq.enorm) hfin
  have key : ∀ x, w x * ‖q x‖ₑ < ∞ → ∀ r : ℝ, |r| ≤ |q x| →
      ENNReal.ofReal ((w x).toReal * r) = w x * ENNReal.ofReal r := by
    intro x hx r hr
    by_cases hwx : w x = ∞
    · have hq0 : q x = 0 := by
        by_contra hq0
        rw [hwx, ENNReal.top_mul (by simpa using hq0)] at hx
        exact lt_irrefl _ hx
      have : r = 0 := by rw [hq0, abs_zero] at hr; exact abs_nonpos_iff.mp hr
      simp [this]
    · rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hwx]
  have e1 : ∫⁻ x, ENNReal.ofReal ((w x).toReal * q x) ∂μ = ∫⁻ x, w x * ENNReal.ofReal (q x) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hnull] with x hx
    exact key x hx (q x) le_rfl
  have e2 : ∫⁻ x, ENNReal.ofReal (-((w x).toReal * q x)) ∂μ =
      ∫⁻ x, w x * ENNReal.ofReal (-q x) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hnull] with x hx
    rw [← mul_neg]
    exact key x hx (-q x) (by rw [abs_neg])
  rw [e1, e2]

## Key steps

1. Split q = q⁺ − q⁻ with q^± = ofReal(±q) ≤ ‖q‖ₑ; apply the co-area identity to q⁺, q⁻ and ‖q‖ₑ.
2. A(t) = ∫‖q‖ₑ dν_t is finite for a.e. t, so q ∈ L¹(ν_t) and ∫ q dν_t = F⁺(t).toReal − F⁻(t).toReal a.e.
3. F^±.toReal are integrable with integrals (∫ w q^± dμ).toReal (integrable_toReal_of_lintegral_ne_top, integral_toReal).
4. h = w̄·q is μ-integrable since ‖h‖ₑ ≤ w‖q‖ₑ; split ∫ h into positive and negative lintegrals.
5. Where w = ∞, finiteness of w‖q‖ₑ forces q = 0 a.e.; hence ofReal(±h) = w·q^± μ-a.e., and the two sides agree.

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
