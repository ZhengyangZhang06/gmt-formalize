# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.projected_comparison-a1.competitor_mass-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.projected_comparison-a1.competitor_mass-a1.pairing_add-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3 and 6 of the parent-supplied proof of the selected node, S(ω) = ∫ (ν_Z + ν_X)(φ) dHⁿ = ∫ ν_Y(φ) dHⁿ with every integrand dominated on the compact closure of G. The argument is step 4 of the accepted sibling comb_action with the test form ω replaced by a bounded, compactly supported field F. Integrability on each carrier comes from the accepted sibling pairing_bound.
Notation. H := μHE[n]. For an IMRep R' = (M', θ', ξ') in U put ν_{R'} := M'.indicator (y ↦ (θ'(y) : ℝ) • ξ'(y)) : ℝ^P → MultiVector P n, h_{R'}(x) := θ'(x)·ξ'(x)(F(x)) ∈ ℝ, and I(R') := ∫_{M'} h_{R'} dH = ∫ h_{R'} d(H⌞M'). The claim is I(R) = I(R₁) + I(R₂).
1. Integrability on each carrier. Let R' = (M', θ', ξ') be any IMRep in U. F is a.e.-strongly measurable for H, hence for the restriction H⌞M' (Mathlib AEStronglyMeasurable.restrict). Apply the sibling pairing_bound (Submission.dpf_pfc_imrep_pairing_integrable_abs_le) with C := K (compact, K ⊆ U), the field F (F = 0 off K and ‖F‖ ≤ B) and the bound B. Its first conjunct says that h_{R'} is H⌞M'-integrable.
2. Pointwise rewriting. For every x, ν_{R'}(x)(F(x)) = 1_{M'}(x)·h_{R'}(x). If x ∈ M', then ν_{R'}(x) = θ'(x)•ξ'(x) and (θ'(x)•ξ'(x))(F(x)) = θ'(x)·ξ'(x)(F(x)) = h_{R'}(x). If x ∉ M', then ν_{R'}(x) = 0 and 0(F(x)) = 0.
3. Global form. M' is measurable (measurableSet_carrier). By step 2, x ↦ ν_{R'}(x)(F(x)) is the indicator of M' applied to h_{R'}. By Mathlib integrable_indicator_iff and step 1 it is H-integrable, and by Mathlib integral_indicator ∫ ν_{R'}(x)(F(x)) dH(x) = ∫_{M'} h_{R'} dH = I(R').
4. The hypothesis evaluated at F. For H-a.e. x, ν_R(x) = ν_{R₁}(x) + ν_{R₂}(x) as continuous linear maps on n-covectors. A sum of linear maps is evaluated termwise, so ν_R(x)(F(x)) = ν_{R₁}(x)(F(x)) + ν_{R₂}(x)(F(x)) for H-a.e. x.
5. Conclusion. Apply step 3 to R, R₁ and R₂. A.e.-equal functions have equal Bochner integrals (step 4), and the integral is additive on the H-integrable functions x ↦ ν_{R_i}(x)(F(x)) (step 3). Hence
I(R) = ∫ ν_R(F) dH = ∫ (ν_{R₁}(F) + ν_{R₂}(F)) dH = ∫ ν_{R₁}(F) dH + ∫ ν_{R₂}(F) dH = I(R₁) + I(R₂).
This is the asserted identity ∫_M θξ(F) dHⁿ = ∫_{M₁} θ₁ξ₁(F) dHⁿ + ∫_{M₂} θ₂ξ₂(F) dHⁿ. ∎

Lean implementation notes (context, not part of the numbered proof). The script below was checked with `lake env lean` after `import GMT.Ch07.Submission` in namespace GMT.Ch07 with the contract's opens, as the body of `theorem Submission.dor_lmb_pc_cm_pairing_add_of_bounded : <frozen type> := by`; the sibling pairing_bound was declared as a Submission.X stand-in with its exact frozen type. #print axioms reports propext, Classical.choice, Quot.sound and sorryAx; sorryAx enters only through the sibling stand-in. The same script with the sibling passed as a hypothesis of its exact frozen type uses only propext, Classical.choice and Quot.sound.
```lean
  intro P n U K R₁ R₂ R F B hK hKU hF hF0 hFB hvd
  have key : ∀ R' : IMRep U n,
      Integrable (fun x => R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x (F x))
        μHE[n] ∧
      ∫ x, R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x (F x) ∂μHE[n] =
        ∫ x in R'.carrier, (R'.mult x : ℝ) * R'.orient x (F x) ∂μHE[n] := by
    intro R'
    have hfun : (fun x => R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x (F x)) =
        R'.carrier.indicator (fun y => (R'.mult y : ℝ) * R'.orient y (F y)) := by
      funext x
      by_cases hx : x ∈ R'.carrier
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    rw [hfun, integrable_indicator_iff R'.measurableSet_carrier,
      integral_indicator R'.measurableSet_carrier]
    exact ⟨(Submission.dpf_pfc_imrep_pairing_integrable_abs_le P n U K R' F B hK hKU hF.restrict hF0 hFB).1, rfl⟩
  obtain ⟨-, he⟩ := key R
  obtain ⟨hi₁, he₁⟩ := key R₁
  obtain ⟨hi₂, he₂⟩ := key R₂
  rw [← he, ← he₁, ← he₂, ← integral_add hi₁ hi₂]
  refine integral_congr_ae ?_
  filter_upwards [hvd] with x hx
  rw [hx, add_apply]
```

## Key steps

1. pairing_bound with C := K makes θ'ξ'(F) integrable on the carrier of each of R, R₁ and R₂.
2. ν_{R'}(x)(F(x)) = 1_{M'}(x)θ'(x)ξ'(x)(F(x)), so ∫ ν_{R'}(F) dHⁿ = ∫_{M'} θ'ξ'(F) dHⁿ, with an Hⁿ-integrable integrand.
3. Evaluating ν_R = ν_{R₁} + ν_{R₂} at F(x) Hⁿ-a.e. and integrating additively gives the identity.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db, mathlib 25730c7c); git -C .lake/packages/simongmt rev-parse HEAD (2b366308)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); sed -n 1,457p GMT/Ch07/Submission.lean (IMRep, IMRep.action/Represents/measure, CompactlyContained)`
- `grep -n 'massOn|massAdmissibleOn|covectorEuclideanNorm' simongmt/Poincare/SimonGMT/Chapter06/Mass.lean; grep -n '^def|^abbrev|^structure' Chapter06/{Forms,Currents}.lean`
- `python3 -I dag.json scans: exact types/status of dor_lmb_pc_unitOrientation_comp, rsdic_exists_imrep_int_combination, rsdic_imrep_action_int_combination, imrep_weighted_orient_indicator_ae_eq; accepted lean_statements containing compContinuousLinearMap / AEStronglyMeasurable F / Integrable (fun x => (R.mult / covectorEuclideanNorm; children of pushforward_action_massOn_le_first_variation and dpf_pushforward_formula_current_exists`
- `git show faacb9cb5caf6ce728ef10ab3b0f5bdd7a47b04d:GMT/Ch07/Submission.lean (accepted Lean proof of rsdic_imrep_action_int_combination); git show 250899733c82:GMT/Ch07/Submission.lean (proof base = contract only)`
- `rg -n 'norm_compContinuousLinearMap_le|continuous_compContinuousLinearMapCLM|def compContinuousLinearMapCLM' local-references/123e8435b4a2469b/mathlib/Mathlib/{Analysis/Normed/Module/Alternating/Basic.lean,Topology/Algebra/Module/Alternating/Topology.lean}`
- `rg -n 'ContinuousOn.aestronglyMeasurable|enorm_integral_le_lintegral_enorm|ContDiffOn.continuousOn_fderiv_of_isOpen|withDensity_apply|lintegral_indicator|lintegral_const_mul|integrable_indicator_iff|integral_indicator|ae_restrict_iff' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `lake env lean /tmp/cm-decomp/Smoke.lean (#check of the cited Mathlib lemmas); lake env lean /tmp/cm-decomp/Types.lean; lake env lean /tmp/cm-decomp/Assembly.lean (#print axioms cm_assembly, cm_childA-D); lake env lean /tmp/cm-decomp/Final.lean (Submission.X comparator-style check)`
- `collision scans for dor_lmb_pc_cm_*: dag.json lean_name/lean_statement (0 hits), grep -rl nodes/ (0 hits), git grep over all 5852 ref objects -- GMT/Ch07/Submission.lean (0 hits; reviewer rescan over 5920 ref tips, 0 hits), rg over local-references project and mathlib (0 hits)`
- `sed -n 215,250p book/chapter-07.txt (7.2.4 (8)-(9)); sed -n 400,445p and 496,512p book/chapter-06.txt (2.23-2.24 push-forward formula, 2.29 mass bound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-projected-co-4ad1f13c76/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-projected-co-4ad1f13c76/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-projected-comparison-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-pushforwa-49ef3e5978/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-pushforwa-49ef3e5978/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`

Snapshot: project b4d606d, mathlib 25730c7c, SimonGMT 2b36630. The snapshot Contract.lean is byte-identical to the workspace Submission.lean, and the node's proof base 250899733c82 contains only the contract.

Reusable facts found:
- SimonGMT Chapter06/Mass.lean gives massOn as sSup of ofReal(T ω) over massAdmissibleOn (tsupport ω ⊆ W and covectorEuclideanNorm ≤ 1), together with le_massOn. No C¹ push-forward mass bound fits the competitor Z + f_#X on a general U.
- Accepted DAG declarations used:
  - rsdic_exists_imrep_int_combination, rsdic_imrep_action_int_combination and imrep_weighted_orient_indicator_ae_eq (step 1);
  - dpf_pfc_imrep_pairing_integrable_abs_le (integrability against bounded, compactly supported covector fields).
- dtc_bc_lc_pf_unitOrientation_comp and dimred_mbl_pf_unitOrientation_comp are accepted with a type byte-identical to the resolved dependency dor_lmb_pc_unitOrientation_comp (rlcr-lean).
- dimred_mbl_pfc_pullback_integrand_bound needs a compact K ⊆ O carrying M_X, which is not available here (only G ⊆ O), so it is not used.
- Mathlib provides:
  - for the pull-back field: ContinuousAlternatingMap.norm_compContinuousLinearMap_le, continuous_compContinuousLinearMapCLM, ContDiffOn.continuousOn_fderiv_of_isOpen, ContinuousOn.aestronglyMeasurable and aestronglyMeasurable_indicator_iff;
  - for the integrals: enorm_integral_le_lintegral_enorm, lintegral_indicator, lintegral_const_mul, withDensity_apply, integrable_indicator_iff, integral_indicator and ae_restrict_iff'.
- The four new names (dor_lmb_pc_cm_*) occur nowhere in dag.json, the node files, any git ref or the snapshot.
- An independent reviewer re-ran the checks in the comparator scope (verifier contract_scope) and accepted the split with no blocking issue:
  - assembly and child proofs: axioms propext, Classical.choice and Quot.sound only;
  - reused types byte-identical, with accepted checkpoints;
  - digest reproduced, no cycles, no collisions.

Lean checks:
- The child types elaborate in the comparator scope.
- The conditional assembly of the exact parent type, and trial proofs of all four new children from their declared dependencies, compile with axioms propext, Classical.choice and Quot.sound only.
