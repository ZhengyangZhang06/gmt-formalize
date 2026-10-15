# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.projected_comparison-a1.competitor_mass-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.projected_comparison-a1.competitor_mass-a1.vd_add-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 of the parent-supplied proof of the selected node. That step is the vector-measure identity behind the competitor mass bound in Simon's proof of 7.2.4, (8)–(9) (chapter-07.txt lines 222–246), for Y = Z + X. The three accepted siblings comb_exists, comb_action and density_unique are used exactly as in that step, and the a.e. bookkeeping of its part (d) is written out.
Notation. H := μHE[n]. For an IMRep R' = (M', θ', ξ') in U put ν_{R'}(x) := 1_{M'}(x)θ'(x)ξ'(x) ∈ MultiVector P n, i.e. ν_{R'} = M'.indicator (y ↦ (θ'(y) : ℝ) • ξ'(y)), and τ(R')(ω) := R'.action ω = ∫_{M'} θ'(x)ξ'(x)(ω(x)) dH(x). Write R₁ = (M₁, θ₁, ξ₁), R₂ = (M₂, θ₂, ξ₂), R = (M, θ, ξ).
1. A combination representative. Apply the sibling comb_exists (Submission.rsdic_exists_imrep_int_combination) to U (open), R₁, R₂ and the integers p₁ = p₂ = 1. It gives an IMRep R' = (M', θ', ξ') in U with ν_{R'}(x) = ((1 : ℤ) : ℝ)•ν_{R₁}(x) + ((1 : ℤ) : ℝ)•ν_{R₂}(x) = ν_{R₁}(x) + ν_{R₂}(x) for H-a.e. x.
2. R' represents T. Fix ω ∈ 𝒟ⁿ(U). Apply the sibling comb_action (Submission.rsdic_imrep_action_int_combination) to R₁, R₂, R', p₁ = p₂ = 1 and the a.e. identity of step 1: τ(R')(ω) = 1·τ(R₁)(ω) + 1·τ(R₂)(ω) = τ(R₁)(ω) + τ(R₂)(ω). By hypothesis the right side equals T(ω). Hence T(ω) = R'.action ω for every ω ∈ 𝒟ⁿ(U), i.e. R'.Represents T.
3. Agreement on the carriers. R' and R both represent T, and U is open. The sibling density_unique (Submission.imrep_weighted_orient_indicator_ae_eq), applied to T, R' and R, gives ν_{R'}(x) = ν_R(x) for H⌞(M' ∪ M)-a.e. x. Each carrier is measurable (measurableSet_carrier), so M' ∪ M is measurable. The statement is therefore equivalent to: for H-a.e. x, x ∈ M' ∪ M ⟹ ν_{R'}(x) = ν_R(x) (Mathlib ae_restrict_iff').
4. Agreement off the carriers. If x ∉ M' ∪ M, then x ∉ M' and x ∉ M. An indicator vanishes off its set, so ν_{R'}(x) = 0 = ν_R(x).
5. Conclusion. The points x where both the implication of step 3 and the identity of step 1 hold form an H-conull set (the intersection of two H-conull sets). At such an x, steps 3–4 give ν_R(x) = ν_{R'}(x), whether or not x ∈ M' ∪ M. Step 1 gives ν_{R'}(x) = ν_{R₁}(x) + ν_{R₂}(x). Hence ν_R(x) = ν_{R₁}(x) + ν_{R₂}(x) for H-a.e. x, which is the assertion. ∎

Lean implementation notes (context, not part of the numbered proof). The script below was checked with `lake env lean` after `import GMT.Ch07.Submission` in namespace GMT.Ch07 with the contract's opens, as the body of `theorem Submission.dor_lmb_pc_cm_vector_density_add : <frozen type> := by`; the three siblings were declared as Submission.X stand-ins with their exact frozen types. #print axioms reports propext, Classical.choice, Quot.sound and sorryAx; sorryAx enters only through the sibling stand-ins. The same script with the siblings passed as hypotheses of their exact frozen types uses only propext, Classical.choice and Quot.sound.
```lean
  intro P n U R₁ R₂ R T hU hR hT
  obtain ⟨R', hR'⟩ := Submission.rsdic_exists_imrep_int_combination P n U R₁ R₂ 1 1 hU
  have hR'T : R'.Represents T := by
    intro ω
    rw [hT ω, Submission.rsdic_imrep_action_int_combination P n U R₁ R₂ R' 1 1 hR' ω]
    simp
  have h1 := Submission.imrep_weighted_orient_indicator_ae_eq P n U T R' R hU hR'T hR
  rw [ae_restrict_iff' (R'.measurableSet_carrier.union R.measurableSet_carrier)] at h1
  filter_upwards [h1, hR'] with x hx hx'
  by_cases hxs : x ∈ R'.carrier ∪ R.carrier
  · rw [← hx hxs, hx']
    simp
  · have h1' : x ∉ R'.carrier := fun h => hxs (Or.inl h)
    have h2' : x ∉ R.carrier := fun h => hxs (Or.inr h)
    rw [Set.indicator_of_notMem h2', ← Set.indicator_of_notMem h1'
      (fun y => (R'.mult y : ℝ) • R'.orient y), hx']
    simp
```

## Key steps

1. comb_exists with p₁ = p₂ = 1 gives an IMRep R' with ν_{R'} = ν_{R₁} + ν_{R₂} Hⁿ-a.e.
2. comb_action turns this into R'.action ω = τ(R₁)(ω) + τ(R₂)(ω) = T(ω), so R' represents T.
3. density_unique gives ν_{R'} = ν_R Hⁿ⌞(M' ∪ M)-a.e.; off M' ∪ M both indicators vanish, so ν_{R'} = ν_R Hⁿ-a.e.
4. Combining the two a.e. identities gives ν_R = ν_{R₁} + ν_{R₂} Hⁿ-a.e.

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
