# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.integer_density-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.integer_density-a1.signed_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 5 and 7 of the parent-supplied proof of dgcr_graph_integer_density_on_graph ('The density on Σ' and 'Representation'), with the cylinder C and the graph Σ replaced by arbitrary sets W and S (S Borel), with the null-set fact (*) of step 3 and the sign conclusion (**) of step 4 taken as hypotheses, and with continuity of β on Σ weakened to a.e.-strong measurability for Hⁿ⌞S (which is all step 5(d) uses). The conclusion starts from R.action ω. Two pieces stay in the parent: the first equality T(ω) = ∫_M θξ_R(ω) dHⁿ of step 7 (R.Represents T), and the sign identification of step 4 (via its prerequisites AT and SG). In the grandparent proof this is the construction of g in step 11 and the second and third equalities of step 12(c). The argument is copied. The only change is that step 7's ∫_M = ∫_{M∩C} = ∫_{M∩Σ} are merged into one step, 'the integrand vanishes a.e. on M ∖ S', so no measurability of W and no inclusion S ⊆ W is needed.
Notation: Hⁿ := μHE[n]; M := R.carrier (Borel, R.measurableSet_carrier); θ := R.mult; ξ_R := R.orient; 1_M is the indicator of M; ‖·‖ₑ is the extended norm, so ‖g(x)‖ₑ = |g(x)| ∈ [0, ∞]. The witness is g := 1_M·θ·ξ_R(β), i.e. g(x) := θ(x)·ξ_R(x)(β(x)) for x ∈ M and g(x) := 0 for x ∉ M (Set.indicator M (fun x => (θ x : ℝ) * ξ_R x (β x))).
Formalization note: unless this child is split further it is a machine leaf: one theorem appended to the frozen GMT/Ch07/Submission.lean (inside `namespace Submission`), with no new import and no helper declaration. It uses no sibling or uncle declaration; every lemma cited below is in the import closure of GMT.Ch07.Submission (Mathlib 25730c7c, simongmt 2b36630, project b4d606d).
1. Sign set. Since M ∩ S is Borel, ae_restrict_iff' turns the sign hypothesis into (†): for Hⁿ-a.e. x ∈ ℝ^P, if x ∈ M ∩ S then ξ_R(x) = ξ(x) or ξ_R(x) = −ξ(x).
2. Pointwise identities. Let x ∈ M ∩ S with ξ_R(x) = εξ(x), ε ∈ {1, −1}. Since x ∈ S, ξ(x)(β(x)) = 1, so ξ_R(x)(β(x)) = ε (for ε = −1 use (−ξ(x))(a) = −(ξ(x)(a)), neg_apply) and g(x) = θ(x)·ε. Consequently: (a) g(x) = m for the integer m := θ(x) if ε = 1 and m := −θ(x) if ε = −1; (b) ‖g(x)‖ₑ = |±θ(x)| = θ(x); (c) for every n-covector α, θ(x)·ξ_R(x)(α) = θ(x)·ε·ξ(x)(α) = g(x)·ξ(x)(α).
3. Proof of (ii). Hⁿ⌞S-a.e. x satisfies (†) (ae_restrict_of_ae) and lies in S (ae_restrict_mem, S Borel). Fix such an x. If x ∈ M, then x ∈ M ∩ S, (†) gives a sign, and step 2(a),(b) give g(x) ∈ ℤ and ‖g(x)‖ₑ = θ(x) = 1_M(x)·θ(x). If x ∉ M, then g(x) = 0 = ((0 : ℤ) : ℝ) is an integer and ‖g(x)‖ₑ = 0 ≤ 1_M(x)·θ(x) (indicator_of_notMem for both indicators).
4. Proof of (i). As M is Borel, aestronglyMeasurable_indicator_iff reduces (i) to a.e.-strong measurability of f₀(x) := θ(x)·ξ_R(x)(β(x)) for (Hⁿ⌞S)⌞M = Hⁿ⌞(M ∩ S) (Measure.restrict_restrict, M measurable). Now: x ↦ (θ(x) : ℝ) is measurable (cast of the measurable ℕ-valued R.measurable_mult), hence a.e.-strongly measurable; ξ_R is a.e.-strongly measurable for Hⁿ⌞M (R.aestronglyMeasurable_orient), hence for the smaller measure Hⁿ⌞(M ∩ S) ≤ Hⁿ⌞M (AEStronglyMeasurable.mono_measure, Measure.restrict_mono); β is a.e.-strongly measurable for Hⁿ⌞S, hence for Hⁿ⌞(M ∩ S) ≤ Hⁿ⌞S. The evaluation map (L, a) ↦ L(a) from Λₙ(ℝ^P) × Λⁿ(ℝ^P) to ℝ is continuous (Continuous.clm_apply), so x ↦ ξ_R(x)(β(x)) is a.e.-strongly measurable (Continuous.comp_aestronglyMeasurable₂), and so is the product f₀ (AEStronglyMeasurable.mul).
5. Proof of (iii). Fix ω with tsupport ω ⊆ W. If x ∉ W then x ∉ tsupport ω, so ω(x) = 0 (image_eq_zero_of_notMem_tsupport). Put f(x) := θ(x)·ξ_R(x)(ω(x)), so R.action ω = ∫_M f dHⁿ (unfold IMRep.action).
 (a) ∫_M f dHⁿ = ∫_{M∩S} f dHⁿ. Here M ∩ S ⊆ M, M is (null-)measurable, and f vanishes Hⁿ-a.e. on M ∖ (M ∩ S): Hⁿ-a.e. x lies outside the null set (M ∩ W) ∖ S (measure_eq_zero_iff_ae_notMem); if such an x lies in M ∖ (M ∩ S), then x ∈ M and x ∉ S, so x ∉ W (otherwise x ∈ (M ∩ W) ∖ S), hence ω(x) = 0 and f(x) = θ(x)·ξ_R(x)(0) = 0 (map_zero). Apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero.
 (b) ∫_{M∩S} f dHⁿ = ∫_{M∩S} g·ξ(ω) dHⁿ. By (†) and step 2(c) with α := ω(x), f(x) = g(x)·ξ(x)(ω(x)) for Hⁿ-a.e. x ∈ M ∩ S (g(x) = θ(x)ξ_R(x)(β(x)) there by indicator_of_mem). Apply setIntegral_congr_ae with the measurable set M ∩ S.
 (c) ∫_S g·ξ(ω) dHⁿ = ∫_{M∩S} g·ξ(ω) dHⁿ. Here M ∩ S ⊆ S, S is measurable, and for x ∈ S ∖ (M ∩ S) we have x ∉ M, so g(x) = 0 and the integrand g(x)·ξ(x)(ω(x)) is 0. Apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero.
 Combining, R.action ω = ∫_M f = ∫_{M∩S} f = ∫_{M∩S} g·ξ(ω) = ∫_S g·ξ(ω) dHⁿ. Each equality only compares integrands a.e. on a domain or discards a set where the integrand vanishes (a.e.), so it holds for Bochner integrals with no integrability hypothesis (if one side is not integrable, neither is the other and both are 0).
6. The function g of the notation satisfies (i), (ii) and (iii) by steps 4, 3 and 5. ∎

Checked Lean rendering of steps above (compiled with `lake env lean` after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` / `namespace Submission` with the contract's opens; `#print axioms` reports only propext, Classical.choice, Quot.sound; it also passes the leaf source-delta rule):
```lean
theorem dgid_imrep_signed_density_representation : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (W S : Set (Euclid P)) (ξ : Euclid P → MultiVector P n) (β : Euclid P → Covector (Euclid P) n), MeasurableSet S → μHE[n] ((R.carrier ∩ W) \ S) = 0 → AEStronglyMeasurable β (μHE[n].restrict S) → (∀ x ∈ S, ξ x (β x) = 1) → (∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ S)), R.orient x = ξ x ∨ R.orient x = -ξ x) → ∃ g : Euclid P → ℝ, AEStronglyMeasurable g (μHE[n].restrict S) ∧ (∀ᵐ x ∂(μHE[n].restrict S), (∃ m : ℤ, g x = m) ∧ ‖g x‖ₑ ≤ R.carrier.indicator (fun y => (R.mult y : ℝ≥0∞)) x) ∧ ∀ ω : DifferentialForm (Euclid P) n, tsupport ω ⊆ W → R.action ω = ∫ x in S, g x * ξ x (ω x) ∂μHE[n] := by
  intro P n U R W S ξ β hS hnull hβ hξβ hor
  have hM : MeasurableSet R.carrier := R.measurableSet_carrier
  have hor' : ∀ᵐ x ∂μHE[n], x ∈ R.carrier ∩ S → (R.orient x = ξ x ∨ R.orient x = -ξ x) :=
    (ae_restrict_iff' (hM.inter hS)).mp hor
  -- pointwise identities on the sign set
  have hpt : ∀ x ∈ R.carrier ∩ S, (R.orient x = ξ x ∨ R.orient x = -ξ x) →
      (∃ m : ℤ, (R.mult x : ℝ) * R.orient x (β x) = m) ∧
      ‖(R.mult x : ℝ) * R.orient x (β x)‖ₑ = (R.mult x : ℝ≥0∞) ∧
      ∀ α : Covector (Euclid P) n,
        (R.mult x : ℝ) * R.orient x α = (R.mult x : ℝ) * R.orient x (β x) * ξ x α := by
    intro x hx hsign
    rcases hsign with hs | hs
    · rw [hs, hξβ x hx.2, mul_one]
      exact ⟨⟨R.mult x, by push_cast; rfl⟩, by simp, fun α => rfl⟩
    · rw [hs, neg_apply, hξβ x hx.2]
      refine ⟨⟨-(R.mult x : ℤ), by push_cast; ring⟩, by simp, fun α => ?_⟩
      rw [neg_apply]; ring
  refine ⟨R.carrier.indicator (fun x => (R.mult x : ℝ) * R.orient x (β x)), ?_, ?_, ?_⟩
  · -- measurability
    rw [aestronglyMeasurable_indicator_iff hM, Measure.restrict_restrict hM]
    have h1 : AEStronglyMeasurable (fun x => (R.mult x : ℝ)) (μHE[n].restrict (R.carrier ∩ S)) :=
      (measurable_from_nat.comp R.measurable_mult).aestronglyMeasurable
    have h2 : AEStronglyMeasurable R.orient (μHE[n].restrict (R.carrier ∩ S)) :=
      R.aestronglyMeasurable_orient.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
    have h3 : AEStronglyMeasurable β (μHE[n].restrict (R.carrier ∩ S)) :=
      hβ.mono_measure (Measure.restrict_mono inter_subset_right le_rfl)
    have h4 : AEStronglyMeasurable (fun x => R.orient x (β x)) (μHE[n].restrict (R.carrier ∩ S)) :=
      (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂ h2 h3
    exact h1.mul h4
  · -- integrality and bound
    filter_upwards [ae_restrict_of_ae hor', ae_restrict_mem hS] with x hx hxS
    by_cases hxM : x ∈ R.carrier
    · obtain ⟨hint, hnorm, -⟩ := hpt x ⟨hxM, hxS⟩ (hx ⟨hxM, hxS⟩)
      rw [indicator_of_mem hxM, indicator_of_mem hxM]
      exact ⟨hint, hnorm.le⟩
    · rw [indicator_of_notMem hxM, indicator_of_notMem hxM]
      exact ⟨⟨0, by simp⟩, by simp⟩
  · -- representation
    intro ω hω
    have hω0 : ∀ x, x ∉ W → ω x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun h => hx (hω h))
    have e1 : ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (ω x) ∂μHE[n] =
        ∫ x in R.carrier ∩ S, (R.mult x : ℝ) * R.orient x (ω x) ∂μHE[n] := by
      apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hM.nullMeasurableSet inter_subset_left
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx hxd
      have hxW : x ∉ W := fun hxW => hx ⟨⟨hxd.1, hxW⟩, fun hxS => hxd.2 ⟨hxd.1, hxS⟩⟩
      rw [hω0 x hxW, map_zero, mul_zero]
    have e2 : ∫ x in R.carrier ∩ S, (R.mult x : ℝ) * R.orient x (ω x) ∂μHE[n] =
        ∫ x in R.carrier ∩ S, R.carrier.indicator (fun x => (R.mult x : ℝ) * R.orient x (β x)) x *
          ξ x (ω x) ∂μHE[n] := by
      apply setIntegral_congr_ae (hM.inter hS)
      filter_upwards [hor'] with x hx hxMS
      rw [indicator_of_mem hxMS.1]
      exact (hpt x hxMS (hx hxMS)).2.2 (ω x)
    have e3 : ∫ x in S, R.carrier.indicator (fun x => (R.mult x : ℝ) * R.orient x (β x)) x *
          ξ x (ω x) ∂μHE[n] =
        ∫ x in R.carrier ∩ S, R.carrier.indicator (fun x => (R.mult x : ℝ) * R.orient x (β x)) x *
          ξ x (ω x) ∂μHE[n] := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hS inter_subset_right
      intro x hx
      have hxM : x ∉ R.carrier := fun hxM => hx.2 ⟨hxM, hx.1⟩
      rw [indicator_of_notMem hxM, zero_mul]
    rw [IMRep.action, e1, e2, e3]
```

## Key steps

1. Take g := 1_M·θ·ξ_R(β). By ae_restrict_iff', ξ_R = ±ξ holds Hⁿ-a.e. on M ∩ S; there ξ(β) = 1 gives g = ±θ ∈ ℤ, |g| = θ and θ·ξ_R(α) = g·ξ(α) for every covector α.
2. Off M, g = 0; hence g ∈ ℤ and ‖g‖ₑ ≤ 1_M·θ Hⁿ⌞S-a.e.
3. aestronglyMeasurable_indicator_iff, restrict_restrict, mono_measure for ξ_R and β, and continuity of evaluation (clm_apply, comp_aestronglyMeasurable₂) give a.e.-strong measurability of g for Hⁿ⌞S.
4. For tsupport ω ⊆ W: ∫_M θξ_R(ω) = ∫_{M∩S} θξ_R(ω) (integrand vanishes a.e. on M ∖ S, using ω = 0 off W and Hⁿ((M ∩ W) ∖ S) = 0) = ∫_{M∩S} g·ξ(ω) (setIntegral_congr_ae) = ∫_S g·ξ(ω) (g = 0 on S ∖ M).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD vs manifest.json project_commit`
- `rg -n "theorem setIntegral_eq_of_subset_of_ae_diff_eq_zero|theorem setIntegral_eq_of_subset_of_forall_diff_eq_zero|theorem setIntegral_congr_ae|theorem aestronglyMeasurable_indicator_iff|theorem locallyIntegrableOn_iff|theorem ae_of_ae_map|theorem lintegral_map'|theorem lintegral_indicator_one|theorem measure_compl_support|theorem ae_restrict_iff'|theorem ae_restrict_of_ae_restrict_of_subset|theorem lintegral_indicator\b|theorem withDensity_apply\b|theorem restrict_restrict\b" mathlib/Mathlib`
- `sed -n 425,480p mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `rg -n "aestronglyMeasurable_indicator_iff|theorem comp_aemeasurable|theorem mono_measure|theorem mono_set" mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `rg -n "measure_eq_zero_iff_ae_notMem|image_eq_zero_of_notMem_tsupport" mathlib/Mathlib`
- `rg -n "lemma measure_compl_support|lemma isClosed_support|theorem setLIntegral_one|theorem setLIntegral_mono'|Continuous.comp_aestronglyMeasurable₂|theorem Continuous.clm_apply|theorem ae_mono|lemma IsOpen.isLocallyClosed|theorem ae_restrict_mem|theorem IsCompact.image_of_continuousOn|theorem le_iff|theorem hasFiniteIntegral_iff_enorm|def LocallyIntegrableOn" mathlib/Mathlib`
- `rg -n "notation.*μHE|EuclideanSpace.euclideanHausdorffMeasure_eq_volume" mathlib/Mathlib`
- `grep -n "abbrev Covector|abbrev DifferentialForm|def IsTestForm|abbrev TestFormOn|structure GeometricCurrentOn" simongmt Chapter06/Forms.lean Chapter06/Currents.lean`
- `rg -n "withDensity.*support|measure_compl_support|Measure.map .* ≤ .*restrict|ae_of_ae_map" simongmt/Poincare/SimonGMT; rg -ln "IMRep|IntegerMultiplicity" simongmt/Poincare/SimonGMT`
- `python3 scan of dag.json lean_names and lean_statements for dgid_, 'R.carrier \ … support', 'IsOpen {x | ∃ v ∈ ball', 'Measure.map … μHE'; grep -rl dgid_ nodes/ dag.json; git grep -l dgid_ over all refs`
- `read runtime.py (_solve_children, _overlay_accepted_children, _wait_for_accepted_dependencies, _publish_decomposition_workspace), leaf_verification.check_source_delta, parent_verification.check_parent_git_delta, gmt-compare.py contract_scope/child_modules, lean_contract.validate_lean_statement`
- `lake env lean /tmp/gid-work/{Challenges,Assembly,C1,C3,C4,Full,Full2}.lean (#print axioms; comparator-style targets `theorem _root_.HumanizeNodeComparator.target : (<type>) := by exact Submission.<name>`); python simulation of check_source_delta for each child; independent reviewer re-ran these plus a full-Submission simulation with the four prerequisites as axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/CompleteLattice.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Filter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/HasFiniteIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/RadonCompactDecomposition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter07/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-83ad345463/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-regular-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-regular-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-b5ecd87c13/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/runtime/flows/gmt-claude-07a3972eec1d/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-07a3972eec1d/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-07a3972eec1d/_recursive_lean/parent_verification.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/gid-work/Challenges.lean`
- `/tmp/gid-work/C1.lean`
- `/tmp/gid-work/C3.lean`
- `/tmp/gid-work/C4.lean`
- `/tmp/gid-work/Full2.lean`

Snapshot = project b4d606d + Mathlib 25730c7c (manifest). Its Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. Every lemma cited in the four child proofs exists under that name in the pinned Mathlib. Locations:
- withDensity_apply: WithDensity.lean:44.
- Measure.restrict_restrict: Restrict.lean:205. ae_restrict_iff', ae_restrict_mem, ae_restrict_of_ae and ae_restrict_of_ae_restrict_of_subset are in the same file.
- Measure.isClosed_support and measure_compl_support: Support.lean:115 and :202.
- setLIntegral_one and setLIntegral_mono': Lebesgue/Basic.lean:124 and :254. lintegral_indicator and lintegral_indicator_one are in the same file.
- lintegral_map': Lebesgue/Map.lean:36. ae_of_ae_map: Measure/Map.lean:253. Measure.le_iff: CompleteLattice.lean:41. ae_mono: Measure/Filter.lean:54.
- aestronglyMeasurable_indicator_iff, mono_measure, mono_set, comp_aemeasurable and Continuous.comp_aestronglyMeasurable₂: AEStronglyMeasurable.lean.
- Continuous.clm_apply: BoundedLinearMaps.lean:471.
- ContinuousOn.aemeasurable and ContinuousOn.aestronglyMeasurable: IntegrableOn.lean:754 and :791.
- locallyIntegrableOn_iff: LocallyIntegrable.lean:188 (takes IsLocallyClosed; IsOpen.isLocallyClosed is in Topology/Basic.lean:143).
- hasFiniteIntegral_iff_enorm: HasFiniteIntegral.lean:90. measure_eq_zero_iff_ae_notMem: OuterMeasure/AE.lean:145.
Naming caveat: in this Mathlib the set-integral subset lemmas are setIntegral_eq_of_subset_of_ae_sdiff_eq_zero and setIntegral_eq_of_subset_of_forall_sdiff_eq_zero. The `_diff_` names are deprecated aliases (2026-06-03). ContinuousLinearMap.neg_apply is deprecated in favour of root neg_apply. The child proofs cite the current names.
No existing declaration supplies any child:
- The project snapshot has only the frozen contract.
- simongmt has Radon-support facts (Chapter01/RadonCompactDecomposition) but nothing about the contract's IMRep.measure, and no push-forward domination lemma.
- The DAG has no dgid_* name. Two lookalikes differ: imrep_carrier_sdiff_support_null is about T.support with IsOpen U and Represents, and dorag_gc_graph_map_volume_le_measure is another branch with different hypotheses.
Runtime facts that shape the split: a child's proof base is the parent's dispatch commit and depends_on is sibling-only, so the children must not use this node's prerequisites (DEC, MB, AT, SG); leaves may append exactly one theorem.
Lean verification:
- All four child types pass validate_lean_statement and elaborate in the comparator scope.
- All four are proved in full against the frozen base, using only propext, Classical.choice and Quot.sound, and pass the leaf-delta rule.
- The parent's frozen type follows from the four children plus the four prerequisites at their exact DAG types, via the 52-line assembly in the rationale.
