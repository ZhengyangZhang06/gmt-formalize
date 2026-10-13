# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_zero-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_zero-a1.imrep_point_sum-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 1 (i)–(iii) and the per-j listing of step 3. The multiplicity of each point is kept as an integer weight w = εθ instead of listing the point θ times with sign ε, and the mass is recorded through R.measure (the parent converts it to M_B with (MR)). Simon's printed proof of Ch. 6, 8.2 (book/chapter-06.txt lines 2322–2323) only says that "the theorem is trivial in case n = 0", so this argument is extracted and specialized from the parent-supplied proof (Part III, CL(0)).

Notation. M := R.carrier, θ := R.mult, ξ := R.orient. e : Fin 0 → ℝ^P is the empty family (Lean: fun i => i.elim0); every family Fin 0 → ℝ^P equals e (function extensionality over the empty type). Put ⟨α⟩ := α(e) for α ∈ Covector(ℝ^P, 0). H⁰ = μHE[0] = μH[0] (euclideanHausdorffMeasure_zero) and H⁰{p} = 1 (hausdorffMeasure_zero_singleton). Let K := closure B; since B ⊂⊂ U, K is compact and K ⊆ U.

1. Local finiteness. By the field locallyIntegrable_mult, I := ∫⁻_{M∩K} θ dH⁰ < ∞. Suppose M ∩ K were infinite. Pick n ∈ ℕ with I < n (ENNReal.exists_nat_gt) and an n-element finset F' ⊆ M ∩ K (Set.Infinite.exists_subset_card_eq). Since θ ≥ 1 on M (field mult_pos), n = Σ_{x∈F'} 1 ≤ Σ_{x∈F'} θ(x) = ∫⁻_{F'} θ dH⁰ (lower-integral identity of the sibling theorem cbrz_finset_integral_hausdorff_zero) ≤ ∫⁻_{M∩K} θ dH⁰ = I (lintegral_mono_set), contradicting I < n. So M ∩ K is finite, and G := M ∩ B ⊆ M ∩ K is finite (B ⊆ closure B). Regard G as a finset.
2. Orientation at every point of M. Let p ∈ M, and suppose no Q satisfies HasApproximateTangentSpaceAt 0 M p Q and IsUnitOrientationOf (ξ(p)) Q. Let Z be the set of points without such a Q. The field orients says (H⁰⌞M)(Z) = 0 (ae_iff); since {p} ⊆ Z, (H⁰⌞M){p} = 0 (measure_mono_null). But (H⁰⌞M){p} = H⁰({p} ∩ M) = H⁰{p} = 1 (Measure.restrict_apply with the measurable set {p}, and p ∈ M), a contradiction. Hence for each p ∈ M there are Q and τ : Fin 0 → ℝ^P with either ξ(p)(α) = α(τ) for all α, or ξ(p)(α) = −α(τ) for all α (definition of IsUnitOrientationOf). As τ = e, there is ε(p) ∈ {1, −1} ⊆ ℤ with ξ(p)(α) = ε(p)⟨α⟩ for every α ∈ Covector(ℝ^P, 0). Choose such ε(p) for each p ∈ M, and any value elsewhere.
3. Action. Let ω ∈ 𝒟^0(U) with tsupport ω ⊆ B. Since R represents S, S(ω) = R.action(ω) = ∫_M θ(x)ξ(x)(ω(x)) dH⁰. For x ∈ M ∖ G we have x ∉ B ⊇ tsupport ω, so ω(x) = 0 (image_eq_zero_of_notMem_tsupport) and θ(x)ξ(x)(0) = 0, ξ(x) being linear. M is measurable and G ⊆ M, so Mathlib setIntegral_eq_of_subset_of_forall_sdiff_eq_zero gives ∫_M θ(x)ξ(x)(ω(x)) dH⁰ = ∫_G θ(x)ξ(x)(ω(x)) dH⁰. The integral identity of the sibling theorem cbrz_finset_integral_hausdorff_zero turns this into Σ_{p∈G} θ(p)ξ(p)(ω(p)), which equals Σ_{p∈G} ε(p)θ(p)⟨ω(p)⟩ by step 2 (G ⊆ M).
4. Mass. G is finite, hence measurable, and G ⊆ M. Therefore R.measure(G) = ∫⁻_G θ d(H⁰⌞M) (withDensity_apply) = ∫⁻_{G∩M} θ dH⁰ (Measure.restrict_restrict) = ∫⁻_G θ dH⁰ = Σ_{p∈G} θ(p) (lower-integral identity of the sibling theorem). Since G ⊆ B, monotonicity of the measure gives Σ_{p∈G} θ(p) = R.measure(G) ≤ R.measure(B); no measurability of B is needed.
5. Listing. Let N := #G and enumerate G by the bijection Finset.equivFin: x_l := G.equivFin.symm(l) for l < N, and x_l := 0 for l ≥ N. Then Σ_{l<N} h(x_l) = Σ_{p∈G} h(p) for every function h into an additive commutative monoid (Finset.sum_range, Equiv.sum_comp, Finset.sum_coe_sort). Put w_l := ε(x_l)θ(x_l) ∈ ℤ. For l < N: x_l ∈ G ⊆ B; w_l ≠ 0, because ε(x_l) = ±1 and θ(x_l) ≥ 1 (x_l ∈ M); and |w_l| = θ(x_l). Hence Σ_{l<N} |w_l| = Σ_{p∈G} θ(p) ≤ R.measure(B) by step 4, and for ω as in step 3, S(ω) = Σ_{p∈G} ε(p)θ(p)⟨ω(p)⟩ = Σ_{l<N} w_l⟨ω(x_l)⟩. ∎

Appendix (not part of the mathematical argument). The following Lean tactic proof of exactly this frozen type compiled in this decomposition session as the body of `theorem Submission.cbrz_imrep_zero_local_point_sum : <frozen type> := by`, placed in `namespace GMT.Ch07` after `import GMT.Ch07.Submission` with the contract's opens (Lean v4.35.0-rc3, Mathlib 25730c7c, SimonGMT 2b36630), the sibling dependency entering only as `have hCI := Submission.cbrz_finset_integral_hausdorff_zero`; `#print axioms` reports only propext, Classical.choice, Quot.sound.
```lean
  have hCI := Submission.cbrz_finset_integral_hausdorff_zero
  intro P U B R S hRS hB
  classical
  -- Step 1: the carrier meets `closure B` in a finite set.
  have hfinK : (R.carrier ∩ closure B).Finite := by
    by_contra hinf
    have hint := R.locallyIntegrable_mult (closure B) hB.1 hB.2
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hint
    obtain ⟨F', hF'sub, hF'card⟩ := Set.Infinite.exists_subset_card_eq hinf n
    have h1 : (n : ℝ≥0∞) ≤ ∫⁻ x in R.carrier ∩ closure B, (R.mult x : ℝ≥0∞) ∂μHE[0] := by
      calc (n : ℝ≥0∞) = ∑ x ∈ F', (1 : ℝ≥0∞) := by simp [hF'card]
        _ ≤ ∑ x ∈ F', (R.mult x : ℝ≥0∞) := by
          apply Finset.sum_le_sum
          intro x hx
          exact Nat.one_le_cast.mpr (R.mult_pos x (hF'sub hx).1)
        _ = ∫⁻ x in (F' : Set (Euclid P)), (R.mult x : ℝ≥0∞) ∂μHE[0] :=
          ((hCI P F' (fun _ => 0) _).2).symm
        _ ≤ ∫⁻ x in R.carrier ∩ closure B, (R.mult x : ℝ≥0∞) ∂μHE[0] := lintegral_mono_set hF'sub
    exact absurd (hn.trans_le h1) (lt_irrefl _)
  -- Step 2: orientation at every carrier point, hence a sign.
  have hor : ∀ p ∈ R.carrier, ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt 0 R.carrier p Q ∧ IsUnitOrientationOf (R.orient p) Q := by
    intro p hp
    by_contra hcon
    have h := R.orients
    rw [ae_iff] at h
    have h0 : (μHE[0].restrict R.carrier) {p} = 0 :=
      measure_mono_null (fun z hz => by rw [mem_singleton_iff.mp hz]; exact hcon) h
    rw [Measure.restrict_apply (measurableSet_singleton p),
      inter_eq_left.mpr (singleton_subset_iff.mpr hp), Measure.euclideanHausdorffMeasure_zero,
      Measure.hausdorffMeasure_zero_singleton] at h0
    exact one_ne_zero h0
  have hsign : ∀ p ∈ R.carrier, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      ∀ α : Covector (Euclid P) 0, R.orient p α = (s : ℝ) * α (fun i => i.elim0) := by
    intro p hp
    obtain ⟨Q, -, τ, -, -, hτ⟩ := hor p hp
    have hτe : τ = fun i => i.elim0 := funext fun i => i.elim0
    subst hτe
    rcases hτ with h | h
    · exact ⟨1, Or.inl rfl, fun α => by simp [h α]⟩
    · exact ⟨-1, Or.inr rfl, fun α => by simp [h α]⟩
  choose! ε hε1 hε using hsign
  -- Step 3: the finite set `G = carrier ∩ B` and its enumeration.
  have hG : (R.carrier ∩ B).Finite := hfinK.subset (inter_subset_inter_right _ subset_closure)
  set Gf := hG.toFinset with hGf
  have hGfmem : ∀ p, p ∈ Gf ↔ p ∈ R.carrier ∩ B := fun p => hG.mem_toFinset
  have hGfcoe : (Gf : Set (Euclid P)) = R.carrier ∩ B := hG.coe_toFinset
  let e : ℕ → Euclid P := fun l => if h : l < Gf.card then (Gf.equivFin.symm ⟨l, h⟩ : Euclid P) else 0
  have he : ∀ l < Gf.card, e l ∈ Gf := by
    intro l hl
    simp only [e, dif_pos hl]
    exact (Gf.equivFin.symm ⟨l, hl⟩).2
  have hsum : ∀ {β : Type} [AddCommMonoid β] (h : Euclid P → β),
      ∑ l ∈ Finset.range Gf.card, h (e l) = ∑ p ∈ Gf, h p := by
    intro β _ h
    rw [Finset.sum_range]
    have h' : ∀ l : Fin Gf.card, e l = (Gf.equivFin.symm l : Euclid P) := by
      intro l
      simp only [e, dif_pos l.isLt, Fin.eta]
    simp_rw [h']
    rw [Equiv.sum_comp Gf.equivFin.symm (fun p : Gf => h p)]
    exact Finset.sum_coe_sort Gf h
  have hnat : ∀ p ∈ R.carrier, (ε p * (R.mult p : ℤ)).natAbs = R.mult p := by
    intro p hp
    rcases hε1 p hp with h | h <;> simp [h]
  refine ⟨Gf.card, fun l => ε (e l) * (R.mult (e l) : ℤ), e, ?_, ?_, ?_, ?_⟩
  · intro l hl
    exact ((hGfmem _).mp (he l hl)).2
  · intro l hl
    have hp := ((hGfmem _).mp (he l hl)).1
    have hm := R.mult_pos _ hp
    rcases hε1 _ hp with h | h <;> simp [h] <;> omega
  · calc (∑ l ∈ Finset.range Gf.card, (((ε (e l) * (R.mult (e l) : ℤ)).natAbs : ℕ) : ℝ≥0∞))
        = ∑ p ∈ Gf, (((ε p * (R.mult p : ℤ)).natAbs : ℕ) : ℝ≥0∞) :=
          hsum (fun p => (((ε p * (R.mult p : ℤ)).natAbs : ℕ) : ℝ≥0∞))
      _ = ∑ p ∈ Gf, (R.mult p : ℝ≥0∞) := by
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [hnat p ((hGfmem p).mp hp).1]
      _ = ∫⁻ x in (Gf : Set (Euclid P)), (R.mult x : ℝ≥0∞) ∂μHE[0] :=
          ((hCI P Gf (fun _ => 0) _).2).symm
      _ = R.measure (Gf : Set (Euclid P)) := by
          have hmeas : MeasurableSet (Gf : Set (Euclid P)) := Gf.finite_toSet.measurableSet
          rw [IMRep.measure, withDensity_apply _ hmeas, Measure.restrict_restrict hmeas,
            inter_eq_left.mpr (by rw [hGfcoe]; exact inter_subset_left)]
      _ ≤ R.measure B := measure_mono (by rw [hGfcoe]; exact inter_subset_right)
  · intro ω hω
    rw [hRS ω, IMRep.action]
    have hGsub : (Gf : Set (Euclid P)) ⊆ R.carrier := by rw [hGfcoe]; exact inter_subset_left
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero R.measurableSet_carrier hGsub]
    · rw [(hCI P Gf _ (fun _ => 0)).1]
      symm
      rw [hsum (fun p => ((ε p * (R.mult p : ℤ) : ℤ) : ℝ) *
        (ω : DifferentialForm (Euclid P) 0) p (fun i => i.elim0))]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [hε p ((hGfmem p).mp hp).1]
      push_cast
      ring
    · intro z hz
      have hzB : z ∉ B := by
        intro hzB
        apply hz.2
        rw [hGfcoe]
        exact ⟨hz.1, hzB⟩
      have hω0 : (ω : DifferentialForm (Euclid P) 0) z = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hzB (hω h))
      simp [hω0]
```

## Key steps

1. M ∩ closure B is finite: an n-point subset would force ∫_{M∩closure B} θ dH⁰ ≥ n for every n, contradicting local integrability (count_integral)
2. the a.e. orientation property holds at every carrier point because H⁰{p} = 1, so ξ(p) = ε(p)⟨·⟩ with ε(p) = ±1
3. for tsupport ω ⊆ B the action integral localises to the finite set G = M ∩ B and equals Σ_{p∈G} ε(p)θ(p)⟨ω(p)⟩ (count_integral)
4. R.measure(B) ≥ R.measure(G) = Σ_{p∈G} θ(p) (count_integral)
5. enumerate G and set w_l = ε(x_l)θ(x_l)

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); cmp GMT/Ch07/Contract.lean <snapshot>/project/GMT/Ch07/Contract.lean (identical); git -C .lake/packages/mathlib log -1 (25730c7c); git -C .lake/packages/simongmt log -1 and git -C lake-packages-25730c7c/simongmt log -1 (both 2b36630); cmp of SimonGMT Chapter03/Rectifiable.lean and Chapter06/{Currents,Mass,CurrentLocalEquality,Forms}.lean between the two package copies (identical)`
- `python3 -I scan of dag.json (902 nodes): lean_name in {cbrz_finset_integral_hausdorff_zero, cbrz_approxTangent_finite_zero, cbrz_isIntegerMultiplicity_point_sum, cbrz_imrep_zero_local_point_sum, cbrz_point_sum_limit} (none), lean_name prefix 'cbrz' (none), lean_statement identical to a proposed one (none); selected node record (status decomposing, message 'subproblem decomposition attempt 2', children []); frozen lean_statement of cbr_isIntegerMultiplicity_of_local; accepted statements containing 'IMRep U 0', 'IMRep V 0', 'μHE[0]', 'HasApproximateTangentSpaceAt 0', 'GeometricCurrentOn U 0' (dtc_dim_zero_carrier_finite, dor_zdm_imrep_zero_structure, regcomp_cop_zdr_unitOrientation_zero, regcomp_cop_zdr_setIntegral_eq_indicator, dtc_dim_zero_erase_point, dtc_point_current, ...)`
- `python3 -I substring scan of the five proposed names in all 807 nodes/*/decomposition-v*.json (only this node's decomposition-v1.json)`
- `read nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-68d9893f8c/{parent-child-handoff.json, parent-supplied-plan.md, parent-supplied-natural-proof.md, decomposition-v1.json, decomposition-review-receipt-v1.json, decomposition-review-receipt-v2.json, decomposition-audit-v1.json, decomposition-scope-v1.json}`
- `grep -rn --include=*.lean in <snapshot>/mathlib/Mathlib: 'euclideanHausdorffMeasure_zero', 'theorem hausdorffMeasure_zero_singleton', 'theorem lintegral_finset', 'theorem setIntegral_finset', 'theorem integrableOn_singleton', 'integrableOn_finite_biUnion', 'theorem setIntegral_eq_of_subset_of_forall_sdiff_eq_zero', 'theorem IsCompact.tendsto_subseq', 'theorem Finite.exists_infinite_fiber', 'theorem extraction_of_frequently_atTop', 'theorem isCompact_univ_pi', 'theorem tendsto_nhds_of_eventually_eq', 'Ioo_mem_nhdsGT', 'image_eq_zero_of_notMem_tsupport', 'theorem Countable.exists_eq_range', 'def apply' (ContinuousAlternatingMap.apply), 'theorem Continuous.eval_const', 'protected theorem exists_nat_gt' (ENNReal), 'theorem limsup_le_iSup', 'theorem liminf_le_limsup', 'DiscreteMeasurableSpace.toMeasurableAdd₂', 'theorem measurable_to_countable'', 'singleton_inter'`
- `grep -n / sed -n of /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT: Chapter03/Rectifiable.lean ('def CountablyRectifiable', 'theorem countablyRectifiable_of_measure_zero', 'theorem countablyRectifiable_range', 'theorem countablyRectifiable_iUnion', 'def blowUpMap', 'def HasApproximateTangentSpaceAt'); Chapter06/Currents.lean (testFormOnSubmodule, TestFormOn, GeometricCurrentOn, WeaklyConvergesOn); Chapter06/Mass.lean (massOn, massOn_mono, WeaklyConvergesOn.massOn_le_liminf); Chapter06/CurrentLocalEquality.lean (testFormOnInclusion, GeometricCurrentOn.restrictDomain, restrictDomain_apply); Chapter06/Forms.lean (Covector, DifferentialForm, IsSmoothForm, IsTestForm)`
- `grep -n '8.2\|trivial in case' book/chapter-06.txt; sed -n 2296,2330p book/chapter-06.txt (Simon Ch. 6, 8.2 statement and the remark 'the theorem is trivial in case n = 0')`
- `sed -n of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py: _decompose (1389-1560), _solve_children (1802-2000), _install_parent_supplied_child_handoff (1660-1730), _accepted_checkpoint (2365), _dependency_problem and _existing_lean_name_problem (6537-6600); swarm-project.json (max_children 12, max_depth 6, max_nodes 1000)`
- `git show 897839f250d247f64d81132474211f0ab45b65b3:GMT/Ch07/Submission.lean (accepted child theorems are declared as 'theorem Submission.X : <type> := by' in namespace GMT.Ch07 after the section 'end')`
- `python3 -I /tmp/cz0v2-8d3f/scripts/scope.py: verifier/lean_contract.py validate_lean_statement on the five statements (all OK, unchanged) and verifier/gmt-compare.py contract_scope(Contract.lean, GMT.Ch07.main_theorem) (replay: open Filter Function Set MeasureTheory Metric; open scoped ENNReal Topology; namespace GMT.Ch07; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt); noncomputable section; end)`
- `lake env lean /tmp/cz0v2-8d3f/lean/{Types,Assembly,C1,C2,C3,C4,Combined,SubStyle,Coe}.lean with toolchain lean-4.35.0-rc3 (#print axioms: the five children and the hypothesis-only assembly use [propext, Classical.choice, Quot.sound]; the parent declared from the children plus an im_local stub adds only sorryAx)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/SumMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fintype/Pigeonhole.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Neighborhoods.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Hom/ContinuousEvalConst.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Group/Arithmetic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Insert.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-68d9893f8c/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-68d9893f8c/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-68d9893f8c/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-68d9893f8c/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-68d9893f8c/decomposition-review-receipt-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/cz0v2-8d3f/lean/Types.lean`
- `/tmp/cz0v2-8d3f/lean/Assembly.lean`
- `/tmp/cz0v2-8d3f/lean/Combined.lean`
- `/tmp/cz0v2-8d3f/lean/SubStyle.lean`
- `/tmp/cz0v2-8d3f/lean/Coe.lean`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean (project b4d606db, Mathlib 25730c7c, SimonGMT 2b36630), and the two SimonGMT package copies agree on every file used. Neither the snapshot Mathlib nor SimonGMT contains a degree-0 closure theorem, a finite-set approximate-tangent lemma, or a point-sum-is-IM lemma. SimonGMT Chapter03 supplies only the definitions and basic closure properties of CountablyRectifiable and HasApproximateTangentSpaceAt, and Chapter06 supplies currents, mass, lower semicontinuity of mass and domain restriction. In the DAG, the accepted degree-0 lemmas of other branches are only partial tools, and no node has a lean_statement identical to a proposed child, so the split is new and no cross-branch node is reused. Every Mathlib and SimonGMT lemma cited in the child proofs exists in the pinned versions and was used in proofs that compiled. The five cbrz_* names collide with no DAG node, no other decomposition file and no declaration. All five exact lean_statements pass the verifier lexical check unchanged and elaborate in the replayed contract scope. A hypothesis-only assembly proves the frozen parent type from imrep_point_sum, point_sum_limit, point_sum_im and the frozen im_local type. Complete Lean proofs of all five children compile in Submission form using only propext, Classical.choice and Quot.sound.
