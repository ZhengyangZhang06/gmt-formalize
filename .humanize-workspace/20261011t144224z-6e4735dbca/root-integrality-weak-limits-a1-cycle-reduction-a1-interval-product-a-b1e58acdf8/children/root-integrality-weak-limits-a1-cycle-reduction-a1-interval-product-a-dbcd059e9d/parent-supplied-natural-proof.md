# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1`
- Child DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1.plane_fubini-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 3(b) and Step 15 of the parent proof ((MP) applies to the plane T = span τ; change of variables along Φ′ and Fubini for the compactly supported continuous integrand f∘Φ′).

Notation. E := ℝ^P = Eucl P, E′ := ℝ^{P+1} = Eucl (P+1), Hᵏ := μHE[k], L¹ := volume on ℝ. Φ(s, u) := (EuclideanSpace.equiv (Fin (P+1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ u)); π(y) := (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P+1)) ℝ y)); y₀ := (EuclideanSpace.equiv (Fin (P+1)) ℝ y) 0; Φ′ : ℝ × E → E′, Φ′(p) := Φ(p.1, p.2). (MP) is the hypothesis: for every A ⊆ E that is Hᵐ-null-measurable, countably m-rectifiable and has Hᵐ(A ∩ K) < ∞ for every compact K, H^{m+1}⌞{y : π(y) ∈ A} = Φ′_*(L¹ ⊗ Hᵐ⌞A). T := span ℝ (range τ).

1. (Φ′ is a homeomorphism.) Φ′ is continuous: p ↦ Fin.cons p.1 (EuclideanSpace.equiv p.2) is continuous (Continuous.finCons with continuous_fst and the continuous equivalence composed with continuous_snd), and so is the inverse equivalence. The map y ↦ (y₀, π(y)) is continuous (coordinate projections, continuous_pi, continuous_apply). They are mutually inverse: (Φ(s, u)₀, π(Φ(s, u))) = (s, u) by Fin.cons_zero, Fin.tail_cons and ContinuousLinearEquiv.apply_symm_apply/symm_apply_apply; and Φ(y₀, π(y)) = y because both sides have the same image under the injective EuclideanSpace.equiv (Fin.cons_self_tail). Hence Φ′ underlies a homeomorphism e : ℝ × E ≃ₜ E′, and Φ′ is a measurable embedding (Homeomorph.measurableEmbedding).
2. (dim T = m.) τ is orthonormal, hence linearly independent (Orthonormal.linearIndependent), so finrank ℝ T = card (Fin m) = m (finrank_span_eq_card, Fintype.card_fin).
3. (T is null-measurable.) T is a finite-dimensional subspace, hence closed (Submodule.closed_of_finiteDimensional), hence Borel measurable, hence Hᵐ-null-measurable.
4. (T is countably m-rectifiable.) Let Λₗ : EuclideanSpace ℝ (Fin m) →ₗ E be Λₗ(u) := Σ_i u_i·τ_i (Fintype.linearCombination ℝ τ composed with EuclideanSpace.equiv (Fin m) ℝ). Its domain is finite-dimensional, so Λₗ is a continuous linear map Λ (LinearMap.toContinuousLinearMap), and Λ is Lipschitz (ContinuousLinearMap.lipschitzWith). range Λ = T: if v = Λ(u) then v = Σ_i u_i τ_i ∈ T; conversely, if v ∈ T then v = Σ_i c_i τ_i for some c : Fin m → ℝ (Submodule.mem_span_range_iff_exists_fun) and v = Λ((EuclideanSpace.equiv (Fin m) ℝ).symm c). Hence T = range Λ is countably m-rectifiable (Poincare.SimonGMT.Chapter03.countablyRectifiable_range).
5. (T is locally Hᵐ-finite.) Since finrank T = m (step 2), the measure Hᵐ⌞T is regular (Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule), in particular finite on compact sets. For compact K (closed, hence Borel), Hᵐ(T ∩ K) = Hᵐ(K ∩ T) = (Hᵐ⌞T)(K) < ∞ (Measure.restrict_apply, IsCompact.measure_lt_top). Also Hᵐ⌞T is σ-finite (finite on compacts in the σ-compact space E).
6. (Apply (MP).) Steps 3–5 verify the three hypotheses of (MP) for A = T, so H^{m+1}⌞{z : π(z) ∈ T} = Φ′_*(L¹ ⊗ Hᵐ⌞T).
7. (Change of variables.) ∫_{{z : π(z) ∈ T}} f dH^{m+1} = ∫ f d(H^{m+1}⌞{π ∈ T}) = ∫ f d(Φ′_*(L¹ ⊗ Hᵐ⌞T)) (step 6) = ∫ f∘Φ′ d(L¹ ⊗ Hᵐ⌞T) (MeasurableEmbedding.integral_map, step 1; valid for every integrand).
8. (Integrability.) f∘Φ′ = f∘e is continuous and has compact support, because e is a homeomorphism and f has compact support (HasCompactSupport.comp_homeomorph). L¹ and Hᵐ⌞T are finite on compact sets and σ-finite, so their product is finite on compact sets (instance Measure.prod.instIsFiniteMeasureOnCompacts). A continuous function with compact support is integrable for a measure that is finite on compact sets (Continuous.integrable_of_hasCompactSupport). Hence f∘Φ′ is (L¹ ⊗ Hᵐ⌞T)-integrable.
9. (Fubini.) By integral_prod (step 8; Hᵐ⌞T s-finite), ∫ f∘Φ′ d(L¹ ⊗ Hᵐ⌞T) = ∫_ℝ (∫ f(Φ(σ, w)) d(Hᵐ⌞T)(w)) dσ = ∫_ℝ (∫_T f(Φ(σ, w)) dHᵐ(w)) dσ.
10. (Conclusion.) Steps 7 and 9 give ∫_{{z : π(z) ∈ T}} f dH^{m+1} = ∫_ℝ ∫_T f(Φ(σ, w)) dHᵐ(w) dσ. ∎

Formalization aid. The following tactic proof, placed after `theorem Submission.iwl_cr_ip_wt_plane_fubini : <the frozen Lean type of this child, verbatim> := by`, was kernel-checked in the contract scope (namespace GMT.Ch06 with the contract's opens) after import GMT.Ch06.Submission at the frozen commit d8d46c9 with the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c); #print axioms = [propext, Classical.choice, Quot.sound]. It uses no helper declarations and no sibling.

  intro P m hMP τ hτ f hfc hfcs
  -- Coordinates.
  let Φ : ℝ → Eucl P → Eucl (P + 1) := fun s u =>
    (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ u))
  let π : Eucl (P + 1) → Eucl P := fun y =>
    (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))
  have hΦc : Continuous fun p : ℝ × Eucl P => Φ p.1 p.2 :=
    (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm.continuous.comp
      (Continuous.finCons (A := fun _ : Fin (P + 1) => ℝ) continuous_fst
        ((EuclideanSpace.equiv (Fin P) ℝ).continuous.comp continuous_snd))
  -- `Φ′` is a homeomorphism `ℝ × ℝ^P ≃ ℝ^{P+1}`.
  let e : ℝ × Eucl P ≃ₜ Eucl (P + 1) :=
    { toFun := fun p => Φ p.1 p.2
      invFun := fun y => (EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0, π y)
      left_inv := fun p => by
        simp only [Φ, π, ContinuousLinearEquiv.apply_symm_apply, Fin.cons_zero, Fin.tail_cons,
          ContinuousLinearEquiv.symm_apply_apply]
      right_inv := fun y => by
        apply (EuclideanSpace.equiv (Fin (P + 1)) ℝ).injective
        simp only [Φ, π, ContinuousLinearEquiv.apply_symm_apply]
        exact Fin.cons_self_tail _
      continuous_toFun := hΦc
      continuous_invFun := by
        refine Continuous.prodMk ((continuous_apply 0).comp
          (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous) ?_
        exact (EuclideanSpace.equiv (Fin P) ℝ).symm.continuous.comp
          (continuous_pi fun i : Fin P => (continuous_apply i.succ).comp
            (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous) }
  have hemb : MeasurableEmbedding (fun p : ℝ × Eucl P => Φ p.1 p.2) := e.measurableEmbedding
  -- The plane `T = span τ` satisfies the hypotheses of (MP).
  set T : Submodule ℝ (Eucl P) := Submodule.span ℝ (range τ) with hT
  have hfinT : Module.finrank ℝ T = m := by
    rw [hT, finrank_span_eq_card hτ.linearIndependent, Fintype.card_fin]
  have hTmeas : MeasurableSet (T : Set (Eucl P)) := T.closed_of_finiteDimensional.measurableSet
  have hTrect : CountablyRectifiable m (T : Set (Eucl P)) := by
    let Λₗ : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] Eucl P :=
      Fintype.linearCombination ℝ τ ∘ₗ (EuclideanSpace.equiv (Fin m) ℝ).toLinearMap
    let Λ : EuclideanSpace ℝ (Fin m) →L[ℝ] Eucl P := LinearMap.toContinuousLinearMap Λₗ
    have hrange : range Λ = (T : Set (Eucl P)) := by
      ext v
      simp only [Λ, LinearMap.coe_toContinuousLinearMap', mem_range, SetLike.mem_coe, hT,
        Submodule.mem_span_range_iff_exists_fun]
      constructor
      · rintro ⟨u, rfl⟩
        exact ⟨fun i => u i, by simp [Λₗ, Fintype.linearCombination_apply]⟩
      · rintro ⟨c, rfl⟩
        exact ⟨(EuclideanSpace.equiv (Fin m) ℝ).symm c, by
          simp [Λₗ, Fintype.linearCombination_apply]⟩
    rw [← hrange]
    exact Poincare.SimonGMT.Chapter03.countablyRectifiable_range Λ.lipschitzWith
  have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule
    (E := Eucl P) hfinT
  have hTfin : ∀ K : Set (Eucl P), IsCompact K →
      (μHE[m] : Measure (Eucl P)) ((T : Set (Eucl P)) ∩ K) < ∞ := by
    intro K hK
    rw [inter_comm, ← Measure.restrict_apply hK.measurableSet]
    exact hK.measure_lt_top
  have hMPT : (μHE[m + 1] : Measure (Eucl (P + 1))).restrict {z | π z ∈ T} =
      Measure.map (fun p : ℝ × Eucl P => Φ p.1 p.2)
        ((volume : Measure ℝ).prod ((μHE[m] : Measure (Eucl P)).restrict (T : Set (Eucl P)))) :=
    hMP (T : Set (Eucl P)) hTmeas.nullMeasurableSet hTrect hTfin
  -- Change of variables along `Φ′` and Fubini.
  have hint : Integrable (fun p : ℝ × Eucl P => f (Φ p.1 p.2))
      ((volume : Measure ℝ).prod ((μHE[m] : Measure (Eucl P)).restrict (T : Set (Eucl P)))) :=
    (hfc.comp e.continuous).integrable_of_hasCompactSupport (hfcs.comp_homeomorph e)
  show ∫ z, f z ∂((μHE[m + 1] : Measure (Eucl (P + 1))).restrict {z | π z ∈ T}) = _
  rw [hMPT, hemb.integral_map, integral_prod _ hint]

## Key steps

1. Φ′ is a homeomorphism ℝ × ℝ^P ≃ ℝ^{P+1} (inverse y ↦ (y₀, π y)), hence a measurable embedding.
2. T = span τ is closed, has finrank m, is the range of the Lipschitz map u ↦ Σ u_i τ_i, and Hᵐ⌞T is regular; so (MP) applies to A = T.
3. MeasurableEmbedding.integral_map: ∫_{π⁻¹T} f dH^{m+1} = ∫ f∘Φ′ d(L¹ ⊗ Hᵐ⌞T).
4. f∘Φ′ is continuous with compact support, hence integrable for the locally finite product measure; integral_prod gives ∫_ℝ ∫_T f(Φ(σ,w)).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean; cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean; sha256sum (ea3ee0dd…853d)`
- `python3 -I: dag.json status/lean_name/lean_statement of root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1* and of root.flat_iff_weak-a1.tangent_locality-a1.blowup_change_of_variables-a1; its accepted-candidate.json contract.lean_statement == dag lean_statement and audit.comparator_passed`
- `git show 91a22d1bfc9063820dd1583526d3d097beffd0ec:GMT/Ch06/Submission.lean (accepted proof and declaration layout of Submission.fiw_tl_blowup_setIntegral)`
- `grep -rhoE "iwl_cr_ip_[A-Za-z0-9_']+" nodes dag.json (finds the sibling product_triple proposals iwl_cr_ip_pt_slab_restrict_eq_map, iwl_cr_ip_pt_slab_transfer, iwl_cr_ip_pt_cylinder_nullMeasurableSet, iwl_cr_ip_pt_cylinder_countablyRectifiable, iwl_cr_ip_pt_frame_orthonormal); grep -rhoE 'iwl_cr_ip_wt[A-Za-z0-9_]*' nodes dag.json (no match)`
- `python3 -I: nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a1/decomposition-v1.json (parent split, blowup_cov entry) and sibling decomposition-v1.json files (measure_identity, slice_formula: no split; product_triple: split with the names above)`
- `grep -n "theorem\|def\|abbrev" in simongmt Poincare/SimonGMT/Chapter03/Rectifiable.lean: CountablyRectifiable (l.34), countablyRectifiable_range (l.64), blowUpMap (l.96), regular_euclideanHausdorffMeasure_restrict_submodule (l.187), HasWeightedApproximateTangentSpaceAt (l.330)`
- `grep -rn in local-references mathlib/Mathlib: tendsto_integral_filter_of_dominated_convergence, continuous_of_dominated, intervalIntegral.integral_comp_mul_add, integral_Ioc_eq_integral_Ioo, intervalIntegral.integral_of_le, Integrable.comp_snd, MeasureTheory.AEStronglyMeasurable.comp_snd, aestronglyMeasurable_iUnion_iff, integrable_indicator_iff, integral_mono_of_nonneg, norm_integral_le_integral_norm, setIntegral_indicator, Continuous.integrable_of_hasCompactSupport, Measure.prod.instIsFiniteMeasureOnCompacts, integral_prod, MeasurableEmbedding.integral_map, HasCompactMulSupport.comp_homeomorph, Fintype.range_linearCombination, LinearMap.coe_toContinuousLinearMap', EuclideanSpace.real_norm_sq_eq, EuclideanSpace.equiv, abs_le_of_sq_le_sq, le_of_sq_le_sq, Filter.Tendsto.const_mul_atTop, Filter.Tendsto.const_mul_atTop_of_neg, tendsto_inv_nhdsGT_zero, Filter.Tendsto.eventually_lt_const, Continuous.bounded_above_of_compact_support, Continuous.finCons`
- `python3 -I /tmp/ptdec/scripts/gen.py and final.py (lean_contract.validate_lean_statement on all 7 child types; key/name regexes; dependency acyclicity)`
- `python3 -I /tmp/ptdec/scripts/layout.py (gmt-compare.py child_modules, contract mode) and lake env lean /tmp/ptdec/layout/AllChallenges.lean (7 exact comparator challenge targets)`
- `lake env lean /tmp/ptdec/Asm.lean (parent assembly from the 7 child stubs; sorryAx only from stubs)`
- `lake env lean /tmp/ptdec/C1.lean … C6.lean and /tmp/ptdec/Full.lean (complete child proofs + accepted blowup_cov proof + parent assembly + solution-side exact checks; #print axioms = [propext, Classical.choice, Quot.sound])`
- `independent reviewer subagent: re-ran Full.lean and AllChallenges.lean, compared payload statements byte-for-byte with the checked Lean files (scripts under /tmp/ptrev); verdict ACCEPT, minor wording fixes applied`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-b1e58acdf8/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-b1e58acdf8/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-b1e58acdf8/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-6184ff8144/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-930be90ff5/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-ef3d70356e/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-ef3d70356e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-tangent-locality-a1-blowup-change-of-variables-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Order/Field.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Filter/AtTopBot/Field.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Order/Ring/Abs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ptdec/scripts/gen.py`
- `/tmp/ptdec/scripts/layout.py`
- `/tmp/ptdec/scripts/full.py`
- `/tmp/ptdec/scripts/final.py`
- `/tmp/ptdec/Check.lean`
- `/tmp/ptdec/layout/AllChallenges.lean`
- `/tmp/ptdec/Asm.lean`
- `/tmp/ptdec/Full.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c. The snapshot's GMT/Ch06/Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean (sha256 ea3ee0dd…853d).

DAG and naming:
- No accepted declaration states any of the six new child statements, so nothing new is reused.
- The only reuse is fiw_tl_blowup_setIntegral: accepted, comparator_passed, with an identical frozen type.
- The sibling product_triple is concurrently proposing iwl_cr_ip_pt_* names (not accepted), two of which overlap product_measure and product_plane (a) mathematically. This node therefore uses the unreserved prefix iwl_cr_ip_wt_, with no match anywhere in the run directory.

SimonGMT Chapter03/Rectifiable.lean supplies blowUpMap, HasWeightedApproximateTangentSpaceAt (Simon Ch. 3, 1.7), countablyRectifiable_range and regular_euclideanHausdorffMeasure_restrict_submodule.

Mathlib supplies every tool used:
- dominated convergence along 𝓝[>] 0 and continuity of parametric integrals (tendsto_integral_filter_of_dominated_convergence, continuous_of_dominated);
- interval substitution (intervalIntegral.integral_comp_mul_add);
- Fubini (integral_prod, Integrable.comp_snd, AEStronglyMeasurable.comp_snd);
- change of variables along the homeomorphism Φ′ (MeasurableEmbedding.integral_map);
- integrability of compactly supported continuous functions (Continuous.integrable_of_hasCompactSupport, Measure.prod.instIsFiniteMeasureOnCompacts);
- the integral estimates integral_mono_of_nonneg and norm_integral_le_integral_norm.

Lean checks:
- All 7 child types elaborate in the exact comparator layout.
- All 6 new children are fully proved with axioms [propext, Classical.choice, Quot.sound].
- The frozen parent type is proved from them and the accepted blow-up lemma with the same axioms.
- An independent reviewer re-ran these checks and accepted the split.

Public sources for the mathematics: L. Simon, Introduction to Geometric Measure Theory, Ch. 3 §1 (Def. 1.7, weighted approximate tangent spaces) and Ch. 6, 3.2(2) (product with an interval); Federer, Geometric Measure Theory, 3.2.23 (product formula behind (MP)).
