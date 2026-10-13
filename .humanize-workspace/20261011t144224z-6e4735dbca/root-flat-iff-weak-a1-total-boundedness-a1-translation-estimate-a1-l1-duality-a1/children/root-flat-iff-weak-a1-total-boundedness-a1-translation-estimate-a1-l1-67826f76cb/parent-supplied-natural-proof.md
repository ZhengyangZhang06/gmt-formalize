# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1.l1_duality-a1`
- Child DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1.l1_duality-a1.compact_sign_approx-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the parent proof's steps 1, 2, 6 and 7 (Borel representative, the finite measure |w| dL, inner regularity, the pointwise inequality and integration). Two changes: ε/4 replaces ε, and the estimate is proved for every a.e.-strongly measurable g with |g| ≤ 1, g = 1 on K₁ and g = −1 on K₂, not only the parent's smooth g.

Notation. L := volume on ℝ^n = Eucl n, i.e. Lebesgue measure. Integrals are Bochner integrals with respect to L unless stated otherwise. The statement's parentheses matter: the conclusion is (∫ |w|) < (∫ w g) + ε, with ε added outside the integral.

1. Borel representative.
   (a) w is integrable, hence a.e.-strongly measurable. Let v := AEStronglyMeasurable.mk w. Then v is strongly measurable, hence Borel measurable, and w = v L-a.e. (AEStronglyMeasurable.ae_eq_mk).
   (b) v is integrable (Integrable.congr).
   (c) For every g : ℝ^n → ℝ, ∫ |w| = ∫ |v| and ∫ w g = ∫ v g (integral_congr_ae, since |w| = |v| and w g = v g L-a.e.).

2. The finite measure ν. Let ν := L.withDensity (x ↦ ENNReal.ofReal |v(x)|).
   (a) |v| is integrable, so ν is a finite measure (isFiniteMeasure_withDensity_ofReal).
   (b) For every measurable E, ν(E) = ∫⁻_E ofReal |v| dL (withDensity_apply).
   (c) Hence ∫_E |v| dL = (ν(E)).toReal (integral_eq_lintegral_of_nonneg_ae on L.restrict E, using |v| ≥ 0 and the a.e.-strong measurability of |v|).

3. Inner regularity. ℝ^n is a proper, second-countable metric space with its Borel σ-algebra, and ν is finite. So ν is inner regular with respect to compact sets on measurable sets of finite measure: the instance Measure.InnerRegularCompactLTTop ν is inferred. Therefore MeasurableSet.exists_isCompact_sdiff_lt applies: for every measurable A (ν(A) ≠ ∞ by finiteness, measure_ne_top) and every η ≠ 0 there is a compact K ⊆ A with ν(A \ K) < η.

4. Choice of K₁ and K₂.
   (a) A⁺ := {x | 0 < v(x)} and A⁻ := {x | v(x) < 0} are measurable (measurableSet_lt, v measurable).
   (b) ε > 0 gives η := ofReal(ε/4) ≠ 0. Step 3 yields compact K₁ ⊆ A⁺ and K₂ ⊆ A⁻ with ν(A⁺ \ K₁) < ofReal(ε/4) and ν(A⁻ \ K₂) < ofReal(ε/4).
   (c) K₁ and K₂ are disjoint: a common point x would satisfy 0 < v(x) < 0.
   These are the required compact sets.

5. The test function. Let g : ℝ^n → ℝ be a.e.-strongly measurable with |g(x)| ≤ 1 for all x, g = 1 on K₁ and g = −1 on K₂. Let S := (A⁺ \ K₁) ∪ (A⁻ \ K₂). S is measurable, because A^± are measurable and compact sets are closed, hence measurable.

6. Pointwise inequality. For every x, v(x)g(x) ≥ |v(x)| − 2·1_S(x)·|v(x)|.
   (a) x ∈ S. Then |v(x)g(x)| = |v(x)|·|g(x)| ≤ |v(x)|, so v(x)g(x) ≥ −|v(x)| = |v(x)| − 2|v(x)|.
   (b) x ∉ S and v(x) > 0. Then x ∈ A⁺ and x ∉ A⁺ \ K₁, so x ∈ K₁. Hence g(x) = 1 and v(x)g(x) = v(x) = |v(x)|.
   (c) x ∉ S and v(x) < 0. Likewise x ∈ K₂, g(x) = −1 and v(x)g(x) = −v(x) = |v(x)|.
   (d) x ∉ S and v(x) = 0. Both sides equal 0.

7. Integration.
   (a) v g is integrable, because v is integrable and g is a.e.-strongly measurable with ‖g‖ ≤ 1 (Integrable.mul_bdd).
   (b) 1_S |v| is integrable (Integrable.indicator).
   (c) Integrating step 6 (integral_mono, integral_sub, integral_const_mul, integral_indicator) gives ∫ |v| − 2 ∫_S |v| ≤ ∫ v g.

8. Smallness of the error.
   (a) By subadditivity (measure_union_le), ν(S) ≤ ν(A⁺ \ K₁) + ν(A⁻ \ K₂).
   (b) By step 4(b), ν(A⁺ \ K₁) + ν(A⁻ \ K₂) < ofReal(ε/4) + ofReal(ε/4) (ENNReal.add_lt_add).
   (c) ofReal(ε/4) + ofReal(ε/4) = ofReal(ε/2) (ENNReal.ofReal_add, ε/4 ≥ 0).
   (d) Hence ∫_S |v| = (ν(S)).toReal < ε/2 (step 2(c) and ENNReal.toReal_lt_of_lt_ofReal).

9. Conclusion. Steps 7 and 8 give ∫ |v| ≤ ∫ v g + 2 ∫_S |v| < ∫ v g + ε. By step 1(c), ∫ |w| = ∫ |v| < ∫ v g + ε = ∫ w g + ε, i.e. (∫ x, |w x|) < (∫ x, w x * g x) + ε. ∎

Appendix (Lean reference proof; it is not part of the numbered argument). The declaration below follows steps 1–9 line by line. During decomposition it compiled with Lean v4.35.0-rc3 and Mathlib 25730c7c. It was placed after `import GMT.Ch06.Submission`, inside `namespace GMT.Ch06`, under the contract's `open MeasureTheory Filter Set Metric` and `open scoped ENNReal NNReal Topology`. `#print axioms` reported only propext, Classical.choice and Quot.sound, and it uses no `sorry`. It may be used verbatim.

```lean
theorem Submission.fiw_tb_te_l1d_compact_sign_approx : ∀ (n : ℕ) (w : Eucl n → ℝ), Integrable w → ∀ ε : ℝ, 0 < ε → ∃ K₁ K₂ : Set (Eucl n), IsCompact K₁ ∧ IsCompact K₂ ∧ Disjoint K₁ K₂ ∧ ∀ g : Eucl n → ℝ, AEStronglyMeasurable g → (∀ x, |g x| ≤ 1) → (∀ x ∈ K₁, g x = 1) → (∀ x ∈ K₂, g x = -1) → (∫ x, |w x|) < (∫ x, w x * g x) + ε := by
  intro n w hw ε hε
  -- Steps 1–3: a Borel representative `v` of `w` and the finite measure `ν = |v| dL`.
  set v : Eucl n → ℝ := hw.aestronglyMeasurable.mk w with hv_def
  have hv_meas : StronglyMeasurable v := hw.aestronglyMeasurable.stronglyMeasurable_mk
  have hwv : w =ᵐ[volume] v := hw.aestronglyMeasurable.ae_eq_mk
  have hvi : Integrable v := hw.congr hwv
  set ν : Measure (Eucl n) := volume.withDensity (fun x => ENNReal.ofReal |v x|) with hν
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hvi.abs.hasFiniteIntegral
  -- Step 4: inner approximation of `{v > 0}` and `{v < 0}` by compact sets.
  set Ap : Set (Eucl n) := {x | 0 < v x} with hAp_def
  set Am : Set (Eucl n) := {x | v x < 0} with hAm_def
  have hAp : MeasurableSet Ap := measurableSet_lt measurable_const hv_meas.measurable
  have hAm : MeasurableSet Am := measurableSet_lt hv_meas.measurable measurable_const
  have hε4 : ENNReal.ofReal (ε / 4) ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  obtain ⟨Kp, hKpA, hKp, hKpν⟩ := hAp.exists_isCompact_sdiff_lt (measure_ne_top ν Ap) hε4
  obtain ⟨Km, hKmA, hKm, hKmν⟩ := hAm.exists_isCompact_sdiff_lt (measure_ne_top ν Am) hε4
  have hdisj : Disjoint Kp Km := by
    rw [Set.disjoint_left]
    intro x hp hm
    have h1 : 0 < v x := hKpA hp
    have h2 : v x < 0 := hKmA hm
    linarith
  refine ⟨Kp, Km, hKp, hKm, hdisj, ?_⟩
  intro g hg hg1 hgp hgm
  -- Steps 5–6: the pointwise inequality `|v| - 2·1_S|v| ≤ v g`.
  set S : Set (Eucl n) := (Ap \ Kp) ∪ (Am \ Km) with hS_def
  have hS : MeasurableSet S := (hAp.diff hKp.measurableSet).union (hAm.diff hKm.measurableSet)
  have hpt : ∀ x, |v x| - 2 * S.indicator (fun y => |v y|) x ≤ v x * g x := by
    intro x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      have h : |v x * g x| ≤ |v x| := by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hg1 x)
      linarith [(abs_le.mp h).1]
    · rw [indicator_of_notMem hx]
      have hx' : (0 < v x → x ∈ Kp) ∧ (v x < 0 → x ∈ Km) := by
        constructor
        · intro h
          by_contra hK
          exact hx (Or.inl ⟨h, hK⟩)
        · intro h
          by_contra hK
          exact hx (Or.inr ⟨h, hK⟩)
      rcases lt_trichotomy (v x) 0 with h | h | h
      · rw [hgm x (hx'.2 h), abs_of_neg h]
        linarith
      · rw [h]
        simp
      · rw [hgp x (hx'.1 h), abs_of_pos h]
        linarith
  -- Step 7: integrate.
  have hvg : Integrable (fun x => v x * g x) :=
    hvi.mul_bdd hg (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hg1 x)
  have hind : Integrable (fun x => S.indicator (fun y => |v y|) x) := hvi.abs.indicator hS
  have hlhs : Integrable (fun x => |v x| - 2 * S.indicator (fun y => |v y|) x) :=
    hvi.abs.sub (hind.const_mul 2)
  have hmono := integral_mono hlhs hvg hpt
  rw [integral_sub hvi.abs (hind.const_mul 2), integral_const_mul, integral_indicator hS] at hmono
  -- Step 8: `∫_S |v| = (ν S).toReal < ε / 2`.
  have hνS : ν S = ∫⁻ x in S, ENNReal.ofReal |v x| := withDensity_apply _ hS
  have hSint : ∫ x in S, |v x| = (ν S).toReal := by
    rw [hνS, integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => abs_nonneg _)
      hvi.abs.aestronglyMeasurable.restrict]
  have hνS_lt : ν S < ENNReal.ofReal (ε / 2) := by
    calc ν S ≤ ν (Ap \ Kp) + ν (Am \ Km) := measure_union_le _ _
      _ < ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) := ENNReal.add_lt_add hKpν hKmν
      _ = ENNReal.ofReal (ε / 2) := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
        ring_nf
  have hSlt : ∫ x in S, |v x| < ε / 2 := by
    rw [hSint]
    exact ENNReal.toReal_lt_of_lt_ofReal hνS_lt
  -- Step 9: transfer back from `v` to `w`.
  have h1 : ∫ x, |w x| = ∫ x, |v x| := integral_congr_ae (hwv.fun_comp abs)
  have h2 : ∫ x, w x * g x = ∫ x, v x * g x :=
    integral_congr_ae (hwv.mono fun x hx => by simp only [hx])
  rw [h1, h2]
  linarith
```

## Key steps

1. Replace w by a Borel representative v = w a.e. The measure ν = |v| dL is finite and inner regular for compact sets, and ∫_E |v| = ν(E).toReal.
2. Choose compact K₁ ⊆ {v > 0} and K₂ ⊆ {v < 0} with ν({v > 0} \ K₁) and ν({v < 0} \ K₂) both < ε/4. K₁ and K₂ are disjoint.
3. For any a.e.-strongly measurable g with |g| ≤ 1, g = 1 on K₁ and g = −1 on K₂: v g ≥ |v| − 2·1_S|v| pointwise, where S is the union of the two error sets.
4. Integrating gives ∫ |v| ≤ ∫ v g + 2ν(S) < ∫ v g + ε. Transfer back from v to w.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (local-project; project d8d46c95, mathlib 25730c7c)`
- `grep -rn 'theorem exists_contDiff_support_eq_eq_one_iff' Mathlib; sed -n 770,792p Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `grep -rn -B2 -A6 'exists_thickenings' Mathlib/Topology/MetricSpace/Thickening.lean; grep -n -A3 '^def thickening' and '^def cthickening' Mathlib/Topology/MetricSpace/Thickening.lean`
- `grep -n 'exists_isCompact_sdiff_lt' / 'exists_isCompact_diff_lt' / 'exists_isCompact_lt_add' Mathlib/MeasureTheory/Measure/Regular.lean; sed -n 815,856p`
- `grep -rn 'theorem isFiniteMeasure_withDensity_ofReal' / 'theorem ofReal_integral_eq_lintegral_ofReal' / 'theorem closure_thickening_subset_cthickening' / 'IsCompact.cthickening' Mathlib`
- `grep -rn 'theorem Integrable.bdd_mul' / 'theorem Integrable.mul_bdd' / 'theorem integral_indicator' / 'theorem toReal_lt_of_lt_ofReal' / 'theorem withDensity_apply' Mathlib`
- `python3 scan of dag.json lean_statement fields containing HasCompactSupport with Integrable/IsCompact, or thickening (looking for reusable accepted lemmas)`
- `rg -n 'fiw_tb_te_l1d|smooth_sign_sep|compact_sign_approx' over project, mathlib/Mathlib, simongmt, GMT (0 matches); dag.json lean_name scan (458 nodes, 0 matches); git grep 'fiw_tb_te_l1d' over 1616 refs (0 matches)`
- `python3 -I gen.py / e2e.py (verifier gmt-compare.py child_modules in contract mode + lean_contract.validate_lean_statement), then lake env lean on Challenge_*.lean, SolutionSim.lean, E2E.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/HasFiniteIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/l1d-decomp-9f3a/SolutionSim.lean`
- `/tmp/l1d-decomp-9f3a/e2e/E2E.lean`
- `/tmp/l1d-decomp-9f3a/e2e/Challenge_smooth_sign_sep.lean`
- `/tmp/l1d-decomp-9f3a/e2e/Challenge_compact_sign_approx.lean`

The snapshot is project d8d46c95 with Mathlib 25730c7c. The pinned Mathlib supplies every lemma the child proofs use:
- exists_contDiff_support_eq_eq_one_iff (implicit {n : ℕ∞}; PartitionOfUnity.lean:789);
- Disjoint.exists_thickenings (compact/closed), isOpen_thickening, self_subset_thickening, closure_thickening_subset_cthickening, IsCompact.cthickening (ProperSpace);
- MeasurableSet.exists_isCompact_sdiff_lt (Regular.lean:843; exists_isCompact_diff_lt is only a deprecated alias);
- isFiniteMeasure_withDensity_ofReal, withDensity_apply, integral_eq_lintegral_of_nonneg_ae, Integrable.mul_bdd, integral_indicator, ENNReal.toReal_lt_of_lt_ofReal.
InnerRegularCompactLTTop is inferred for the finite withDensity measure on Eucl n. thickening and cthickening are defined through infEDist.

No existing DAG or project lemma gives the needed inequality. The accepted slicing_ru_continuous_to_bounded and polyhedral_approx_integrable_smooth_ext are equality extensions. rpn_null_compact_cutoff and fiw_tb_ext_cutoff are one-sided [0, 1] cutoffs. So both children are new.

The names fiw_tb_te_l1d_smooth_sign_sep and fiw_tb_te_l1d_compact_sign_approx are globally fresh: no match in the DAG, project, Mathlib, SimonGMT or any of 1616 git refs.

Both child types and the parent's frozen type elaborate in the comparator's exact contract scope. The full child proofs (embedded) and the parent proved from them compile, and the comparator-style targets pass with axioms propext, Classical.choice and Quot.sound only.
