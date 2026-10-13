# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1.l1_duality-a1`
- Child DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1.l1_duality-a1.smooth_sign_sep-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the parent proof's steps 3–5 (disjoint δ-thickenings and smooth Urysohn functions), stated for arbitrary disjoint compact sets K₁, K₂ in place of K⁺, K⁻.

Notation. ℝ^n = Eucl n = EuclideanSpace ℝ (Fin n). For δ ∈ ℝ and A ⊆ ℝ^n, thickening(δ, A) = Metric.thickening δ A is the open δ-neighbourhood {x | infEDist x A < ENNReal.ofReal δ}, and cthickening(δ, A) = Metric.cthickening δ A is the closed one {x | infEDist x A ≤ ENNReal.ofReal δ}.

1. Separation. K₁ and K₂ are compact, hence closed in the Hausdorff space ℝ^n (IsCompact.isClosed), and they are disjoint. Disjoint.exists_thickenings needs K₁ compact and K₂ closed, and gives δ > 0 with thickening(δ, K₁) and thickening(δ, K₂) disjoint. For i = 1, 2 put V_i := thickening(δ, K_i).

2. Properties of V_i, for i = 1, 2:
   (a) V_i is open (isOpen_thickening);
   (b) K_i ⊆ V_i, because δ > 0 (self_subset_thickening);
   (c) closure V_i ⊆ cthickening(δ, K_i) (closure_thickening_subset_cthickening);
   (d) cthickening(δ, K_i) is compact, because K_i is compact and ℝ^n is a proper metric space (IsCompact.cthickening).

3. Smooth Urysohn functions. ℝ^n is a finite-dimensional real normed space. For i = 1, 2 apply exists_contDiff_support_eq_eq_one_iff to the open set V_i and the closed set K_i ⊆ V_i (steps 1 and 2(a), 2(b)). Set the lemma's own implicit smoothness parameter, of type ℕ∞ and unrelated to the dimension n, to ⊤, so that its conclusion reads ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞). The lemma gives a C^∞ function g_i : ℝ^n → ℝ with:
   - range g_i ⊆ [0, 1];
   - support g_i = V_i;
   - x ∈ K_i ↔ g_i(x) = 1, for every x.
   In particular 0 ≤ g_i(x) ≤ 1 for every x, and g_i(x) = 1 for x ∈ K_i.

4. Compact supports. tsupport g_i = closure(support g_i) = closure V_i ⊆ cthickening(δ, K_i) by step 2(c). tsupport g_i is closed and lies inside the compact set of step 2(d), so it is compact (IsCompact.of_isClosed_subset). That is, g_i has compact support.

5. Disjoint supports. For every x, g₁(x) = 0 or g₂(x) = 0. Otherwise x ∈ support g₁ ∩ support g₂ = V₁ ∩ V₂, which is empty by step 1.

6. The function. Let g := g₁ − g₂. It is C^∞ (ContDiff.sub) and has compact support (HasCompactSupport.sub with step 4).

7. Bound |g| ≤ 1. Fix x. If g₁(x) = 0, then g(x) = −g₂(x) ∈ [−1, 0]. If g₂(x) = 0, then g(x) = g₁(x) ∈ [0, 1]. By step 5 one of the two cases holds, so −1 ≤ g(x) ≤ 1, i.e. |g(x)| ≤ 1.

8. Values on K₁ and K₂.
   (a) If x ∈ K₁, then g₁(x) = 1 ≠ 0 by step 3, so g₂(x) = 0 by step 5, and g(x) = 1 − 0 = 1.
   (b) If x ∈ K₂, then g₂(x) = 1 ≠ 0, so g₁(x) = 0, and g(x) = 0 − 1 = −1.

9. Conclusion. g is C^∞, has compact support, satisfies |g(x)| ≤ 1 for all x, equals 1 on K₁ and equals −1 on K₂. This is the claim. ∎

Appendix (Lean reference proof; it is not part of the numbered argument). The declaration below follows steps 1–9 line by line. During decomposition it compiled with Lean v4.35.0-rc3 and Mathlib 25730c7c. It was placed after `import GMT.Ch06.Submission`, inside `namespace GMT.Ch06`, under the contract's `open MeasureTheory Filter Set Metric` and `open scoped ENNReal NNReal Topology`. `#print axioms` reported only propext, Classical.choice and Quot.sound, and it uses no `sorry`. It may be used verbatim.

```lean
theorem Submission.fiw_tb_te_l1d_smooth_sign_sep : ∀ (n : ℕ) (K₁ K₂ : Set (Eucl n)), IsCompact K₁ → IsCompact K₂ → Disjoint K₁ K₂ → ∃ g : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ HasCompactSupport g ∧ (∀ x, |g x| ≤ 1) ∧ (∀ x ∈ K₁, g x = 1) ∧ (∀ x ∈ K₂, g x = -1) := by
  intro n K₁ K₂ hK₁ hK₂ hd
  -- Steps 1–2: disjoint δ-thickenings `V₁ ⊇ K₁`, `V₂ ⊇ K₂`.
  obtain ⟨δ, hδ, hdδ⟩ := hd.exists_thickenings hK₁ hK₂.isClosed
  -- Step 3: smooth Urysohn functions `g₁, g₂ : ℝ^n → [0, 1]` with `support gᵢ = Vᵢ`, `gᵢ = 1` on `Kᵢ`.
  obtain ⟨g₁, hg₁, hr₁, hs₁, he₁⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (isOpen_thickening (δ := δ) (E := K₁)) hK₁.isClosed (self_subset_thickening hδ K₁)
  obtain ⟨g₂, hg₂, hr₂, hs₂, he₂⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (isOpen_thickening (δ := δ) (E := K₂)) hK₂.isClosed (self_subset_thickening hδ K₂)
  -- Step 4: `tsupport gᵢ = closure Vᵢ ⊆ cthickening δ Kᵢ`, which is compact.
  have hc : ∀ (K : Set (Eucl n)) (f : Eucl n → ℝ), IsCompact K →
      Function.support f = thickening δ K → HasCompactSupport f := by
    intro K f hK hs
    refine (hK.cthickening (r := δ)).of_isClosed_subset (isClosed_tsupport f) ?_
    rw [tsupport, hs]
    exact closure_thickening_subset_cthickening δ K
  have h01₁ : ∀ x, 0 ≤ g₁ x ∧ g₁ x ≤ 1 := fun x => hr₁ (mem_range_self x)
  have h01₂ : ∀ x, 0 ≤ g₂ x ∧ g₂ x ≤ 1 := fun x => hr₂ (mem_range_self x)
  -- Step 5: at every point one of `g₁, g₂` vanishes, since `V₁ ∩ V₂ = ∅`.
  have hdis : ∀ x, g₁ x = 0 ∨ g₂ x = 0 := by
    intro x
    by_contra h
    rw [not_or] at h
    have h1 : x ∈ Function.support g₁ := h.1
    have h2 : x ∈ Function.support g₂ := h.2
    rw [hs₁] at h1
    rw [hs₂] at h2
    exact Set.disjoint_left.mp hdδ h1 h2
  -- Steps 6–8: `g = g₁ - g₂`.
  refine ⟨g₁ - g₂, hg₁.sub hg₂, (hc K₁ g₁ hK₁ hs₁).sub (hc K₂ g₂ hK₂ hs₂), ?_, ?_, ?_⟩
  · intro x
    have a := h01₁ x
    have b := h01₂ x
    rw [Pi.sub_apply, abs_le]
    rcases hdis x with h | h <;> constructor <;> linarith
  · intro x hx
    have h1 : g₁ x = 1 := (he₁ x).1 hx
    have h2 : g₂ x = 0 := by
      rcases hdis x with h | h
      · rw [h1] at h; norm_num at h
      · exact h
    simp [h1, h2]
  · intro x hx
    have h2 : g₂ x = 1 := (he₂ x).1 hx
    have h1 : g₁ x = 0 := by
      rcases hdis x with h | h
      · exact h
      · rw [h2] at h; norm_num at h
    simp [h1, h2]
```

## Key steps

1. K₁ and K₂ are compact, hence closed. Disjoint.exists_thickenings gives δ > 0 such that the open δ-thickenings V_i ⊇ K_i are disjoint. Each V_i is open and its closure lies in the compact set cthickening(δ, K_i).
2. exists_contDiff_support_eq_eq_one_iff, with smoothness ⊤, gives C^∞ functions g_i : ℝ^n → [0, 1] with support g_i = V_i and g_i = 1 exactly on K_i. Each has compact support, since tsupport g_i = closure V_i.
3. At every point one of g₁ and g₂ vanishes, because V₁ ∩ V₂ = ∅.
4. g := g₁ − g₂ is C^∞ with compact support, satisfies |g| ≤ 1, and takes the values 1 on K₁ and −1 on K₂.

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
