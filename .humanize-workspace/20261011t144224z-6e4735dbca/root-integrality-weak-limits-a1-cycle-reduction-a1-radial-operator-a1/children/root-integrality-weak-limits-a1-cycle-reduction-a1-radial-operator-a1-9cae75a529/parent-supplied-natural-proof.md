# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_operator-a1`
- Child DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_operator-a1.integrand_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 7 of the parent proof (bound (iii)), stated for the integrand at a fixed t ∈ [0,1] and filled in. A Lean rendering of exactly this argument was compiled against the pinned snapshot, using only the standard axioms.

Conventions. E := Eucl P, Λ_l := Covector E l, D^i := iteratedFDeriv ℝ i, and ‖·‖ is the operator norm.

0. Fix j, R and D ≥ 0 with ‖D^iω(y)‖ ≤ D for all i ≤ j and all y with ‖y‖ ≤ R. Fix t ∈ [0,1] and x with ‖x‖ ≤ R. Then R ≥ 0, since ‖x‖ ≥ 0.

1. (Interior product.) Let 𝔅 := (ContinuousAlternatingMap.curryLeftLI).toContinuousLinearMap : Λ_{k+1} →L[ℝ] (E →L[ℝ] Λ_k). Then 𝔅(α) = α.curryLeft, and ‖𝔅‖ ≤ 1 because the continuous linear map underlying a linear isometry has norm at most 1 (LinearIsometry.norm_toContinuousLinearMap_le). So the function in the statement is f_t(z) = t^a • 𝔅(g_t(z))(id z), where g_t(z) := ω(t • z).

2. (Derivatives of g_t.) Let L := t • id_E ∈ E →L[ℝ] E. Then ‖L‖ = |t|·‖id_E‖ ≤ 1·1 = 1 (norm_smul, ContinuousLinearMap.norm_id_le, 0 ≤ t ≤ 1). So g_t = ω ∘ L is C^∞. For i ≤ j:
 - ContinuousLinearMap.iteratedFDeriv_comp_right gives D^ig_t(x) = (D^iω(Lx)).compContinuousLinearMap (fun _ => L);
 - so ‖D^ig_t(x)‖ ≤ ‖D^iω(Lx)‖·∏_{Fin i}‖L‖ ≤ ‖D^iω(Lx)‖ (ContinuousMultilinearMap.norm_compContinuousLinearMap_le and Finset.prod_le_one₀);
 - since ‖Lx‖ ≤ ‖L‖‖x‖ ≤ R, we have Lx ∈ closedBall 0 R, and the hypothesis gives ‖D^ig_t(x)‖ ≤ D.

3. (Removing the scalar t^a.) H(z) := 𝔅(g_t(z))(id z) is C^∞, since a bounded bilinear map composed with C^∞ maps is C^∞ (B.isBoundedBilinearMap.contDiff.comp (hg.prodMk contDiff_id)). Hence D^jf_t(x) = t^a • D^jH(x) (iteratedFDeriv_const_smul_apply'), so ‖D^jf_t(x)‖ = |t^a|·‖D^jH(x)‖ with 0 ≤ t^a ≤ 1 (pow_le_one₀).

4. (Leibniz bound.) Apply ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one with the bilinear map 𝔅 (norm ≤ 1), f = g_t and g = id, both C^∞:
 ‖D^jH(x)‖ ≤ Σ_{i=0}^{j} C(j,i)·‖D^ig_t(x)‖·‖D^{j−i}id(x)‖.

5. (Derivatives of the identity.)
 - ‖D^0 id(x)‖ = ‖x‖ ≤ R (norm_iteratedFDeriv_zero).
 - ‖D^1 id(x)‖ = ‖fderiv ℝ id x‖ = ‖id_E‖ ≤ 1 (norm_iteratedFDeriv_one, fderiv_id, ContinuousLinearMap.norm_id_le).
 - D^l id(x) = 0 for l ≥ 2. Write l = n + 1 with n ≥ 1. By iteratedFDeriv_succ_eq_comp_right, D^{n+1}id(x) = Ψ(D^n(y ↦ fderiv ℝ id y)(x)) for the linear isometry Ψ := (continuousMultilinearCurryRightEquiv' ℝ n E E).symm. The map y ↦ fderiv ℝ id y is the constant y ↦ id_E (fderiv_id), so its n-th iterated derivative vanishes because n ≠ 0 (iteratedFDeriv_const_of_ne). Finally Ψ(0) = 0.

6. (Evaluating the sum.)
 - If j = 0, the sum has the single term C(0,0)·‖D^0g_t(x)‖·‖D^0id(x)‖ = ‖ω(t•x)‖·‖x‖ ≤ D·R = (R + 0)·D.
 - If j = m + 1, split off the last two terms (Finset.sum_range_succ twice):
 · for i < m, j − i ≥ 2, so these terms vanish by Step 5;
 · the term i = m is C(m+1,m)·‖D^mg_t(x)‖·‖D^1id(x)‖ ≤ (m+1)·D·1 (Nat.choose_succ_self_right, Step 2 with m ≤ j, and Step 5);
 · the term i = m+1 is C(m+1,m+1)·‖D^{m+1}g_t(x)‖·‖D^0id(x)‖ ≤ 1·D·R.
 Hence the sum is at most (m+1)·D + D·R = (R + j)·D.

7. (Conclusion.) By Steps 3, 4 and 6, ‖D^jf_t(x)‖ ≤ |t^a|·(R + j)·D ≤ 1·(R + j)·D = (R + j)·D, using (R + j)·D ≥ 0. ∎

Implementation notes (all checked in a scratch build against the snapshot):
- Add `import Mathlib.Analysis.Calculus.ContDiff.Bounds` to Submission.lean, and put `set_option maxSynthPendingDepth 3 in` before the theorem.
- Introduce 𝔅 opaquely: `obtain ⟨B, hB, hBnorm⟩ : ∃ B : Covector (Eucl P) (k + 1) →L[ℝ] (Eucl P →L[ℝ] Covector (Eucl P) k), (∀ α, B α = α.curryLeft) ∧ ‖B‖ ≤ 1 := ⟨(ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Eucl P) (F := ℝ) (n := k)).toContinuousLinearMap, fun α => rfl, LinearIsometry.norm_toContinuousLinearMap_le _⟩`. Then rewrite the function to `fun z => t ^ a • B (ω (t • z)) (id z)` with `funext z; rw [hB]; rfl`.
- The vanishing of D^l id is a six-line auxiliary lemma, `Submission.iwl_cr_ro_ib_iteratedFDeriv_id_eq_zero`.
- Use `Finset.prod_le_one₀`; the unprimed `Finset.prod_le_one` is the ordered-monoid version.
- In the case j = 0, a `simp only` with `Finset.range_one`, `Finset.sum_singleton`, `Nat.choose_self`, `Nat.sub_zero` and `norm_iteratedFDeriv_zero` reduces the sum.
- In the case j = m+1, use `rw [hzero, zero_add, Nat.sub_self, Nat.choose_self, Nat.choose_succ_self_right, show m + 1 - m = 1 by omega, norm_iteratedFDeriv_zero, norm_iteratedFDeriv_one]`, then `push_cast`, then `nlinarith` from the two term bounds.

Appendix — verified Lean rendering of the proof above. It was compiled against the pinned snapshot in the Submission.lean layout, i.e. inside `namespace GMT.Ch06` after the contract's section, with the contract's `open`s. A comparator-style check `theorem … : (frozen type) := by exact Submission.<name>`, run in the replayed contract scope, also passes. `#print axioms` reports only propext, Classical.choice and Quot.sound. Required import: `import Mathlib.Analysis.Calculus.ContDiff.Bounds`.

```lean
theorem Submission.iwl_cr_ro_ib_iteratedFDeriv_id_eq_zero (P : ℕ) (l : ℕ) (hl : 2 ≤ l)
    (x : Eucl P) : iteratedFDeriv ℝ l (id : Eucl P → Eucl P) x = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, l = n + 1 := ⟨l - 1, by omega⟩
  rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
  have hconst : (fun y : Eucl P => fderiv ℝ (id : Eucl P → Eucl P) y) =
      fun _ => ContinuousLinearMap.id ℝ (Eucl P) := by
    funext y; exact fderiv_id
  rw [hconst, iteratedFDeriv_const_of_ne (by omega)]
  simp

set_option maxSynthPendingDepth 3 in
theorem Submission.iwl_cr_ro_integrand_iteratedFDeriv_le :
    (∀ (P k a : ℕ) (ω : DifferentialForm (Eucl P) (k + 1)), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω → ∀ (j : ℕ) (R D : ℝ), 0 ≤ D → (∀ i ≤ j, ∀ y ∈ closedBall (0 : Eucl P) R, ‖iteratedFDeriv ℝ i ω y‖ ≤ D) → ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall (0 : Eucl P) R, ‖iteratedFDeriv ℝ j (fun z : Eucl P => t ^ a • (ω (t • z)).curryLeft z) x‖ ≤ (R + j) * D) := by
  intro P k a ω hω j R D hD hbound t ht x hx
  obtain ⟨B, hB, hBnorm⟩ : ∃ B : Covector (Eucl P) (k + 1) →L[ℝ] (Eucl P →L[ℝ] Covector (Eucl P) k),
      (∀ α, B α = α.curryLeft) ∧ ‖B‖ ≤ 1 :=
    ⟨(ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Eucl P) (F := ℝ) (n := k)).toContinuousLinearMap,
      fun α => rfl, LinearIsometry.norm_toContinuousLinearMap_le _⟩
  have hx' : ‖x‖ ≤ R := by simpa using hx
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have hfun : (fun z : Eucl P => t ^ a • (ω (t • z)).curryLeft z) =
      fun z => t ^ a • B (ω (t • z)) (id z) := by
    funext z; rw [hB]; rfl
  rw [hfun]
  set L : Eucl P →L[ℝ] Eucl P := t • ContinuousLinearMap.id ℝ (Eucl P) with hL
  have hLnorm : ‖L‖ ≤ 1 := by
    rw [hL, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    calc t * ‖ContinuousLinearMap.id ℝ (Eucl P)‖ ≤ 1 * 1 :=
          mul_le_mul ht1 ContinuousLinearMap.norm_id_le (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hgfun : (fun z : Eucl P => ω (t • z)) = ω ∘ L := by
    funext z; simp [hL]
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Eucl P => ω (t • z)) := by
    rw [hgfun]; exact hω.comp L.contDiff
  have hgnorm : ∀ i ≤ j, ‖iteratedFDeriv ℝ i (fun z : Eucl P => ω (t • z)) x‖ ≤ D := by
    intro i hi
    rw [hgfun, L.iteratedFDeriv_comp_right hω x (by exact_mod_cast le_top)]
    have hLx : L x ∈ closedBall (0 : Eucl P) R := by
      rw [mem_closedBall, dist_zero_right]
      calc ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
        _ ≤ 1 * R := mul_le_mul hLnorm hx' (norm_nonneg x) zero_le_one
        _ = R := one_mul R
    calc ‖(iteratedFDeriv ℝ i ω (L x)).compContinuousLinearMap fun _ => L‖
        ≤ ‖iteratedFDeriv ℝ i ω (L x)‖ * ∏ _ : Fin i, ‖L‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ D * 1 := by
          apply mul_le_mul (hbound i hi _ hLx) _ (Finset.prod_nonneg fun _ _ => norm_nonneg _) hD
          exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hLnorm)
      _ = D := mul_one D
  have hH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Eucl P => B (ω (t • z)) (id z)) :=
    B.isBoundedBilinearMap.contDiff.comp (hg.prodMk contDiff_id)
  have hsmul : iteratedFDeriv ℝ j (fun z : Eucl P => t ^ a • B (ω (t • z)) (id z)) x =
      t ^ a • iteratedFDeriv ℝ j (fun z : Eucl P => B (ω (t • z)) (id z)) x :=
    iteratedFDeriv_const_smul_apply' (hH.contDiffAt.of_le (by exact_mod_cast le_top))
  rw [hsmul, norm_smul]
  have hta : ‖t ^ a‖ ≤ 1 := by
    rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg ht0]
    exact pow_le_one₀ ht0 ht1
  have key := B.norm_iteratedFDeriv_le_of_bilinear_of_le_one hg contDiff_id x
    (n := j) (by exact_mod_cast le_top) hBnorm
  have hsum : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i (fun z : Eucl P => ω (t • z)) x‖ *
      ‖iteratedFDeriv ℝ (j - i) (id : Eucl P → Eucl P) x‖ ≤ (R + j) * D := by
    rcases j with _ | m
    · simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.choose_self, Nat.cast_one,
        one_mul, Nat.sub_zero, norm_iteratedFDeriv_zero, id_eq, CharP.cast_eq_zero, add_zero]
      calc ‖ω (t • x)‖ * ‖x‖ ≤ D * R := by
            apply mul_le_mul _ hx' (norm_nonneg _) hD
            have := hgnorm 0 le_rfl
            simpa using this
        _ = R * D := mul_comm D R
    · rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hzero : ∑ i ∈ Finset.range m, ((m + 1).choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun z : Eucl P => ω (t • z)) x‖ *
          ‖iteratedFDeriv ℝ (m + 1 - i) (id : Eucl P → Eucl P) x‖ = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [Finset.mem_range] at hi
        rw [Submission.iwl_cr_ro_ib_iteratedFDeriv_id_eq_zero P (m + 1 - i) (by omega) x,
          norm_zero, mul_zero]
      rw [hzero, zero_add, Nat.sub_self, Nat.choose_self, Nat.choose_succ_self_right,
        show m + 1 - m = 1 by omega, norm_iteratedFDeriv_zero, norm_iteratedFDeriv_one]
      have h1 : ‖fderiv ℝ (id : Eucl P → Eucl P) x‖ ≤ 1 := by
        rw [fderiv_id]; exact ContinuousLinearMap.norm_id_le
      have hm := hgnorm m (by omega)
      have hm1 := hgnorm (m + 1) le_rfl
      push_cast
      have e1 : ((m : ℝ) + 1) * ‖iteratedFDeriv ℝ m (fun z : Eucl P => ω (t • z)) x‖ *
          ‖fderiv ℝ (id : Eucl P → Eucl P) x‖ ≤ ((m : ℝ) + 1) * D * 1 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hm (by positivity)) h1 (norm_nonneg _)
          (by positivity)
      have e2 : 1 * ‖iteratedFDeriv ℝ (m + 1) (fun z : Eucl P => ω (t • z)) x‖ * ‖id x‖ ≤
          1 * D * R := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hm1 zero_le_one) hx' (norm_nonneg _)
          (by positivity)
      nlinarith
  calc ‖t ^ a‖ * ‖iteratedFDeriv ℝ j (fun z : Eucl P => B (ω (t • z)) (id z)) x‖
      ≤ 1 * ((R + j) * D) := by
        apply mul_le_mul hta (key.trans hsum) (norm_nonneg _) zero_le_one
    _ = (R + j) * D := one_mul _
```

## Key steps

1. Write the integrand as t^a • 𝔅(ω(t•z))(id z), with ‖𝔅‖ ≤ 1 (curryLeftLI) and 0 ≤ t^a ≤ 1.
2. For i ≤ j, ‖D^i(ω∘(t•id))(x)‖ ≤ ∏‖t•id‖·‖D^iω(tx)‖ ≤ D, via iteratedFDeriv_comp_right and ‖tx‖ ≤ R.
3. Leibniz bound for a bounded bilinear map of norm ≤ 1: ‖D^jH(x)‖ ≤ Σ C(j,i)‖D^ig_t(x)‖‖D^{j−i}id(x)‖.
4. ‖D^0id(x)‖ = ‖x‖ ≤ R, ‖D^1id‖ ≤ 1 and D^l id = 0 for l ≥ 2. Only i = j and i = j−1 contribute, giving ≤ RD + jD = (R+j)D.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (project_commit d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean; sha256sum GMT/Ch06/Contract.lean`
- `rg -n "(theorem|lemma|def|abbrev) [A-Za-z_.']*<name>\b" mathlib/Mathlib for <name> in hasFDerivAt_integral_of_dominated_of_fderiv_le, norm_iteratedFDeriv_le_of_bilinear, curryLeftLI, norm_curryLeft, curryLeft_apply_apply, iteratedFDeriv_comp_right, continuous_iteratedFDeriv, iteratedFDeriv_succ_eq_comp_left, continuous_parametric_intervalIntegral_of_continuous, contDiff_of_differentiable_iteratedFDeriv, intervalIntegral_comp_comm, norm_compContinuousLinearMap_le, norm_integral_le_of_norm_le_const, contDiff_parametric_integral_of_contDiff, contDiff_parametric_primitive_of_contDiff`
- `rg -n 'contDiff_parametric|ContDiff.*intervalIntegral|contDiff_integral|iteratedFDeriv_integral|integral_iteratedFDeriv|contDiffOn_parametric|fderiv_integral|hasFDerivAt_integral\b' mathlib/Mathlib`
- `rg -n 'parametric_primitive|parametric_integral|ParametricIntegral' mathlib/Mathlib`
- `rg -n 'norm_iteratedFDeriv_le_of_bilinear_of_le_one|norm_iteratedFDeriv_clm_apply|iteratedFDeriv_const_smul_apply|iteratedFDeriv_const_of_ne|theorem fderiv_id|prod_le_one₀|iteratedFDeriv_succ_eq_comp_right|contDiff_succ_iff_fderiv|contDiff_infty|iteratedFDeriv_one_apply|norm_iteratedFDeriv_one|intervalIntegral_comp_comm' mathlib/Mathlib`
- `rg -n 'def apply' mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Topology.lean`
- `rg -n 'iteratedFDeriv_fixedSupportParameterSlice|intervalIntegral|∫ t in' simongmt/Poincare/SimonGMT; grep -n 'abbrev|^def' simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `python3: dag.json node metadata and lean_name scan (iwl_cr_*, radial, lean_statements containing ∫ together with fderiv/iteratedFDeriv/ContDiff); grep -rl iwl_cr_ro_ over dag.json, nodes/ and GMT/; git grep -l iwl_cr_ro_ over all 619 ref tips`
- `git show 2f3657605e574458d48b2cd837f262ae2f392816:GMT/Ch06/Submission.lean (imports and Submission.X declaration layout of an accepted candidate)`
- `python3 -I /tmp/ro_split/scripts/gen.py (verifier gmt-compare.py child_modules + lean_contract.validate_lean_statement); lake env lean /tmp/ro_split/gen/*__NodeChallenge.lean`
- `lake env lean /tmp/ro_split/scratch/{Assembly,Full,InstCheck,ImportCheck}.lean and /tmp/ro_split/snip/Snip{A,B1,B2}.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-radial-operator-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-radial-operator-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-radial-operator-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Bounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Multilinear/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/ParametricCurrentContinuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ro_split/scripts/gen.py`
- `/tmp/ro_split/scratch/Assembly.lean`
- `/tmp/ro_split/scratch/Full.lean`
- `/tmp/ro_split/scratch/InstCheck.lean`
- `/tmp/ro_split/scratch/ImportCheck.lean`
- `/tmp/ro_split/snip/SnipA.lean`
- `/tmp/ro_split/snip/SnipB1.lean`
- `/tmp/ro_split/snip/SnipB2.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c. Its Ch06 Contract.lean is byte-identical to the workspace Contract.lean (sha256 ea3ee0dd…).

Missing obligation. The snapshot Mathlib has only first-order differentiation under an interval integral (`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`, Analysis/Calculus/ParametricIntervalIntegral.lean:55) and continuity of parametric integrals (`continuous_parametric_intervalIntegral_of_continuous'`, DominatedConvergence.lean:619). There is no lemma for C^∞ smoothness of x ↦ ∫ G(t,x) dt or for iterated derivatives under the integral: the searches for contDiff_parametric*, ContDiff.*intervalIntegral and iteratedFDeriv_integral found nothing. So the all-order statement is a genuinely missing, reusable obligation, which becomes child parametric_integral.

Available Mathlib tools:
- Leibniz bounds `ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear(_of_le_one)` (ContDiff/Bounds.lean:202/226);
- curryLeft, curryLeftLI, norm_curryLeft and curryLeft_apply_apply (Normed/Module/Alternating/Curry.lean);
- `ContinuousLinearMap.iteratedFDeriv_comp_right` (ContDiff/Basic.lean:461);
- `iteratedFDeriv_succ_eq_comp_right` and `iteratedFDeriv_one_apply` (FTaylorSeries.lean);
- `contDiff_succ_iff_fderiv` and `contDiff_infty` (ContDiff/Defs.lean);
- `ContinuousAlternatingMap.apply` and `ContinuousMultilinearMap.apply` (Topology/Algebra/Module/{Alternating,Multilinear}/Topology.lean).

Imports. ParametricIntervalIntegral and ContDiff.Bounds are not imported by GMT.Ch06.Submission (an #check reports unknown constants), so children 1 and 3 add those imports. The accepted candidate at commit 2f36576 also adds imports to Submission.lean and declares `theorem Submission.X` inside namespace GMT.Ch06.

SimonGMT. Covector and DifferentialForm are abbrevs (Chapter06/Forms.lean:31/37). `iteratedFDeriv_fixedSupportParameterSlice` (Chapter06/ParametricCurrentContinuity.lean:76) uses the same partial-derivative-by-inclusion pattern, but SimonGMT has no smoothness result for parametric integrals.

DAG and names. No DAG node supplies a parametric-integral smoothness lemma or the radial integrand facts. The names iwl_cr_ro_* and the helper prefixes iwl_cr_ro_pi_ / iwl_cr_ro_ib_ occur nowhere in dag.json, nodes/, GMT/ or any of the 619 git ref tips.

Lean checks:
- The three frozen child types, generated through the verifier's own child_modules / validate_lean_statement path, elaborate in the replayed contract scope.
- Assembly.lean proves the parent's exact frozen type from the three children, which are sorried there.
- Full.lean and Snip{A,B1,B2}.lean prove all three children and the parent; #print axioms gives [propext, Classical.choice, Quot.sound], and the comparator-style `exact Submission.<name>` targets pass.
- An independent reviewer agent re-ran these builds and accepted the split.

Public citations for the standard mathematics: differentiation under the integral sign (Dieudonné, Foundations of Modern Analysis, §8.11) and the radial homotopy operator of the Poincaré lemma (Spivak, Calculus on Manifolds, Thm 4-11).
