# Parent-supplied natural-language proof

- Parent DAG node: `root.whitney_extension-a1.whitney_gluing-a1`
- Child DAG node: `root.whitney_extension-a1.whitney_gluing-a1.first_order_on_set-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: (E1), step 2 and step 3 of the supplied proof of whitney_jet_gluing_c1. The convex-combination representation (R) at points x ∉ A is a hypothesis here; the supplied proof derives it in (1a), (1b) and (1f) from (P3)-(P6). (P2), (P4), (P5) and (P7) are not needed.

Notation. d(x) := Metric.infDist x A. For v ∈ ℝⁿ, L_v := innerSL ℝ v, so L_v(w) = ⟨v, w⟩ (innerSL_apply_apply).

Proof. Fix a ∈ A. By HasFDerivAt.of_isLittleO and Asymptotics.IsLittleO.of_bound, it suffices to show: for every c > 0, the inequality |g(x) − g(a) − L_{ν(a)}(x − a)| ≤ c‖x − a‖ holds for all x in some neighbourhood of a. Fix c > 0.

1. Put ε := c/(2C + 1). Since C ≥ 0, 2C + 1 ≥ 1 > 0, so ε > 0 and (2C + 1)ε = c.

2. Let K := A ∩ B̄(a, 1). The closed ball is compact in the proper space ℝⁿ and A is closed, so K is compact (IsCompact.inter_left). Also K ⊆ A and a ∈ K. Apply (W) to K and ε: there is δ₁ > 0 with |h(y) − h(b) − ⟨ν(b), y − b⟩| ≤ ε‖y − b‖ for all b ∈ K and y ∈ A with 0 < ‖y − b‖ < δ₁. Take b := a; for y = a both sides vanish. Hence
(2a) |h(y) − h(a) − ⟨ν(a), y − a⟩| ≤ ε‖y − a‖ for every y ∈ A with ‖y − a‖ < δ₁.

3. ν is continuous on A and a ∈ A, so (Metric.continuousWithinAt_iff) there is τ > 0 with ‖ν(y) − ν(a)‖ < ε for all y ∈ A with ‖y − a‖ < τ.

4. Put r := min{1, δ₁, τ} > 0 and ρ := r/(C + 2) > 0. Since C ≥ 0 and r > 0, we have (C + 1)ρ = (C + 1)r/(C + 2) < r and ρ ≤ (C + 1)ρ < r.

5. Let x ∈ ℝⁿ with ‖x − a‖ < ρ; the open ball B(a, ρ) is a neighbourhood of a. Recall g(a) = h(a). We show |g(x) − h(a) − ⟨ν(a), x − a⟩| ≤ (2C + 1)ε‖x − a‖.
Case x ∈ A. Then g(x) = h(x) and ‖x − a‖ < ρ < r ≤ δ₁. By (2a) the left side is ≤ ε‖x − a‖ ≤ (2C + 1)ε‖x − a‖.
Case x ∉ A. Take S from (R). Put Q_i := h(p_i) + ⟨ν(p_i), x − p_i⟩ and q := h(a) + ⟨ν(a), x − a⟩. Since Σ_{i∈S} φ_i(x) = 1,
(5a) g(x) − q = Σ_{i∈S} φ_i(x)Q_i − (Σ_{i∈S} φ_i(x))q = Σ_{i∈S} φ_i(x)(Q_i − q).
Fix i ∈ S. We bound |Q_i − q| in six steps.
(i) d(x) ≤ ‖x − a‖ because a ∈ A (infDist_le_dist_of_mem). With C ≥ 0 and (R): ‖x − p_i‖ ≤ C·d(x) ≤ C‖x − a‖.
(ii) ‖p_i − a‖ = ‖(x − a) − (x − p_i)‖ ≤ ‖x − a‖ + ‖x − p_i‖ ≤ (C + 1)‖x − a‖ ≤ (C + 1)ρ < r.
(iii) p_i ∈ A and ‖p_i − a‖ < r ≤ τ, so ‖ν(p_i) − ν(a)‖ < ε by step 3.
(iv) p_i ∈ A and ‖p_i − a‖ < r ≤ δ₁. By (2a) and (ii), |h(p_i) − h(a) − ⟨ν(a), p_i − a⟩| ≤ ε‖p_i − a‖ ≤ ε(C + 1)‖x − a‖.
(v) (E1) Since x − a = (x − p_i) + (p_i − a), we have ⟨ν(a), x − a⟩ = ⟨ν(a), x − p_i⟩ + ⟨ν(a), p_i − a⟩. Hence Q_i − q = [h(p_i) − h(a) − ⟨ν(a), p_i − a⟩] + ⟨ν(p_i) − ν(a), x − p_i⟩.
(vi) By Cauchy–Schwarz (abs_real_inner_le_norm), (iii) and (i): |⟨ν(p_i) − ν(a), x − p_i⟩| ≤ ‖ν(p_i) − ν(a)‖·‖x − p_i‖ ≤ ε·C‖x − a‖.
By (v), (iv), (vi) and the triangle inequality, |Q_i − q| ≤ ε(C + 1)‖x − a‖ + εC‖x − a‖ = (2C + 1)ε‖x − a‖.
For i ∈ S we have φ_i(x) ≥ 0, and Σ_{i∈S} φ_i(x) = 1. So (5a) gives |g(x) − q| ≤ Σ_{i∈S} φ_i(x)|Q_i − q| ≤ Σ_{i∈S} φ_i(x)(2C + 1)ε‖x − a‖ = (2C + 1)ε‖x − a‖.

6. In both cases, |g(x) − g(a) − L_{ν(a)}(x − a)| ≤ (2C + 1)ε‖x − a‖ = c‖x − a‖ for all x ∈ B(a, ρ) ∈ 𝓝 a. As c > 0 was arbitrary, g(x) − g(a) − L_{ν(a)}(x − a) = o(x − a) as x → a, that is, HasFDerivAt g (innerSL ℝ (ν a)) a. Since a ∈ A was arbitrary, the theorem follows. ∎

Formalization remark (non-normative; the numbered proof above is complete without it). During the decomposition session the frozen type was proved verbatim by the following declaration. It was kernel-checked against a scratch build of GMT.Ch02.Submission at the frozen commit, with Lean v4.35.0-rc3 and Mathlib 25730c7c, and uses only the axioms propext, Classical.choice and Quot.sound. It follows steps 1-6 above. Placed inside `namespace GMT.Ch02` of GMT/Ch02/Submission.lean, before `main_theorem`, it elaborates unchanged:

theorem Submission.whitney_gluing_hasFDerivAt : (∀ (n : ℕ) (A : Set (Rn n)) (h : Rn n → ℝ) (ν : Rn n → Rn n) (ι : Type) (φ : ι → Rn n → ℝ) (p : ι → Rn n) (C : ℝ) (g : Rn n → ℝ), IsClosed A → ContinuousOn ν A → (∀ K ⊆ A, IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y ∈ A, 0 < ‖y - x‖ → ‖y - x‖ < δ → |h y - h x - inner ℝ (ν x) (y - x)| ≤ ε * ‖y - x‖) → 0 ≤ C → (∀ i, p i ∈ A) → (∀ x ∈ A, g x = h x) → (∀ x ∉ A, ∃ S : Finset ι, (∀ i ∈ S, 0 ≤ φ i x ∧ ‖x - p i‖ ≤ C * Metric.infDist x A) ∧ ∑ i ∈ S, φ i x = 1 ∧ g x = ∑ i ∈ S, φ i x * (h (p i) + inner ℝ (ν (p i)) (x - p i))) → ∀ a ∈ A, HasFDerivAt g (innerSL ℝ (ν a)) a) := by
  intro n A h ν ι φ p C g hA hν hW hC hp hgA hrep a ha
  apply HasFDerivAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have hC1 : 0 < 2 * C + 1 := by linarith
  set ε := c / (2 * C + 1) with hε_def
  have hε : 0 < ε := div_pos hc hC1
  have hεc : (2 * C + 1) * ε = c := by rw [hε_def]; field_simp
  set K : Set (Rn n) := A ∩ closedBall a 1 with hK_def
  have hK : IsCompact K := (isCompact_closedBall a 1).inter_left hA
  obtain ⟨δ₁, hδ₁, hWK⟩ := hW K inter_subset_left hK ε hε
  obtain ⟨τ, hτ, hντ⟩ := Metric.continuousWithinAt_iff.mp (hν a ha) ε hε
  set r := min 1 (min δ₁ τ) with hr_def
  have hr : 0 < r := lt_min one_pos (lt_min hδ₁ hτ)
  have hrδ : r ≤ δ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hrτ : r ≤ τ := (min_le_right _ _).trans (min_le_right _ _)
  set ρ := r / (C + 2) with hρ_def
  have hC2 : 0 < C + 2 := by linarith
  have hρ : 0 < ρ := div_pos hr hC2
  have hρr : (C + 1) * ρ < r := by
    rw [hρ_def, mul_div_assoc', div_lt_iff₀ hC2]
    nlinarith
  have hρr' : ρ < r := by
    have : ρ ≤ (C + 1) * ρ := by nlinarith
    linarith
  have haK : a ∈ K := ⟨ha, mem_closedBall_self zero_le_one⟩
  have hWa : ∀ b ∈ A, ‖b - a‖ < δ₁ → |h b - h a - inner ℝ (ν a) (b - a)| ≤ ε * ‖b - a‖ := by
    intro b hb hba
    rcases eq_or_ne b a with rfl | hne
    · simp
    · exact hWK a haK b hb (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) hba
  filter_upwards [Metric.ball_mem_nhds a hρ] with x hx
  have hxa : ‖x - a‖ < ρ := by simpa [dist_eq_norm] using hx
  rw [innerSL_apply_apply, hgA a ha, Real.norm_eq_abs, ← hεc]
  by_cases hxA : x ∈ A
  · rw [hgA x hxA]
    have h1 := hWa x hxA (by linarith)
    have h2 : ε * ‖x - a‖ ≤ (2 * C + 1) * ε * ‖x - a‖ := by
      have : ε ≤ (2 * C + 1) * ε := by nlinarith
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    exact h1.trans h2
  · obtain ⟨S, hS, hS1, hval⟩ := hrep x hxA
    have hid : g x - h a - inner ℝ (ν a) (x - a) = ∑ i ∈ S, φ i x *
        ((h (p i) + inner ℝ (ν (p i)) (x - p i)) - (h a + inner ℝ (ν a) (x - a))) := by
      rw [hval]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hS1, one_mul]
      ring
    rw [hid]
    have hdx : infDist x A ≤ ‖x - a‖ := by rw [← dist_eq_norm]; exact infDist_le_dist_of_mem ha
    have hterm : ∀ i ∈ S, |(h (p i) + inner ℝ (ν (p i)) (x - p i)) - (h a + inner ℝ (ν a) (x - a))|
        ≤ (2 * C + 1) * ε * ‖x - a‖ := by
      intro i hi
      have hxp : ‖x - p i‖ ≤ C * ‖x - a‖ := (hS i hi).2.trans (mul_le_mul_of_nonneg_left hdx hC)
      have hpa : ‖p i - a‖ ≤ (C + 1) * ‖x - a‖ := by
        calc ‖p i - a‖ = ‖(x - a) - (x - p i)‖ := by congr 1; abel
          _ ≤ ‖x - a‖ + ‖x - p i‖ := norm_sub_le _ _
          _ ≤ ‖x - a‖ + C * ‖x - a‖ := by linarith
          _ = (C + 1) * ‖x - a‖ := by ring
      have hpa_lt : ‖p i - a‖ < r := by
        have : (C + 1) * ‖x - a‖ ≤ (C + 1) * ρ := mul_le_mul_of_nonneg_left hxa.le (by linarith)
        linarith
      have hνi : ‖ν (p i) - ν a‖ ≤ ε := by
        have := hντ (hp i) (by rw [dist_eq_norm]; linarith)
        rw [dist_eq_norm] at this
        exact this.le
      have hWi := hWa (p i) (hp i) (by linarith)
      have hE1 : (h (p i) + inner ℝ (ν (p i)) (x - p i)) - (h a + inner ℝ (ν a) (x - a)) =
          (h (p i) - h a - inner ℝ (ν a) (p i - a)) + inner ℝ (ν (p i) - ν a) (x - p i) := by
        have hsplit : x - a = (x - p i) + (p i - a) := by abel
        rw [inner_sub_left, hsplit, inner_add_right]
        ring
      rw [hE1]
      calc |(h (p i) - h a - inner ℝ (ν a) (p i - a)) + inner ℝ (ν (p i) - ν a) (x - p i)|
          ≤ |h (p i) - h a - inner ℝ (ν a) (p i - a)| + |inner ℝ (ν (p i) - ν a) (x - p i)| :=
            abs_add_le _ _
        _ ≤ ε * ‖p i - a‖ + ‖ν (p i) - ν a‖ * ‖x - p i‖ :=
            add_le_add hWi (abs_real_inner_le_norm _ _)
        _ ≤ ε * ((C + 1) * ‖x - a‖) + ε * (C * ‖x - a‖) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hpa hε.le
            · exact mul_le_mul hνi hxp (norm_nonneg _) hε.le
        _ = (2 * C + 1) * ε * ‖x - a‖ := by ring
    calc |∑ i ∈ S, φ i x * ((h (p i) + inner ℝ (ν (p i)) (x - p i)) - (h a + inner ℝ (ν a) (x - a)))|
        ≤ ∑ i ∈ S, |φ i x * ((h (p i) + inner ℝ (ν (p i)) (x - p i)) - (h a + inner ℝ (ν a) (x - a)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ S, φ i x * |(h (p i) + inner ℝ (ν (p i)) (x - p i)) - (h a + inner ℝ (ν a) (x - a))| := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [abs_mul, abs_of_nonneg (hS i hi).1]
      _ ≤ ∑ i ∈ S, φ i x * ((2 * C + 1) * ε * ‖x - a‖) := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left (hterm i hi) (hS i hi).1
      _ = (2 * C + 1) * ε * ‖x - a‖ := by rw [← Finset.sum_mul, hS1, one_mul]

## Key steps

1. Fix a ∈ A and c > 0 and put ε := c/(2C+1). (W) on the compact K = A ∩ B̄(a,1) gives δ₁, continuity of ν at a gives τ; set r := min{1,δ₁,τ} and ρ := r/(C+2).
2. If x ∈ A and |x−a| < ρ: (W) with base point a gives |g(x) − g(a) − ⟨ν(a), x−a⟩| ≤ ε|x−a|.
3. If x ∉ A: g(x) − q = Σ_S φ_i(x)(Q_i − q), with |x−p_i| ≤ C|x−a| and |p_i−a| ≤ (C+1)|x−a| < r. (E1), (W) and continuity of ν then give |Q_i − q| ≤ (2C+1)ε|x−a|.
4. The weights are convex, so |g(x) − g(a) − ⟨ν(a), x−a⟩| ≤ c|x−a| on B(a,ρ). IsLittleO.of_bound and HasFDerivAt.of_isLittleO conclude.

## Reference use

### local-project

Queries:
- `cmp local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean workspaces/gmt-ch02/GMT/Ch02/Contract.lean`
- `rg -n "Whitney|whitney" local-references/ff09f3909baeeae7/project/GMT`
- `rg -n "whitney_gluing_local_structure|whitney_gluing_hasFDerivAt|whitney_gluing_continuousAt_fderiv" <run dir> local-references/ff09f3909baeeae7/project local-references/ff09f3909baeeae7/mathlib/Mathlib lake-packages-25730c7c/simongmt/Poincare (exit 1: no match); dag.json lean_name scan for the same names (absent)`
- `rg -n "theorem IsLocalMin.fderiv_eq_zero|theorem innerSL_apply_apply|theorem innerSL_apply_norm|theorem contDiff_one_iff_fderiv|theorem ContDiffAt.continuousAt_fderiv|theorem ContDiffAt.congr_of_eventuallyEq|theorem HasFDerivAt.mul |theorem ContDiffAt.sum|theorem abs_real_inner_le_norm|theorem infDist_le_dist_of_mem|theorem IsCompact.inter_left|theorem abs_sum_le_sum_abs" mathlib/Mathlib`
- `rg -n "finsum_eq_sum_of_support_subset|theorem sum_filter_of_ne|theorem sum_filter_ne_zero|exists_infDist_eq_dist|notMem_iff_infDist_pos|HasFDerivAt.of_isLittleO|EventuallyEq.fderiv_eq" mathlib/Mathlib`
- `rg -n "theorem finsum_eq_sum_of_support_subset|theorem prod_filter_of_ne|theorem prod_filter_ne_one|theorem HasFDerivAt.sum|theorem IsLittleO.of_bound|theorem continuousWithinAt_iff|theorem continuousAt_iff|theorem HasFDerivAt.unique|theorem HasFDerivAt.congr_of_eventuallyEq|theorem hasFDerivAt_const|theorem mem_of_mem_nhds" mathlib/Mathlib`
- `full reads of lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean and WhitneyExtension.lean; ls simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02 | grep -i whitney; grep import Poincare/SimonGMT.lean | grep -i whitney (exit 1)`
- `lean -R . -o /tmp/gluing-decomp/build/GMT/Ch02/Submission.olean GMT/Ch02/Submission.lean (scratch copy of the frozen Submission; LEAN_PATH = scratch build + shared package oleans, read-only)`
- `python3 -I gen.py (gmt-compare.py layout/child_modules + lean_contract.validate_lean_statement), then lean NodeChallenge_00.lean NodeChallenge_01.lean NodeChallenge_02.lean`
- `lean asm/AssemblyCheck.lean; lean c1/Child1Check.lean; lean c2/Child2Check.lean; lean c3/Child3Check.lean (each with #print axioms)`
- `lean full/GMT/Ch02/Submission.lean (copy with Submission.whitney_gluing_* and Submission.whitney_jet_gluing_c1 inserted before main_theorem), then lean full/NodeSolution_0..3.lean (exact Submission.X)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/LocalExtr/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Algebra/BigOperators/Finprod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Neighborhoods.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-whitney-extension-a1-whitney-gluing-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-whitney-extension-a1-whitney-gluing-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-whitney-extension-a1/decomposition-v1.json`
- `/tmp/gluing-decomp/gen-v1/NodeChallenge_00.lean`
- `/tmp/gluing-decomp/gen-v1/NodeChallenge_01.lean`
- `/tmp/gluing-decomp/gen-v1/NodeChallenge_02.lean`
- `/tmp/gluing-decomp/asm/AssemblyCheck.lean`
- `/tmp/gluing-decomp/c1/Child1Check.lean`
- `/tmp/gluing-decomp/c2/Child2Check.lean`
- `/tmp/gluing-decomp/c3/Child3Check.lean`
- `/tmp/gluing-decomp/full/GMT/Ch02/Submission.lean`

Snapshot and names:
- The snapshot's project/GMT/Ch02/Contract.lean is byte-identical to the workspace contract (cmp).
- In project/GMT, 'Whitney' occurs only in the WhitneyExtension definition (Contract/Submission lines 204-208) and README rows 3-4.
- None of the three proposed names occurs anywhere: run directory, dag.json lean_name fields, snapshot project, snapshot Mathlib, or simongmt (rg exit 1). The names are unreserved.

Mathlib reuse. Snapshot Mathlib has no abstract Whitney-gluing lemma, but supplies every tool the child proofs cite:
- IsLocalMin.fderiv_eq_zero (LocalExtr/Basic.lean:181);
- finsum_eq_sum_of_support_subset (to_additive of Finprod.lean:350);
- Finset.sum_filter_of_ne / sum_filter_ne_zero (to_additive of Group/Finset/Basic.lean:319/328);
- innerSL_apply_apply and innerSL_apply_norm (InnerProductSpace/LinearMap.lean:172/225);
- abs_real_inner_le_norm (InnerProductSpace/Basic.lean:471);
- ContDiffAt.congr_of_eventuallyEq and contDiff_one_iff_fderiv (ContDiff/Defs.lean:966/1261);
- ContDiffAt.continuousAt_fderiv (ContDiff/Comp.lean:816);
- ContDiffAt.sum (ContDiff/Operations.lean:369);
- HasFDerivAt.mul (FDeriv/Mul.lean:205);
- HasFDerivAt.sum, with fun_sum generated by to_fun (FDeriv/Add.lean:418);
- HasFDerivAt.unique (FDeriv/Basic.lean:174);
- HasFDerivAt.congr_of_eventuallyEq and Filter.EventuallyEq.fderiv_eq (FDeriv/Congr.lean:176/260);
- hasFDerivAt_const (FDeriv/Const.lean:115);
- HasFDerivAt.of_isLittleO (FDeriv/Defs.lean:230);
- IsLittleO.of_bound (Asymptotics/Defs.lean:185);
- infDist_le_dist_of_mem, IsClosed.notMem_iff_infDist_pos and IsClosed.exists_infDist_eq_dist (HausdorffDistance.lean:500/584/615);
- Metric.continuousAt_iff and continuousWithinAt_iff (Pseudo/Defs.lean:871/875);
- IsCompact.inter_left (Compactness/Compact.lean:96);
- abs_sum_le_sum_abs (Order/BigOperators/Group/Finset.lean:371);
- mem_of_mem_nhds (Neighborhoods.lean:85).

SimonGMT. The pinned WhitneyExtension.lean proves the analogous facts for its own WhitneyBallCover:
- whitneyExtension_contDiffAt_compl and whitneyExtension_fderiv_eq_near_sum correspond to child 1;
- HasWhitneyC1Compatibility.hasFDerivAt_whitneyExtension corresponds to child 2;
- continuousAt_fderiv_whitneyExtension, with norm_fderiv_whitneyExtension_sub_le, corresponds to child 3.
WhitneyExtension has no .olean (only WhitneyCover/Jet/Partition do), and Poincare/SimonGMT.lean imports no Whitney file. So it served only as a template, and the children were proved from Mathlib alone.

Lean checks. All ran in /tmp scratch with the pinned toolchain; the shared package tree and workspace stayed untouched.
- The three types elaborate in the verifier-generated NodeChallenge modules.
- AssemblyCheck derives the selected exact type from them.
- Child1-3Check prove each exact type.
- The Submission copy compiles Submission.whitney_gluing_* and Submission.whitney_jet_gluing_c1, and NodeSolution_0..3 pass.
- #print axioms reports only propext, Classical.choice and Quot.sound everywhere.
