# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.unit_ball_estimate-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.unit_ball_estimate-a1.absorption-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1, 6 and 7 of the parent proof (definition of Q, absorption, conclusion), with Dw replaced by g and 2 C_delta M by A. The parent's Q (a supremum of rho^{1+alpha} [Dw]_{B_{rho/2}(y)} over admissible pairs) is realized, as suggested in the parent's Lean notes, as one supremum of ratios. Steps 3-5 of the parent are supplied by the sibling lemma holder_improvement (dependency).
1. Admissible pairs. If (y, rho) is admissible (rho > 0, |y| + rho <= 1), then 0 < rho <= 1 (as |y| >= 0), so rho^{1+alpha} <= 1; and every x in B_{rho/2}(y) satisfies |x| <= |y| + |x - y| < |y| + rho/2 < 1, so B_{rho/2}(y) is contained in B_1(0). The pair (0, 1) is admissible and its half ball is B_{1/2}(0).
2. The set T and Q. Let T be the set of real numbers consisting of 0 together with all quotients q = rho^{1+alpha} ||g(x) - g(x')|| / |x - x'|^alpha, where (y, rho) is admissible, x and x' are in B_{rho/2}(y), and x != x'. For such a quotient |x - x'| > 0, so |x - x'|^alpha > 0, and by step 1 and (H7'), rho^{1+alpha} ||g(x) - g(x')|| <= ||g(x) - g(x')|| <= K0 |x - x'|^alpha, so q <= K0. Hence T is nonempty (0 is in T) and bounded above by max(K0, 0). Let Q := sup T, a real number; since 0 is in T, Q >= 0.
3. (P1) holds with Q. Let (y, rho) be admissible and x, x' in B_{rho/2}(y). If x = x', both sides of rho^{1+alpha} ||g(x) - g(x')|| <= Q |x - x'|^alpha are 0 (0^alpha = 0 because alpha > 0). If x != x', the corresponding quotient q lies in T, so q <= Q (le_csSup), and multiplying by |x - x'|^alpha > 0 gives rho^{1+alpha} ||g(x) - g(x')|| <= Q |x - x'|^alpha.
4. Improvement. The hypotheses of the sibling lemma holder_improvement hold for (g, alpha, M, A, Q): 0 < alpha <= 1; M, A, Q >= 0; (P1) by step 3; (P2) and (P3) by assumption. Hence for every admissible (y, rho): (a) rho ||g(x)|| <= 32 M + Q/4 + 16 A for x in B_{rho/2}(y); (b) rho^{1+alpha} ||g(x) - g(x')|| <= (Q/2 + 512 M + 32 A) |x - x'|^alpha for x, x' in B_{rho/2}(y).
5. Absorption (parent 6e). Every element of T is at most Q/2 + 512 M + 32 A: the element 0 because Q, M, A >= 0; a quotient q by (b), divided by |x - x'|^alpha > 0. Since T is nonempty, its least upper bound satisfies Q <= Q/2 + 512 M + 32 A (csSup_le). As Q is a finite real number, Q <= 1024 M + 64 A.
6. Conclusion (parent 6f). Take (y, rho) = (0, 1). For x, x' in B_{1/2}(0), step 3 gives ||g(x) - g(x')|| = 1^{1+alpha} ||g(x) - g(x')|| <= Q |x - x'|^alpha <= (1024 M + 64 A) |x - x'|^alpha, as |x - x'|^alpha >= 0. By (a) with rho = 1, ||g(x)|| <= 32 M + Q/4 + 16 A <= 32 M + (256 M + 16 A) + 16 A = 288 M + 32 A <= 1024 M + 64 A. QED
Lean proof checked at the pin (Lean 4.35.0-rc3, Mathlib 25730c7c; stated inside `namespace GMT.Ch05` with the contract's `open`s, appended to a scratch copy of the submission after the holder_improvement child; the generated NodeSolution target closes by `exact Submission.dohr_eb_sch_ube_absorption`; #print axioms: propext, Classical.choice, Quot.sound):
set_option maxSynthPendingDepth 3 in
theorem Submission.dohr_eb_sch_ube_absorption : ∀ (n ℓ : ℕ) (g : Rn n → (Rn n →L[ℝ] Rn ℓ)) (α M A : ℝ), 0 < α → α ≤ 1 → 0 ≤ M → 0 ≤ A → (∃ K : ℝ, ∀ x ∈ ball (0 : Rn n) 1, ∀ y ∈ ball (0 : Rn n) 1, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α) → (∀ (y : Rn n) (ρ K : ℝ), 0 < ρ → ‖y‖ + ρ ≤ 1 → (∀ x ∈ ball y ρ, ∀ x' ∈ ball y ρ, ‖g x - g x'‖ ≤ K * ‖x - x'‖ ^ α) → ∀ x ∈ ball y (ρ / 2), ∀ x' ∈ ball y (ρ / 2), ρ ^ (1 + α) * ‖g x - g x'‖ ≤ (1 / 16 * ρ ^ (1 + α) * K + A) * ‖x - x'‖ ^ α) → (∀ (x : Rn n) (r t K : ℝ), ‖x‖ + r ≤ 1 → 0 ≤ K → 0 < t → t < r → (∀ z ∈ ball x r, ∀ z' ∈ ball x r, ‖g z - g z'‖ ≤ K * ‖z - z'‖ ^ α) → ‖g x‖ ≤ 2 * M / t + t ^ α * K) → (∀ x ∈ ball (0 : Rn n) (1 / 2), ‖g x‖ ≤ 1024 * M + 64 * A) ∧ ∀ x ∈ ball (0 : Rn n) (1 / 2), ∀ y ∈ ball (0 : Rn n) (1 / 2), ‖g x - g y‖ ≤ (1024 * M + 64 * A) * ‖x - y‖ ^ α := by
  have hImp := Submission.dohr_eb_sch_ube_holder_improvement
  intro n ℓ g α M A hα0 hα1 hM hA hK hP2 hP3
  obtain ⟨K0, hK0⟩ := hK
  have hmem : ∀ (y : Rn n) (ρ : ℝ) (x : Rn n), ‖y‖ + ρ ≤ 1 → x ∈ ball y (ρ / 2) → 0 < ρ →
      x ∈ ball (0 : Rn n) 1 := by
    intro y ρ x hyρ hx hρ
    rw [mem_ball, dist_eq_norm] at hx
    rw [mem_ball_zero_iff]
    calc ‖x‖ = ‖y + (x - y)‖ := by rw [add_sub_cancel]
      _ ≤ ‖y‖ + ‖x - y‖ := norm_add_le _ _
      _ < ‖y‖ + ρ / 2 := by linarith
      _ ≤ 1 := by linarith
  let T : Set ℝ := {q | q = 0 ∨ ∃ (y : Rn n) (ρ : ℝ) (x x' : Rn n), 0 < ρ ∧ ‖y‖ + ρ ≤ 1 ∧
      x ∈ ball y (ρ / 2) ∧ x' ∈ ball y (ρ / 2) ∧ x ≠ x' ∧
      q = ρ ^ (1 + α) * ‖g x - g x'‖ / ‖x - x'‖ ^ α}
  have hbdd : BddAbove T := by
    refine ⟨max K0 0, ?_⟩
    rintro q (rfl | ⟨y, ρ, x, x', hρ, hyρ, hx, hx', hne, rfl⟩)
    · exact le_max_right _ _
    · have hxx : 0 < ‖x - x'‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
      have hpow : 0 < ‖x - x'‖ ^ α := Real.rpow_pos_of_pos hxx α
      have hρ1 : ρ ≤ 1 := by linarith [norm_nonneg y]
      have hρa : ρ ^ (1 + α) ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by linarith)
      have h := hK0 x (hmem y ρ x hyρ hx hρ) x' (hmem y ρ x' hyρ hx' hρ)
      rw [div_le_iff₀ hpow]
      calc ρ ^ (1 + α) * ‖g x - g x'‖ ≤ 1 * ‖g x - g x'‖ :=
            mul_le_mul_of_nonneg_right hρa (norm_nonneg _)
        _ ≤ K0 * ‖x - x'‖ ^ α := by rw [one_mul]; exact h
        _ ≤ max K0 0 * ‖x - x'‖ ^ α :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hpow.le
  have h0T : (0 : ℝ) ∈ T := Or.inl rfl
  set Q := sSup T with hQ
  have hQ0 : 0 ≤ Q := le_csSup hbdd h0T
  have hP1 : ∀ (y : Rn n) (ρ : ℝ), 0 < ρ → ‖y‖ + ρ ≤ 1 → ∀ x ∈ ball y (ρ / 2),
      ∀ x' ∈ ball y (ρ / 2), ρ ^ (1 + α) * ‖g x - g x'‖ ≤ Q * ‖x - x'‖ ^ α := by
    intro y ρ hρ hyρ x hx x' hx'
    by_cases hne : x = x'
    · subst hne
      simp [Real.zero_rpow hα0.ne']
    · have hxx : 0 < ‖x - x'‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
      have hpow : 0 < ‖x - x'‖ ^ α := Real.rpow_pos_of_pos hxx α
      have hq : ρ ^ (1 + α) * ‖g x - g x'‖ / ‖x - x'‖ ^ α ∈ T :=
        Or.inr ⟨y, ρ, x, x', hρ, hyρ, hx, hx', hne, rfl⟩
      have := le_csSup hbdd hq
      rwa [div_le_iff₀ hpow] at this
  have himp := hImp n ℓ g α M A Q hα0 hα1 hM hA hQ0 hP1 hP2 hP3
  have hQle : Q ≤ Q / 2 + 512 * M + 32 * A := by
    apply csSup_le ⟨0, h0T⟩
    rintro q (rfl | ⟨y, ρ, x, x', hρ, hyρ, hx, hx', hne, rfl⟩)
    · linarith
    · have hxx : 0 < ‖x - x'‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
      have hpow : 0 < ‖x - x'‖ ^ α := Real.rpow_pos_of_pos hxx α
      rw [div_le_iff₀ hpow]
      exact (himp y ρ hρ hyρ).2 x hx x' hx'
  have hQC : Q ≤ 1024 * M + 64 * A := by linarith
  have h01 : ‖(0 : Rn n)‖ + 1 ≤ 1 := by simp
  obtain ⟨hsup, -⟩ := himp 0 1 one_pos h01
  constructor
  · intro x hx
    have h := hsup x hx
    rw [one_mul] at h
    linarith
  · intro x hx y hy
    have h := hP1 0 1 one_pos h01 x hx y hy
    rw [Real.one_rpow, one_mul] at h
    calc ‖g x - g y‖ ≤ Q * ‖x - y‖ ^ α := h
      _ ≤ (1024 * M + 64 * A) * ‖x - y‖ ^ α :=
          mul_le_mul_of_nonneg_right hQC (Real.rpow_nonneg (norm_nonneg _) _)

## Key steps

1. for admissible (y, rho): rho^{1+alpha} <= 1 and B_{rho/2}(y) is contained in B_1(0)
2. T := {0} together with all rho^{1+alpha} ||g(x) - g(x')|| / |x - x'|^alpha (x != x'); T is bounded above by max(K0, 0) via (H7'); Q := sup T >= 0
3. (P1) holds with Q (le_csSup; x = x' trivially)
4. holder_improvement gives (a) rho ||g(x)|| <= 32M + Q/4 + 16A and (b) the weighted bound with constant Q/2 + 512M + 32A
5. csSup_le: Q <= Q/2 + 512M + 32A, so Q <= 1024M + 64A
6. specialize to (y, rho) = (0, 1): both bounds on B_{1/2}(0) with constant 1024M + 64A

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Submission.lean`
- `rg -n '^def HolderOnWith|^def HolderWith' and rg -n '^(theorem|lemma|protected theorem|protected lemma) (HolderOnWith|HolderWith)?\.?(comp|smul|dist_le|mono)' <snapshot>/mathlib/Mathlib/Topology/MetricSpace/Holder.lean`
- `rg -il 'absorption|absorb' <snapshot>/mathlib/Mathlib <snapshot>/project`
- `rg -n -i 'holder|hölder|campanato|schauder' <snapshot>/project (*.lean)`
- `rg -l -i 'interior estimate|C\^\{1,\s*α\}|schauder estimate|blow-?up' <snapshot>/mathlib/Mathlib`
- `rg -n '^theorem le_csSup |^theorem csSup_le |le_csSup_of_le|theorem csSup_le' <snapshot>/mathlib/Mathlib/Order/ConditionallyCompleteLattice/Basic.lean`
- `rg -n '^theorem (div_rpow|mul_rpow|rpow_add|one_rpow|zero_rpow|rpow_pos_of_pos|rpow_nonneg|rpow_le_rpow|rpow_le_one|one_le_rpow|rpow_le_rpow_of_exponent_le|inv_rpow|rpow_two) ' <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`
- `rg -n "theorem ball_subset_ball'|theorem mem_ball_self" <snapshot>/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean; grep 'add_sub_cancel|mul_div_cancel' <snapshot>/mathlib/Mathlib/Algebra/Group/Basic.lean`
- `python3 gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch05.main_theorem') to obtain the replayed child scope; python3 scan of dag.json for collisions of the 4 proposed lean_names and for the sibling statuses/frozen types`
- `lake env lean Checks/AllChallenges.lean, Checks/Assembly.lean, Checks/Proof_<key>.lean for the 4 keys; in a scratch Submission copy with the children appended: lake build GMT.Ch05.Submission, then Checks/Sol_<key>.lean, Checks/Chal_<key>.lean, Checks/Sol_parent.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Holder.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Order/ConditionallyCompleteLattice/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Algebra/Group/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Order/Lattice.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Tactic/Linarith/Frontend.lean`

Pins: the snapshot fixes project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace Submission.lean is byte-identical to the snapshot Contract.lean.

No relevant library result exists at the pin, so the children must be proved:
- 'absorption|absorb' matches only algebraic and lattice absorption laws (e.g. Order/Lattice.lean). There is no analytic absorption lemma.
- 'interior estimate|schauder estimate|blow-up' matches only tactic documentation (e.g. 'exponential blowup' in Tactic/Linarith/Frontend.lean).
- The project's Hoelder matches are only the contract definitions IsHolderCkα and IsLocallyHolderCkα (Contract.lean:84, 92).
- Mathlib's HolderOnWith (Topology/MetricSpace/Holder.lean:57) uses ℝ≥0 constants and edist, and its comp (line 105) multiplies exponents. It cannot express rho^{1+alpha}-weighted quotients with real constants, so the children state explicit inequalities in the style of the frozen parent.

Mathlib lemmas used in the verified child proofs:
- le_csSup and csSup_le (ConditionallyCompleteLattice/Basic.lean:197, 201).
- Real.rpow_pos_of_pos, zero_rpow, one_rpow, rpow_nonneg, rpow_add, rpow_two, mul_rpow, div_rpow, rpow_le_rpow, rpow_le_rpow_of_exponent_le, rpow_le_one, one_le_rpow (Pow/Real.lean, lines 116-677).
- Metric.ball_subset_ball' and mem_ball_self (Pseudo/Defs.lean:537, 379).
- add_sub_cancel, the to_additive form of mul_div_cancel (Group/Basic.lean:962).

The four proposed lean_names do not occur in dag.json (486 nodes at check time).

Lean checks on scratch builds at the pin:
1. All four child types and the frozen parent type elaborate in the comparator's replayed scope.
2. The frozen parent type is proved with the four child types and the three sibling types as hypotheses. Axioms: propext, Classical.choice, Quot.sound.
3. Each child is proved outright (absorption from holder_improvement). Each closes its generated NodeSolution target by `exact Submission.X` with the same three axioms.
4. Instance checks: (ρ • Φ u) P = ρ * Φ u P holds by rfl, and ‖T‖ on L(R^n,R^l) is the operator norm. smul_sub on L(R^n,R^l) needs `set_option maxSynthPendingDepth 3`.
