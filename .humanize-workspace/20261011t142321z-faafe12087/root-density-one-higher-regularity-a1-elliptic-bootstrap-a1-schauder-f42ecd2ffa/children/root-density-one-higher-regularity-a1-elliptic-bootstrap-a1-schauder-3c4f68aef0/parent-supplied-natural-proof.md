# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.unit_ball_estimate-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.unit_ball_estimate-a1.rescaled_structure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof ("We check its hypotheses"), for the rescaled data at(z) := a(y0 + rho z), Phit(z) := rho Phi(y0 + rho z), wt(z) := w(y0 + rho z) on B_1(0), where (y0, rho) is admissible (rho > 0, |y0| + rho <= 1).
1. Since |y0| >= 0 and |y0| + rho <= 1, we have 0 < rho <= 1. Hence 0 <= rho^alpha <= 1 (rpow_le_one, using alpha >= 0) and rho * rho^alpha <= 1.
2. For z in B_1(0): |y0 + rho z| <= |y0| + rho |z| < |y0| + rho <= 1, so y0 + rho z is in B_1(0).
3. For all z, z' in R^n: (y0 + rho z) - (y0 + rho z') = rho (z - z'), so |(y0 + rho z) - (y0 + rho z')|^alpha = (rho |z - z'|)^alpha = rho^alpha |z - z'|^alpha (mul_rpow; both factors are >= 0).
4. (i), (ii), (v): apply (H1), (H2), (H5) at the point y0 + rho z, which lies in B_1(0) by step 2.
5. (iii): by (H3) at the points y0 + rho z, y0 + rho z' of B_1(0) and by step 3, the left side is at most M rho^alpha |z - z'|^alpha ||P|| ||Q|| = rho^alpha X with X := M |z - z'|^alpha ||P|| ||Q||. Since M >= 0, X >= 0, and since rho^alpha <= 1 (step 1), rho^alpha X <= X.
6. (iv): (rho Phi(u))[P] = rho * Phi(u)[P] for every u, so the left side equals |rho (Phi(y0 + rho z)[P] - Phi(y0 + rho z')[P])| = rho |Phi(y0 + rho z)[P] - Phi(y0 + rho z')[P]|. By (H4) at the points of step 2 and by step 3, this is at most rho M rho^alpha |z - z'|^alpha ||P|| = (rho rho^alpha) Y with Y := M |z - z'|^alpha ||P|| >= 0. Since rho rho^alpha <= 1 (step 1), it is at most Y. QED
Lean proof checked at the pin (Lean 4.35.0-rc3, Mathlib 25730c7c; stated inside `namespace GMT.Ch05` with the contract's `open`s, appended to a scratch copy of the submission; the generated NodeSolution target closes by `exact Submission.dohr_eb_sch_ube_rescaled_structure`; #print axioms: propext, Classical.choice, Quot.sound):
set_option maxSynthPendingDepth 3 in
theorem Submission.dohr_eb_sch_ube_rescaled_structure : ∀ (n ℓ : ℕ) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (w : Rn n → Rn ℓ) (y₀ : Rn n) (ρ α lam M : ℝ), 0 < ρ → ‖y₀‖ + ρ ≤ 1 → 0 ≤ α → 0 ≤ M → (∀ x ∈ ball (0 : Rn n) 1, ∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ a x P P) → (∀ x ∈ ball (0 : Rn n) 1, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q| ≤ M * ‖P‖ * ‖Q‖) → (∀ x ∈ ball (0 : Rn n) 1, ∀ y ∈ ball (0 : Rn n) 1, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q - a y P Q| ≤ M * ‖x - y‖ ^ α * ‖P‖ * ‖Q‖) → (∀ x ∈ ball (0 : Rn n) 1, ∀ y ∈ ball (0 : Rn n) 1, ∀ P : Rn n →L[ℝ] Rn ℓ, |Φ x P - Φ y P| ≤ M * ‖x - y‖ ^ α * ‖P‖) → (∀ x ∈ ball (0 : Rn n) 1, ‖w x‖ ≤ M) → (∀ z ∈ ball (0 : Rn n) 1, ∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ a (y₀ + ρ • z) P P) ∧ (∀ z ∈ ball (0 : Rn n) 1, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a (y₀ + ρ • z) P Q| ≤ M * ‖P‖ * ‖Q‖) ∧ (∀ z ∈ ball (0 : Rn n) 1, ∀ z' ∈ ball (0 : Rn n) 1, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a (y₀ + ρ • z) P Q - a (y₀ + ρ • z') P Q| ≤ M * ‖z - z'‖ ^ α * ‖P‖ * ‖Q‖) ∧ (∀ z ∈ ball (0 : Rn n) 1, ∀ z' ∈ ball (0 : Rn n) 1, ∀ P : Rn n →L[ℝ] Rn ℓ, |(ρ • Φ (y₀ + ρ • z)) P - (ρ • Φ (y₀ + ρ • z')) P| ≤ M * ‖z - z'‖ ^ α * ‖P‖) ∧ ∀ z ∈ ball (0 : Rn n) 1, ‖w (y₀ + ρ • z)‖ ≤ M := by
  intro n ℓ a Φ w y₀ ρ α lam M hρ hyρ hα hM h1 h2 h3 h4 h5
  have hρ1 : ρ ≤ 1 := by linarith [norm_nonneg y₀]
  have hmap : ∀ z ∈ ball (0 : Rn n) 1, y₀ + ρ • z ∈ ball (0 : Rn n) 1 := by
    intro z hz
    rw [mem_ball_zero_iff] at hz ⊢
    calc ‖y₀ + ρ • z‖ ≤ ‖y₀‖ + ‖ρ • z‖ := norm_add_le _ _
      _ = ‖y₀‖ + ρ * ‖z‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
      _ < ‖y₀‖ + ρ * 1 := by gcongr
      _ ≤ 1 := by linarith
  have hdiff : ∀ z z' : Rn n, ‖(y₀ + ρ • z) - (y₀ + ρ • z')‖ ^ α = ρ ^ α * ‖z - z'‖ ^ α := by
    intro z z'
    rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hρ,
      Real.mul_rpow hρ.le (norm_nonneg _)]
  have hρα : ρ ^ α ≤ 1 := Real.rpow_le_one hρ.le hρ1 hα
  have hρα0 : 0 ≤ ρ ^ α := Real.rpow_nonneg hρ.le α
  refine ⟨fun z hz P => h1 _ (hmap z hz) P, fun z hz P Q => h2 _ (hmap z hz) P Q, ?_, ?_,
    fun z hz => h5 _ (hmap z hz)⟩
  · intro z hz z' hz' P Q
    have h := h3 _ (hmap z hz) _ (hmap z' hz') P Q
    rw [hdiff] at h
    have hX : 0 ≤ M * ‖z - z'‖ ^ α * ‖P‖ * ‖Q‖ :=
      mul_nonneg (mul_nonneg (mul_nonneg hM (Real.rpow_nonneg (norm_nonneg _) _))
        (norm_nonneg _)) (norm_nonneg _)
    calc |a (y₀ + ρ • z) P Q - a (y₀ + ρ • z') P Q|
        ≤ M * (ρ ^ α * ‖z - z'‖ ^ α) * ‖P‖ * ‖Q‖ := h
      _ = ρ ^ α * (M * ‖z - z'‖ ^ α * ‖P‖ * ‖Q‖) := by ring
      _ ≤ 1 * (M * ‖z - z'‖ ^ α * ‖P‖ * ‖Q‖) := mul_le_mul_of_nonneg_right hρα hX
      _ = M * ‖z - z'‖ ^ α * ‖P‖ * ‖Q‖ := one_mul _
  · intro z hz z' hz' P
    have h := h4 _ (hmap z hz) _ (hmap z' hz') P
    rw [hdiff] at h
    have hX : 0 ≤ M * ‖z - z'‖ ^ α * ‖P‖ :=
      mul_nonneg (mul_nonneg hM (Real.rpow_nonneg (norm_nonneg _) _)) (norm_nonneg _)
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [← mul_sub, abs_mul, abs_of_pos hρ]
    have hρρ : ρ * ρ ^ α ≤ 1 := by nlinarith
    calc ρ * |Φ (y₀ + ρ • z) P - Φ (y₀ + ρ • z') P|
        ≤ ρ * (M * (ρ ^ α * ‖z - z'‖ ^ α) * ‖P‖) := by gcongr
      _ = (ρ * ρ ^ α) * (M * ‖z - z'‖ ^ α * ‖P‖) := by ring
      _ ≤ 1 * (M * ‖z - z'‖ ^ α * ‖P‖) := mul_le_mul_of_nonneg_right hρρ hX
      _ = M * ‖z - z'‖ ^ α * ‖P‖ := one_mul _

## Key steps

1. 0 < rho <= 1, hence rho^alpha <= 1 and rho rho^alpha <= 1
2. y0 + rho z lies in B_1(0) for z in B_1(0)
3. |(y0 + rho z) - (y0 + rho z')|^alpha = rho^alpha |z - z'|^alpha
4. (i), (ii), (v) pointwise from (H1), (H2), (H5); (iii) and (iv) from (H3), (H4) after discarding the factors rho^alpha <= 1 and rho rho^alpha <= 1, using M >= 0

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
