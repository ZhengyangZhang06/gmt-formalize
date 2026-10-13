# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.unit_ball_estimate-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.unit_ball_estimate-a1.holder_improvement-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3, 4 and 5 of the parent proof, with the supremum Q replaced by an arbitrary constant Q >= 0 satisfying (P1), delta = 1/16, and A in the role of 2 C_delta M. The parent's H(rho) corresponds to H / rho^{1+alpha} with H := Q/4 + 16 A (the parent's bound rho^{1+alpha} H(rho) <= 4 delta Q + 32 C_delta M).
Fix an admissible (y, rho) and put H := Q/4 + 16 A >= 0.
1. Position of points. For x in B_{rho/2}(y): |x| <= |y| + |x - y| < |y| + rho/2, so |x| + rho/2 < |y| + rho <= 1. Hence (x, rho/2) and (x, rho/4) are admissible and |x| + rho/8 <= 1.
2. Numerical facts. Since 1 <= 1 + alpha <= 2 and the bases are >= 1: 2^{1+alpha} <= 2^2 = 4 and 4^{1+alpha} <= 4^2 = 16. Since 0 < alpha <= 1: 16^alpha >= 1, 8^alpha <= 8^1 = 8 and 8^alpha <= 16^alpha. Also rho^{1+alpha} = rho rho^alpha, and (rho/m)^beta = rho^beta / m^beta for m > 0 (div_rpow).
3. Hoelder bound on small balls (parent 6b). Claim: for x in B_{rho/2}(y) and z, z' in B_{rho/8}(x): rho^{1+alpha} ||g(z) - g(z')|| <= H |z - z'|^alpha.
 Proof. By (P1) for the admissible pair (x, rho/2) (whose half ball is B_{rho/4}(x)), for u, u' in B_{rho/4}(x): (rho/2)^{1+alpha} ||g(u) - g(u')|| <= Q |u - u'|^alpha, i.e. ||g(u) - g(u')|| <= K' |u - u'|^alpha with K' := Q / (rho/2)^{1+alpha}. Apply (P2) to the admissible pair (x, rho/4) (whose half ball is B_{rho/8}(x)) and this K': for z, z' in B_{rho/8}(x), (rho/4)^{1+alpha} ||g(z) - g(z')|| <= ((1/16) (rho/4)^{1+alpha} K' + A) |z - z'|^alpha. By step 2, (rho/4)^{1+alpha} = rho^{1+alpha} / 4^{1+alpha} and (rho/4)^{1+alpha} K' = Q 2^{1+alpha} / 4^{1+alpha}. Multiplying by 4^{1+alpha} > 0 gives rho^{1+alpha} ||g(z) - g(z')|| <= (Q 2^{1+alpha}/16 + A 4^{1+alpha}) |z - z'|^alpha <= (Q/4 + 16 A) |z - z'|^alpha, using Q >= 0, A >= 0, |z - z'|^alpha >= 0 and step 2.
4. Fine sup bound (parent 6c). Claim: for x in B_{rho/2}(y): rho ||g(x)|| <= 32 M + H / 16^alpha.
 Proof. By step 3, ||g(z) - g(z')|| <= K |z - z'|^alpha for z, z' in B_{rho/8}(x), with K := H / rho^{1+alpha} >= 0. Apply (P3) with r := rho/8 and t := rho/16 (|x| + rho/8 <= 1 by step 1, and 0 < t < r): ||g(x)|| <= 2M/(rho/16) + (rho/16)^alpha H / rho^{1+alpha} = 32 M / rho + (rho^alpha / 16^alpha) H / (rho rho^alpha) = (32 M + H / 16^alpha) / rho. Multiply by rho > 0.
5. Conclusion (a). Since 16^alpha >= 1 and H >= 0, H / 16^alpha <= H; by step 4, rho ||g(x)|| <= 32 M + H = 32 M + Q/4 + 16 A for x in B_{rho/2}(y).
6. Conclusion (b) (parent 6d). Let x, x' be in B_{rho/2}(y) and d := |x - x'|^alpha >= 0. Note H <= Q/2 + 512 M + 32 A since Q, M, A >= 0.
 Case |x - x'| < rho/8. Then x and x' lie in B_{rho/8}(x), and step 3 gives rho^{1+alpha} ||g(x) - g(x')|| <= H d <= (Q/2 + 512 M + 32 A) d.
 Case |x - x'| >= rho/8. By monotonicity of s -> s^alpha on [0, infinity) (alpha >= 0), d >= (rho/8)^alpha = rho^alpha / 8^alpha, so rho^alpha <= 8^alpha d <= 8 d and rho^alpha / 16^alpha <= 8^alpha d / 16^alpha <= d (step 2). By the triangle inequality and step 4 at x and at x': rho^{1+alpha} ||g(x) - g(x')|| = rho^alpha (rho ||g(x) - g(x')||) <= rho^alpha (rho ||g(x)|| + rho ||g(x')||) <= rho^alpha * 2 (32 M + H / 16^alpha) = 64 M rho^alpha + 2 H (rho^alpha / 16^alpha) <= 64 M * 8 d + 2 H d = (Q/2 + 512 M + 32 A) d, using M >= 0 and H >= 0.
In both cases (b) holds. QED
Lean proof checked at the pin (Lean 4.35.0-rc3, Mathlib 25730c7c; stated inside `namespace GMT.Ch05` with the contract's `open`s, appended to a scratch copy of the submission; the generated NodeSolution target closes by `exact Submission.dohr_eb_sch_ube_holder_improvement`; #print axioms: propext, Classical.choice, Quot.sound):
set_option maxSynthPendingDepth 3 in
theorem Submission.dohr_eb_sch_ube_holder_improvement : ∀ (n ℓ : ℕ) (g : Rn n → (Rn n →L[ℝ] Rn ℓ)) (α M A Q : ℝ), 0 < α → α ≤ 1 → 0 ≤ M → 0 ≤ A → 0 ≤ Q → (∀ (y : Rn n) (ρ : ℝ), 0 < ρ → ‖y‖ + ρ ≤ 1 → ∀ x ∈ ball y (ρ / 2), ∀ x' ∈ ball y (ρ / 2), ρ ^ (1 + α) * ‖g x - g x'‖ ≤ Q * ‖x - x'‖ ^ α) → (∀ (y : Rn n) (ρ K : ℝ), 0 < ρ → ‖y‖ + ρ ≤ 1 → (∀ x ∈ ball y ρ, ∀ x' ∈ ball y ρ, ‖g x - g x'‖ ≤ K * ‖x - x'‖ ^ α) → ∀ x ∈ ball y (ρ / 2), ∀ x' ∈ ball y (ρ / 2), ρ ^ (1 + α) * ‖g x - g x'‖ ≤ (1 / 16 * ρ ^ (1 + α) * K + A) * ‖x - x'‖ ^ α) → (∀ (x : Rn n) (r t K : ℝ), ‖x‖ + r ≤ 1 → 0 ≤ K → 0 < t → t < r → (∀ z ∈ ball x r, ∀ z' ∈ ball x r, ‖g z - g z'‖ ≤ K * ‖z - z'‖ ^ α) → ‖g x‖ ≤ 2 * M / t + t ^ α * K) → ∀ (y : Rn n) (ρ : ℝ), 0 < ρ → ‖y‖ + ρ ≤ 1 → (∀ x ∈ ball y (ρ / 2), ρ * ‖g x‖ ≤ 32 * M + Q / 4 + 16 * A) ∧ ∀ x ∈ ball y (ρ / 2), ∀ x' ∈ ball y (ρ / 2), ρ ^ (1 + α) * ‖g x - g x'‖ ≤ (Q / 2 + 512 * M + 32 * A) * ‖x - x'‖ ^ α := by
  intro n ℓ g α M A Q hα0 hα1 hM hA hQ0 hP1 hP2 hP3 y ρ hρ hyρ
  have hxnorm : ∀ x ∈ ball y (ρ / 2), ‖x‖ + ρ / 2 < 1 := by
    intro x hx
    rw [mem_ball, dist_eq_norm] at hx
    have : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
      calc ‖x‖ = ‖y + (x - y)‖ := by rw [add_sub_cancel]
        _ ≤ ‖y‖ + ‖x - y‖ := norm_add_le _ _
    linarith
  have hR : 0 < ρ ^ (1 + α) := Real.rpow_pos_of_pos hρ _
  have hsplit : ρ ^ (1 + α) = ρ * ρ ^ α := by rw [Real.rpow_add hρ, Real.rpow_one]
  have hρα : 0 < ρ ^ α := Real.rpow_pos_of_pos hρ α
  have p2pos : (0:ℝ) < 2 ^ (1 + α) := by positivity
  have p4pos : (0:ℝ) < 4 ^ (1 + α) := by positivity
  have p2ne : (2:ℝ) ^ (1 + α) ≠ 0 := p2pos.ne'
  have p4ne : (4:ℝ) ^ (1 + α) ≠ 0 := p4pos.ne'
  have hRne : ρ ^ (1 + α) ≠ 0 := hR.ne'
  have p2le : (2:ℝ) ^ (1 + α) ≤ 4 := by
    calc (2:ℝ) ^ (1 + α) ≤ 2 ^ (2:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 4 := by rw [Real.rpow_two]; norm_num
  have p4le : (4:ℝ) ^ (1 + α) ≤ 16 := by
    calc (4:ℝ) ^ (1 + α) ≤ 4 ^ (2:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 16 := by rw [Real.rpow_two]; norm_num
  have hH0 : 0 ≤ Q / 4 + 16 * A := by linarith
  -- Step 3: Hoelder bound with constant (Q/4 + 16 A) / ρ^(1+α) on ball x (ρ/8)
  have hsmall : ∀ x ∈ ball y (ρ / 2), ∀ z ∈ ball x (ρ / 8), ∀ z' ∈ ball x (ρ / 8),
      ρ ^ (1 + α) * ‖g z - g z'‖ ≤ (Q / 4 + 16 * A) * ‖z - z'‖ ^ α := by
    intro x hx z hz z' hz'
    have hx1 := hxnorm x hx
    have hρ2 : 0 < ρ / 2 := by positivity
    have hρ4 : 0 < ρ / 4 := by positivity
    have e2 : (ρ / 2) ^ (1 + α) = ρ ^ (1 + α) / 2 ^ (1 + α) :=
      Real.div_rpow hρ.le (by norm_num) _
    have e4 : (ρ / 4) ^ (1 + α) = ρ ^ (1 + α) / 4 ^ (1 + α) :=
      Real.div_rpow hρ.le (by norm_num) _
    have hpos2 : 0 < (ρ / 2) ^ (1 + α) := Real.rpow_pos_of_pos hρ2 _
    have hHolK : ∀ u ∈ ball x (ρ / 4), ∀ u' ∈ ball x (ρ / 4),
        ‖g u - g u'‖ ≤ Q / (ρ / 2) ^ (1 + α) * ‖u - u'‖ ^ α := by
      intro u hu u' hu'
      have e : ρ / 2 / 2 = ρ / 4 := by ring
      have h := hP1 x (ρ / 2) hρ2 hx1.le u (by rwa [e]) u' (by rwa [e])
      rw [div_mul_eq_mul_div, le_div_iff₀ hpos2]
      linarith
    have hx4 : ‖x‖ + ρ / 4 ≤ 1 := by linarith
    have e8 : ρ / 4 / 2 = ρ / 8 := by ring
    have h1 := hP2 x (ρ / 4) (Q / (ρ / 2) ^ (1 + α)) hρ4 hx4 hHolK z (by rwa [e8])
      z' (by rwa [e8])
    rw [e4, e2] at h1
    have hd : 0 ≤ ‖z - z'‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
    have key : 1 / 16 * (ρ ^ (1 + α) / 4 ^ (1 + α)) * (Q / (ρ ^ (1 + α) / 2 ^ (1 + α)))
        = Q * 2 ^ (1 + α) / (16 * 4 ^ (1 + α)) := by
      field_simp
    rw [key] at h1
    have h2 : ρ ^ (1 + α) * ‖g z - g z'‖
        ≤ (Q * 2 ^ (1 + α) / 16 + A * 4 ^ (1 + α)) * ‖z - z'‖ ^ α := by
      have h3 := mul_le_mul_of_nonneg_left h1 p4pos.le
      calc ρ ^ (1 + α) * ‖g z - g z'‖
          = 4 ^ (1 + α) * (ρ ^ (1 + α) / 4 ^ (1 + α) * ‖g z - g z'‖) := by
            field_simp
        _ ≤ 4 ^ (1 + α) * ((Q * 2 ^ (1 + α) / (16 * 4 ^ (1 + α)) + A) * ‖z - z'‖ ^ α) := h3
        _ = (Q * 2 ^ (1 + α) / 16 + A * 4 ^ (1 + α)) * ‖z - z'‖ ^ α := by
            field_simp
    calc ρ ^ (1 + α) * ‖g z - g z'‖
        ≤ (Q * 2 ^ (1 + α) / 16 + A * 4 ^ (1 + α)) * ‖z - z'‖ ^ α := h2
      _ ≤ (Q / 4 + 16 * A) * ‖z - z'‖ ^ α := by
          apply mul_le_mul_of_nonneg_right _ hd
          have q1 := mul_le_mul_of_nonneg_left p2le hQ0
          have q2 := mul_le_mul_of_nonneg_left p4le hA
          linarith
  -- Step 4: sup bound
  have hsupfine : ∀ x ∈ ball y (ρ / 2), ρ * ‖g x‖ ≤ 32 * M + (Q / 4 + 16 * A) / 16 ^ α := by
    intro x hx
    have hx1 := hxnorm x hx
    have hK0 : 0 ≤ (Q / 4 + 16 * A) / ρ ^ (1 + α) := div_nonneg hH0 hR.le
    have hHol8 : ∀ z ∈ ball x (ρ / 8), ∀ z' ∈ ball x (ρ / 8),
        ‖g z - g z'‖ ≤ (Q / 4 + 16 * A) / ρ ^ (1 + α) * ‖z - z'‖ ^ α := by
      intro z hz z' hz'
      have h := hsmall x hx z hz z' hz'
      rw [div_mul_eq_mul_div, le_div_iff₀ hR]
      linarith
    have h := hP3 x (ρ / 8) (ρ / 16) ((Q / 4 + 16 * A) / ρ ^ (1 + α)) (by linarith) hK0
      (by positivity) (by linarith) hHol8
    have e16 : (ρ / 16) ^ α = ρ ^ α / 16 ^ α := Real.div_rpow hρ.le (by norm_num) _
    rw [e16, hsplit] at h
    have p16 : (0:ℝ) < 16 ^ α := by positivity
    have p16ne : (16:ℝ) ^ α ≠ 0 := p16.ne'
    have hραne : ρ ^ α ≠ 0 := hρα.ne'
    have hρne : ρ ≠ 0 := hρ.ne'
    have hid : ρ * (2 * M / (ρ / 16) + ρ ^ α / 16 ^ α * ((Q / 4 + 16 * A) / (ρ * ρ ^ α)))
        = 32 * M + (Q / 4 + 16 * A) / 16 ^ α := by
      field_simp
      ring
    calc ρ * ‖g x‖
        ≤ ρ * (2 * M / (ρ / 16) + ρ ^ α / 16 ^ α * ((Q / 4 + 16 * A) / (ρ * ρ ^ α))) :=
          mul_le_mul_of_nonneg_left h hρ.le
      _ = 32 * M + (Q / 4 + 16 * A) / 16 ^ α := hid
  have h16 : (1:ℝ) ≤ 16 ^ α := Real.one_le_rpow (by norm_num) hα0.le
  refine ⟨?_, ?_⟩
  · intro x hx
    have h := hsupfine x hx
    have : (Q / 4 + 16 * A) / 16 ^ α ≤ Q / 4 + 16 * A := div_le_self hH0 h16
    linarith
  · intro x hx x' hx'
    have hd : 0 ≤ ‖x - x'‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
    by_cases hcase : ‖x - x'‖ < ρ / 8
    · have hxin : x ∈ ball x (ρ / 8) := mem_ball_self (by positivity)
      have hx'in : x' ∈ ball x (ρ / 8) := by
        rw [mem_ball, dist_comm, dist_eq_norm]; exact hcase
      have h := hsmall x hx x hxin x' hx'in
      calc ρ ^ (1 + α) * ‖g x - g x'‖ ≤ (Q / 4 + 16 * A) * ‖x - x'‖ ^ α := h
        _ ≤ (Q / 2 + 512 * M + 32 * A) * ‖x - x'‖ ^ α := by
          apply mul_le_mul_of_nonneg_right _ hd; linarith
    · push Not at hcase
      have hdl : (ρ / 8) ^ α ≤ ‖x - x'‖ ^ α := Real.rpow_le_rpow (by positivity) hcase hα0.le
      have e8 : (ρ / 8) ^ α = ρ ^ α / 8 ^ α := Real.div_rpow hρ.le (by norm_num) _
      have p8 : (0:ℝ) < 8 ^ α := by positivity
      have p16 : (0:ℝ) < 16 ^ α := by positivity
      have hρα8 : ρ ^ α ≤ 8 ^ α * ‖x - x'‖ ^ α := by
        rw [e8, div_le_iff₀ p8] at hdl; linarith
      have h8 : (8:ℝ) ^ α ≤ 8 := by
        calc (8:ℝ) ^ α ≤ 8 ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1
          _ = 8 := Real.rpow_one 8
      have h816 : (8:ℝ) ^ α ≤ 16 ^ α := Real.rpow_le_rpow (by norm_num) (by norm_num) hα0.le
      have hA1 : ρ ^ α ≤ 8 * ‖x - x'‖ ^ α := by
        have := mul_le_mul_of_nonneg_right h8 hd
        linarith
      have hA2 : ρ ^ α / 16 ^ α ≤ ‖x - x'‖ ^ α := by
        have := mul_le_mul_of_nonneg_right h816 hd
        rw [div_le_iff₀ p16]
        linarith
      have hsx := hsupfine x hx
      have hsx' := hsupfine x' hx'
      have htri : ‖g x - g x'‖ ≤ ‖g x‖ + ‖g x'‖ := norm_sub_le _ _
      calc ρ ^ (1 + α) * ‖g x - g x'‖ = ρ ^ α * (ρ * ‖g x - g x'‖) := by rw [hsplit]; ring
        _ ≤ ρ ^ α * (ρ * ‖g x‖ + ρ * ‖g x'‖) := by
            apply mul_le_mul_of_nonneg_left _ hρα.le
            rw [← mul_add]
            exact mul_le_mul_of_nonneg_left htri hρ.le
        _ ≤ ρ ^ α * (2 * (32 * M + (Q / 4 + 16 * A) / 16 ^ α)) := by
            apply mul_le_mul_of_nonneg_left _ hρα.le
            linarith
        _ = 64 * M * ρ ^ α + 2 * (Q / 4 + 16 * A) * (ρ ^ α / 16 ^ α) := by ring
        _ ≤ 64 * M * (8 * ‖x - x'‖ ^ α) + 2 * (Q / 4 + 16 * A) * ‖x - x'‖ ^ α :=
            add_le_add (mul_le_mul_of_nonneg_left hA1 (by linarith))
              (mul_le_mul_of_nonneg_left hA2 (by linarith))
        _ = (Q / 2 + 512 * M + 32 * A) * ‖x - x'‖ ^ α := by ring

## Key steps

1. points x of B_{rho/2}(y) satisfy |x| + rho/2 < 1, so (x, rho/2) and (x, rho/4) are admissible and |x| + rho/8 <= 1
2. (P1) at (x, rho/2) gives the Hoelder constant K' = Q/(rho/2)^{1+alpha} on B_{rho/4}(x)
3. (P2) at (x, rho/4) with K' gives rho^{1+alpha} ||g(z) - g(z')|| <= (Q/4 + 16A) |z - z'|^alpha on B_{rho/8}(x), using 2^{1+alpha} <= 4 and 4^{1+alpha} <= 16
4. (P3) with r = rho/8, t = rho/16 gives rho ||g(x)|| <= 32M + (Q/4 + 16A)/16^alpha, hence (a)
5. (b) by cases |x - x'| < rho/8 (small-ball bound) and |x - x'| >= rho/8 (sup bound, rho^alpha <= 8 |x - x'|^alpha, rho^alpha/16^alpha <= |x - x'|^alpha)

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
