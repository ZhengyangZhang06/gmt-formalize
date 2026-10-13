# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.density_bounds-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.density_bounds-a1.sharp_ratio-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Steps 1–2 (Simon Ch. 5, 2.4, chapter-05.txt lines 278–288). Simon bounds (ω_n(1 − δ)ⁿρⁿ)^{−1}μ(B_{(1−δ)ρ}(y)) ≤ 1 + Cδ 'because B_{(1−δ)ρ}(y) ⊆ B_ρ(0)'. Here the parent's radii 4δρ and (1 − 4δ)ρ are used and the constant is exact. The monotonicity inequality is Simon Ch. 4, 4.7–4.8 (chapter-04.txt lines 536–546) and is a hypothesis of this lemma. In the parent it is the first conjunct (M1) of Submission.dorag_monotonicity_density with its nonnegative integral term dropped.

Notation: for real a write a⁺ := ENNReal.ofReal a; ω := unitBallVolume n ∈ [0, ∞]; B_t(y) is the closed ball; all products are in [0, ∞]; K := e^δ(1 + δ)/(1 − 4δ)ⁿ ∈ ℝ. ENNReal.ofReal_mul: (ab)⁺ = a⁺b⁺ for a ≥ 0.

1. Put t' := (1 − 4δ)ρ. From 0 ≤ δ ≤ 1/8 we get 1/2 ≤ 1 − 4δ ≤ 1, so 0 < t' ≤ ρ.
2. Ball inclusion. Let y ∈ B_{4δρ}(z), i.e. |y − z| ≤ 4δρ. For p ∈ B_{t'}(y): |p − z| ≤ |p − y| + |y − z| ≤ (1 − 4δ)ρ + 4δρ = ρ. Hence B_{t'}(y) ⊆ B_ρ(z) ⊆ W.
3. Normalized mass at the radius t'. Since κ ≥ 0 and t' ≤ ρ, κt' ≤ κρ ≤ δ. So e^{κt'} ≤ e^δ and, dividing by t'ⁿ > 0, (e^{κt'}/t'ⁿ)⁺ ≤ (e^δ/t'ⁿ)⁺. By Step 2 and monotonicity of μ, μ(B_{t'}(y)) ≤ μ(B_ρ(z)) ≤ (1 + δ)⁺·ω·(ρⁿ)⁺. Therefore
 (e^{κt'}/t'ⁿ)⁺·μ(B_{t'}(y)) ≤ (e^δ/t'ⁿ)⁺·(1 + δ)⁺·ω·(ρⁿ)⁺ = (e^δ(1 + δ)ρⁿ/t'ⁿ)⁺·ω = K⁺·ω,
 because ρⁿ/t'ⁿ = 1/(1 − 4δ)ⁿ.
4. Conclusion (i). Let 0 < t ≤ t'. If t < t', apply the monotonicity hypothesis with centre y and radii t < t' (allowed since B_{t'}(y) ⊆ W by Step 2): (e^{κt}/tⁿ)⁺μ(B_t(y)) ≤ (e^{κt'}/t'ⁿ)⁺μ(B_{t'}(y)). If t = t', the two sides coincide. Together with Step 3: (e^{κt}/tⁿ)⁺·μ(B_t(y)) ≤ K⁺·ω.
5. Conclusion (ii).
 (a) κt ≥ 0 gives e^{κt} ≥ 1, hence (tⁿ/e^{κt})⁺ ≤ (tⁿ)⁺.
 (b) Since tⁿ > 0, (tⁿ/e^{κt})⁺·(e^{κt}/tⁿ)⁺ = 1⁺ = 1.
 (c) By Step 4: μ(B_t(y)) = (tⁿ/e^{κt})⁺·[(e^{κt}/tⁿ)⁺·μ(B_t(y))] ≤ (tⁿ/e^{κt})⁺·K⁺·ω ≤ (tⁿ)⁺·K⁺·ω = K⁺·ω·(tⁿ)⁺.
6. Steps 4 and 5 are the two conjuncts, for every y ∈ B_{4δρ}(z) and every t with 0 < t ≤ (1 − 4δ)ρ. ∎

Appendix: Lean proof of exactly this statement, following Steps 1–5. It was kernel-checked (lean-4.35.0-rc3, Mathlib 25730c7c, after import GMT.Ch07.Submission in the contract scope); #print axioms gives propext, Classical.choice, Quot.sound.
theorem Submission.dorag_dbs_sharp_mass_ratio : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (W : Set (Euclid P)) (κ δ ρ : ℝ) (z : Euclid P), 0 < ρ → 0 ≤ δ → δ ≤ 1 / 8 → 0 ≤ κ → κ * ρ ≤ δ → closedBall z ρ ⊆ W → μ (closedBall z ρ) ≤ ENNReal.ofReal (1 + δ) * unitBallVolume n * ENNReal.ofReal (ρ ^ n) → (∀ (y : Euclid P) (s t : ℝ), 0 < s → s < t → closedBall y t ⊆ W → ENNReal.ofReal (Real.exp (κ * s) / s ^ n) * μ (closedBall y s) ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * μ (closedBall y t)) → ∀ y ∈ closedBall z (4 * δ * ρ), ∀ t : ℝ, 0 < t → t ≤ (1 - 4 * δ) * ρ → ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * μ (closedBall y t) ≤ ENNReal.ofReal (Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n) * unitBallVolume n ∧ μ (closedBall y t) ≤ ENNReal.ofReal (Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n) * unitBallVolume n * ENNReal.ofReal (t ^ n) := by
  intro P n μ W κ δ ρ z hρ hδ0 hδ8 hκ hκρ hball hmass hmono y hy t ht htle
  set t' := (1 - 4 * δ) * ρ with ht'_def
  have h14 : 0 < 1 - 4 * δ := by linarith
  have ht'pos : 0 < t' := mul_pos h14 hρ
  have ht'ρ : t' ≤ ρ := by nlinarith
  have hsub : closedBall y t' ⊆ closedBall z ρ := by
    intro p hp
    rw [mem_closedBall] at hp hy ⊢
    calc dist p z ≤ dist p y + dist y z := dist_triangle p y z
      _ ≤ t' + 4 * δ * ρ := add_le_add hp hy
      _ = ρ := by rw [ht'_def]; ring
  -- step 3: normalized mass at t'
  have hstep3 : ENNReal.ofReal (Real.exp (κ * t') / t' ^ n) * μ (closedBall y t') ≤
      ENNReal.ofReal (Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n) * unitBallVolume n := by
    have ht'n : 0 < t' ^ n := pow_pos ht'pos n
    have he : Real.exp (κ * t') / t' ^ n ≤ Real.exp δ / t' ^ n := by
      apply div_le_div_of_nonneg_right _ ht'n.le
      apply Real.exp_le_exp.mpr
      calc κ * t' ≤ κ * ρ := mul_le_mul_of_nonneg_left ht'ρ hκ
        _ ≤ δ := hκρ
    calc ENNReal.ofReal (Real.exp (κ * t') / t' ^ n) * μ (closedBall y t')
        ≤ ENNReal.ofReal (Real.exp δ / t' ^ n) * μ (closedBall z ρ) := by
          gcongr
      _ ≤ ENNReal.ofReal (Real.exp δ / t' ^ n) *
            (ENNReal.ofReal (1 + δ) * unitBallVolume n * ENNReal.ofReal (ρ ^ n)) := by
          gcongr
      _ = ENNReal.ofReal (Real.exp δ / t' ^ n * (1 + δ) * ρ ^ n) * unitBallVolume n := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
          ring
      _ = ENNReal.ofReal (Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n) * unitBallVolume n := by
          congr 2
          rw [ht'_def, mul_pow]
          field_simp
  -- step 4
  have hi : ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * μ (closedBall y t) ≤
      ENNReal.ofReal (Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n) * unitBallVolume n := by
    rcases lt_or_eq_of_le htle with hlt | heq
    · exact (hmono y t t' ht hlt (hsub.trans hball)).trans hstep3
    · rw [heq]; exact hstep3
  refine ⟨hi, ?_⟩
  -- step 5
  have htn : 0 < t ^ n := pow_pos ht n
  have hexp1 : 1 ≤ Real.exp (κ * t) := Real.one_le_exp (mul_nonneg hκ ht.le)
  have hfac : ENNReal.ofReal (t ^ n / Real.exp (κ * t)) * ENNReal.ofReal (Real.exp (κ * t) / t ^ n) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    rw [show t ^ n / Real.exp (κ * t) * (Real.exp (κ * t) / t ^ n) = 1 by
      field_simp]
    simp
  have hle : ENNReal.ofReal (t ^ n / Real.exp (κ * t)) ≤ ENNReal.ofReal (t ^ n) := by
    apply ENNReal.ofReal_le_ofReal
    exact div_le_self htn.le hexp1
  calc μ (closedBall y t)
      = ENNReal.ofReal (t ^ n / Real.exp (κ * t)) *
          (ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * μ (closedBall y t)) := by
        rw [← mul_assoc, hfac, one_mul]
    _ ≤ ENNReal.ofReal (t ^ n / Real.exp (κ * t)) *
          (ENNReal.ofReal (Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n) * unitBallVolume n) := by
        gcongr
    _ ≤ ENNReal.ofReal (t ^ n) *
          (ENNReal.ofReal (Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n) * unitBallVolume n) := by
        gcongr
    _ = ENNReal.ofReal (Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n) * unitBallVolume n *
          ENNReal.ofReal (t ^ n) := by ring

## Key steps

1. t' := (1 − 4δ)ρ ∈ (0, ρ]; for y ∈ B_{4δρ}(z), B_{t'}(y) ⊆ B_ρ(z) ⊆ W by the triangle inequality.
2. κt' ≤ κρ ≤ δ and μ(B_{t'}(y)) ≤ μ(B_ρ(z)) ≤ (1 + δ)ω_nρⁿ give e^{κt'}t'^{−n}μ(B_{t'}(y)) ≤ K(δ)ω_n.
3. For t < t' the monotonicity hypothesis (radii t < t') transfers the bound to radius t; the case t = t' is immediate.
4. Since e^{κt} ≥ 1, multiplying by (tⁿe^{−κt})⁺ ≤ (tⁿ)⁺ gives μ(B_t(y)) ≤ K(δ)ω_ntⁿ.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json  (mode local-project; project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean  (both identical; HEAD b4d606d)`
- `rg -n '^def unitBallVolume|^structure IMRep|^def IMRep.measure' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean  (lines 143, 61, 88)`
- `rg -n 'dorag_dbs|dorag_standing' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project  (no match)`
- `rg -n 'theorem ae_tendsto_measure_inter_div|instance.*HasBesicovitchCovering|theorem ae_tendsto_rnDeriv' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/`
- `rg -n 'euclideanHausdorffMeasure_homothety_image|theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume|theorem Isometry.euclideanHausdorffMeasure_image' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean; rg -n 'theorem addHaar_closedBall_eq_addHaar_ball' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean; rg -n 'one_add_mul_le_pow' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order; rg -n 'theorem add_one_le_exp' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -n 'def HasApproximateTangentSpaceAt' -A 25 /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean; sed -n 123,260p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean  (blowUpMap, regular_euclideanHausdorffMeasure_restrict_submodule, planeMeasure_eq)`
- `grep -rn 'simon_theorem_3_6|measure_toOuterMeasure_isBorelRegular|simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT; sed -n 300,420p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `sed -n 25,260p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean; sed -n 25,200p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/LowerDensityTangents.lean; sed -n 25,200p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/PositiveMultiplicityScale.lean  (proof patterns only)`
- `lean Avail.lean / Avail2.lean after import GMT.Ch07.Submission: #check Besicovitch.ae_tendsto_measure_inter_div (ok), Poincare.SimonGMT.Chapter01.simon_theorem_3_6 / Chapter04.planeMeasure_unit_closedBall / Chapter04.hausdorff_blowUp_image (unknown identifier), example : HasBesicovitchCovering (EuclideanSpace ℝ (Fin P)) := inferInstance (ok)`
- `python3: scan of dag.json for related lean_statements (HasApproximateTangentSpaceAt|unitBallVolume|withDensity|densit) and collision scan of the six dorag_dbs_* names over all 8 workspaces' dag.json (no collision); math-wiki page submission-regcomp-atl-upper-density-zero.md`
- `python3 -I: gmt-compare.py child_modules (contract mode) + lean_contract.validate_lean_statement on the six statements; lean on the six Challenge_*.lean (only the sorry warning)`
- `lean Integrated.lean (six complete child proofs + parent assembly, uncle as axiom; #print axioms)`
- `grep/sed in /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt (2.3–2.4, lines 266–288), chapter-03.txt (1.4–1.5, lines 77–96), chapter-01.txt (3.6–3.7 lines 700–711, 3.11–3.12 lines 773–854, 3.16 lines 905–925), chapter-04.txt (4.7–4.8, lines 536–546)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Ring/Pow.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Complex/Exponential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaNormalization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/LowerDensityTangents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/PositiveMultiplicityScale.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-498c875e36/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/math-wiki/submission-regcomp-atl-upper-density-zero.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`

The snapshot pins project b4d606d and Mathlib 25730c7c. Its GMT/Ch07/Contract.lean is byte-identical to the workspace contract and to GMT/Ch07/Submission.lean, the compiler context of every child type.

No declaration in the snapshot proves this node or any child; dorag_dbs_*/dorag_standing have no match.

What is importable after import GMT.Ch07.Submission (checked with lean):
- Not importable: the parent’s Step 5b library pointer simon_theorem_3_6 (Chapter01/DensityComparison.lean) and the SimonGMT Chapter04 tangent-density lemmas; these are used only as proof patterns.
- Importable: Mathlib’s Besicovitch.ae_tendsto_measure_inter_div (Covering/Besicovitch.lean:1105) with the HasBesicovitchCovering instance (BesicovitchVectorSpace.lean:499), euclideanHausdorffMeasure_homothety_image (Volume/Measure.lean:164), EuclideanSpace.euclideanHausdorffMeasure_eq_volume (:187), Isometry.euclideanHausdorffMeasure_image (:131), addHaar_closedBall_eq_addHaar_ball (EqHaar.lean:509), one_add_mul_le_pow (Ring/Pow.lean:99), add_one_le_exp (Complex/Exponential.lean:632), and SimonGMT Chapter03 regular_euclideanHausdorffMeasure_restrict_submodule. The children use these.

Related nodes in other branches:
- rsd_tendsto_closedBall_density_of_approxTangent (full limit, needs finiteness), rsd_ae_tendsto_withDensity_div_closedBall and rsd_imrep_compact_measure_ne_top are still decomposing, so they are not reusable.
- regcomp_atl_upper_density_zero is accepted, but no child needs it.
The six dorag_dbs_* names collide with nothing in any workspace DAG.

Lean checks:
- All six statements elaborate in comparator scope.
- Complete proofs of all six compile with only propext, Classical.choice and Quot.sound.
- The exact parent type compiles from them plus the sibling monotonicity type.
