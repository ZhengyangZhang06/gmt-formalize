# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.density_bounds-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.density_bounds-a1.constants-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 0 (Simon Ch. 5, 2.3–2.4, chapter-05.txt lines 266–288, where δ ≤ δ₀(n) is chosen so that 1 + Cδ ≤ 2). The parent obtains C₁ from the mean value theorem. Here explicit elementary constants are used instead. This is a detail-level change: the parent only uses the existence of δ₁ ∈ (0, 1/8] and C₁ > 0 with C₁δ₁ ≤ 1/2 and e^δ(1 + δ)(1 − 4δ)^{−n} ≤ 1 + C₁δ on [0, δ₁].

1. Definitions. Put δ₁ := 1/(24(n + 1)) and C₁ := 4 + 12n (n cast to ℝ).
2. Properties of the constants. δ₁ > 0 and δ₁ ≤ 1/24 ≤ 1/8 because n + 1 ≥ 1. C₁ ≥ 4 > 0. C₁δ₁ = (4 + 12n)/(24n + 24) ≤ 1/2 because 2(4 + 12n) = 8 + 24n ≤ 24 + 24n.
3. Fix a real δ with 0 ≤ δ ≤ δ₁. Then δ(24(n + 1)) ≤ 1, so δ ≤ 1/24 and nδ ≤ 1/24.
4. Exponential factor: e^δ ≤ 1 + 2δ. Real.add_one_le_exp at −δ gives 1 − δ ≤ e^{−δ}, and e^δ·e^{−δ} = 1 with e^δ > 0, so e^δ(1 − δ) ≤ 1. Since (1 + 2δ)(1 − δ) = 1 + δ − 2δ² ≥ 1 (as 2δ² ≤ δ for 0 ≤ δ ≤ 1/2) and 1 − δ > 0, e^δ ≤ 1/(1 − δ) ≤ 1 + 2δ.
5. Denominator: (1 − 4δ)ⁿ > 0 and 1/(1 − 4δ)ⁿ ≤ 1 + 8nδ.
 (a) 1 − 4δ ≥ 5/6 > 0, so (1 − 4δ)ⁿ > 0.
 (b) Bernoulli's inequality (Mathlib one_add_mul_le_pow, valid because −4δ ≥ −2) gives (1 − 4δ)ⁿ ≥ 1 − 4nδ.
 (c) (1 + 8nδ)(1 − 4nδ) = 1 + 4nδ(1 − 8nδ) ≥ 1, because nδ ≥ 0 and 8nδ ≤ 1/3.
 (d) As 1 + 8nδ ≥ 0, (1 + 8nδ)(1 − 4δ)ⁿ ≥ (1 + 8nδ)(1 − 4nδ) ≥ 1. Dividing by (1 − 4δ)ⁿ > 0 gives the claim.
6. Product. Using 4, 5 and 1 + δ > 0, all factors being nonnegative:
 e^δ(1 + δ)/(1 − 4δ)ⁿ = e^δ·(1 + δ)·(1/(1 − 4δ)ⁿ) ≤ (1 + 2δ)(1 + δ)(1 + 8nδ).
 (1 + 2δ)(1 + δ) = 1 + 3δ + 2δ² ≤ 1 + 4δ.
 (1 + 4δ)(1 + 8nδ) = 1 + (4 + 8n)δ + 32nδ² ≤ 1 + (4 + 12n)δ, because 32nδ² ≤ 4nδ for δ ≤ 1/8 (nδ(1 − 8δ) ≥ 0).
 Hence e^δ(1 + δ)/(1 − 4δ)ⁿ ≤ 1 + C₁δ.
7. Steps 2 and 6 give every conjunct: 0 < δ₁, δ₁ ≤ 1/8, 0 < C₁, C₁δ₁ ≤ 1/2, and the inequality for every δ ∈ [0, δ₁]. ∎

Appendix: Lean proof of exactly this statement, following Steps 1–6. It was kernel-checked (lean-4.35.0-rc3, Mathlib 25730c7c, after import GMT.Ch07.Submission in the contract scope: namespace GMT.Ch07 with the contract's open commands); #print axioms gives propext, Classical.choice, Quot.sound.
theorem Submission.dorag_dbs_density_constants : ∀ n : ℕ, ∃ δ₁ C₁ : ℝ, 0 < δ₁ ∧ δ₁ ≤ 1 / 8 ∧ 0 < C₁ ∧ C₁ * δ₁ ≤ 1 / 2 ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ δ₁ → Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n ≤ 1 + C₁ * δ := by
  intro n
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨1 / (24 * (n + 1)), 4 + 12 * n, by positivity, ?_, by positivity, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  · rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  · intro δ hδ0 hδ1
    have hpos : (0 : ℝ) < 24 * (n + 1) := by positivity
    have hδ' : δ * (24 * (n + 1)) ≤ 1 := (le_div_iff₀ hpos).mp hδ1
    have hδ24 : δ ≤ 1 / 24 := by nlinarith
    have hnδ : n * δ ≤ 1 / 24 := by nlinarith
    have hnδ0 : 0 ≤ (n : ℝ) * δ := mul_nonneg hn0 hδ0
    -- exponential factor
    have hexp : Real.exp δ ≤ 1 + 2 * δ := by
      have hlow := Real.add_one_le_exp (-δ)
      have hprod : Real.exp δ * Real.exp (-δ) = 1 := by rw [← Real.exp_add]; simp
      have hepos := Real.exp_pos δ
      nlinarith
    -- denominator
    have hbern : 1 + (n : ℝ) * (-4 * δ) ≤ (1 + (-4 * δ)) ^ n :=
      one_add_mul_le_pow (by linarith) n
    have hA : 1 + (n : ℝ) * (-4 * δ) = 1 - 4 * n * δ := by ring
    have hB : (1 + (-4 * δ)) = 1 - 4 * δ := by ring
    rw [hA, hB] at hbern
    have hden_pos : 0 < (1 - 4 * δ) ^ n := pow_pos (by linarith) n
    have h8 : 0 ≤ 1 + 8 * n * δ := by positivity
    have hden : 1 ≤ (1 + 8 * n * δ) * (1 - 4 * δ) ^ n := by
      have h1 : (1 + 8 * n * δ) * (1 - 4 * n * δ) ≤ (1 + 8 * n * δ) * (1 - 4 * δ) ^ n :=
        mul_le_mul_of_nonneg_left hbern h8
      have h2 : 1 ≤ (1 + 8 * n * δ) * (1 - 4 * n * δ) := by
        nlinarith [mul_nonneg hnδ0 (by linarith : (0 : ℝ) ≤ 1 - 8 * n * δ)]
      linarith
    have hinv : 1 / (1 - 4 * δ) ^ n ≤ 1 + 8 * n * δ := by
      rw [div_le_iff₀ hden_pos]; linarith
    have hq1 : (1 + 2 * δ) * (1 + δ) ≤ 1 + 4 * δ := by nlinarith
    have hq2 : (1 + 4 * δ) * (1 + 8 * n * δ) ≤ 1 + (4 + 12 * n) * δ := by
      nlinarith [mul_nonneg hnδ0 (by linarith : (0 : ℝ) ≤ 1 - 8 * δ)]
    calc Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n
        = Real.exp δ * (1 + δ) * (1 / (1 - 4 * δ) ^ n) := by ring
      _ ≤ (1 + 2 * δ) * (1 + δ) * (1 + 8 * n * δ) := by
          apply mul_le_mul _ hinv (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right hexp (by linarith)
      _ ≤ (1 + 4 * δ) * (1 + 8 * n * δ) := mul_le_mul_of_nonneg_right hq1 h8
      _ ≤ 1 + (4 + 12 * n) * δ := hq2

## Key steps

1. Choose δ₁ = 1/(24(n+1)) and C₁ = 4 + 12n; then 0 < δ₁ ≤ 1/8, C₁ > 0 and C₁δ₁ ≤ 1/2.
2. For 0 ≤ δ ≤ δ₁: e^δ ≤ 1/(1 − δ) ≤ 1 + 2δ, from Real.add_one_le_exp at −δ.
3. Bernoulli gives (1 − 4δ)ⁿ ≥ 1 − 4nδ, and (1 + 8nδ)(1 − 4nδ) ≥ 1 since 8nδ ≤ 1/3; hence (1 − 4δ)^{−n} ≤ 1 + 8nδ.
4. Multiply: e^δ(1 + δ)(1 − 4δ)^{−n} ≤ (1 + 2δ)(1 + δ)(1 + 8nδ) ≤ (1 + 4δ)(1 + 8nδ) ≤ 1 + (4 + 12n)δ.

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
