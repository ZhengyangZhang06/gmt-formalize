# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.density_bounds-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.density_bounds-a1.mult_one-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Sibling map (dependency key — frozen Lean declaration): lower_density_mult — Submission.dorag_dbs_lower_density_ge_mult.
Source: parent proof Step 6, θ = 1 a.e. in B_{4δρ}(z) (Simon Ch. 5, 2.3–2.4, chapter-05.txt lines 266–288, with the parent's correction replacing Simon's '1 ≤ θ ≤ 1 + Cδ'). The parent applies the present lemma with S = B_{4δρ}(z) and c₀ = 3/2; then c = 7/4 below, exactly the parent's choice.

Notation: M := R.carrier, θ := R.mult, Hⁿ := μHE[n], μ := R.measure = (Hⁿ⌞M).withDensity θ, ω := unitBallVolume n, a⁺ := ENNReal.ofReal a, B_t(x) the closed ball.

1. μ ≪ Hⁿ⌞M (withDensity_absolutelyContinuous). Hence the conclusion of lower_density_mult (for P, n, U, W, R, using n ≥ 1, W open, W ⊆ U) holds for μ-a.e. x: if x ∈ W then for every c < θ(x), eventually c⁺·ω·(tⁿ)⁺ ≤ μ(B_t(x)). Also Hⁿ⌞M-a.e. x lies in M (ae_restrict_mem), hence μ-a.e. x lies in M.
2. Fix x with both properties and x ∈ S.
 (a) Then x ∈ W (as S ⊆ W) and x ∈ M, so θ(x) ≥ 1 (R.mult_pos).
 (b) Suppose θ(x) ≠ 1; then θ(x) ≥ 2.
 (c) Let c₁ := max(c₀, 0) < 2 and c := (c₁ + 2)/2. Then c₁ < c < 2 ≤ θ(x); for c₀ = 3/2, c = 7/4.
3. By Step 1 and the hypothesis on S, both of the following hold as t ↓ 0: eventually c⁺·ω·(tⁿ)⁺ ≤ μ(B_t(x)), and eventually μ(B_t(x)) ≤ c₀⁺·ω·(tⁿ)⁺. Since 𝓝[>]0 is a proper filter, there is t > 0 with c⁺·ω·(tⁿ)⁺ ≤ c₀⁺·ω·(tⁿ)⁺.
4. Contradiction.
 (a) ω ∈ (0, ∞): it is the Lebesgue measure of the nonempty, open, bounded unit ball of Euclid n (measure_ball_pos, measure_ball_lt_top). Also (tⁿ)⁺ ∈ (0, ∞) since t > 0.
 (b) Cancelling the factor ω·(tⁿ)⁺ ∈ (0, ∞) (ENNReal.mul_le_mul_iff_left) gives c⁺ ≤ c₀⁺.
 (c) By ENNReal.ofReal_le_ofReal_iff', c ≤ c₀ or c ≤ 0. Both contradict c > c₁ = max(c₀, 0).
5. Hence θ(x) = 1. As this holds for μ-a.e. x with x ∈ S, R.mult x = 1 for μ-a.e. x ∈ S. ∎

Appendix: Lean proof of exactly this statement from the sibling declaration, following Steps 1–5. It was kernel-checked (lean-4.35.0-rc3, Mathlib 25730c7c, after import GMT.Ch07.Submission in the contract scope, with the sibling at its frozen type); #print axioms gives propext, Classical.choice, Quot.sound plus the sibling chain.
theorem Submission.dorag_dbs_mult_eq_one_of_density_lt_two : ∀ (P n : ℕ) (U W S : Set (Euclid P)) (R : IMRep U n) (c₀ : ℝ), 0 < n → IsOpen W → W ⊆ U → S ⊆ W → c₀ < 2 → (∀ x ∈ S, ∀ᶠ t in 𝓝[>] (0 : ℝ), R.measure (closedBall x t) ≤ ENNReal.ofReal c₀ * unitBallVolume n * ENNReal.ofReal (t ^ n)) → ∀ᵐ x ∂R.measure, x ∈ S → R.mult x = 1 := by
  intro P n U W S R c₀ hn hW hWU hSW hc₀ hup
  have h5 := Submission.dorag_dbs_lower_density_ge_mult P n U W R hn hW hWU
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  have h5' := hac.ae_le h5
  have hmem : ∀ᵐ x ∂R.measure, x ∈ R.carrier :=
    hac.ae_le (ae_restrict_mem R.measurableSet_carrier)
  filter_upwards [h5', hmem] with x hx hxM hxS
  have hxW := hSW hxS
  have hpos := R.mult_pos x hxM
  by_contra hne
  have h2 : 2 ≤ R.mult x := by omega
  have hc₁ : max c₀ 0 < 2 := max_lt hc₀ (by norm_num)
  have h2' : (2 : ℝ) ≤ R.mult x := by exact_mod_cast h2
  have hcm : (max c₀ 0 + 2) / 2 < (R.mult x : ℝ) := by linarith
  have hlow := hx hxW ((max c₀ 0 + 2) / 2) hcm
  obtain ⟨t, ht1, ht2, htpos⟩ := (hlow.and ((hup x hxS).and self_mem_nhdsWithin)).exists
  have hω0 : unitBallVolume n ≠ 0 := by
    unfold unitBallVolume
    exact (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := by
    unfold unitBallVolume
    exact measure_ball_lt_top.ne
  have htn0 : ENNReal.ofReal (t ^ n) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact pow_pos htpos n
  have hcomb := ht1.trans ht2
  rw [mul_assoc, mul_assoc] at hcomb
  have hle : ENNReal.ofReal ((max c₀ 0 + 2) / 2) ≤ ENNReal.ofReal c₀ :=
    (ENNReal.mul_le_mul_iff_left (mul_ne_zero hω0 htn0)
      (ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top)).mp hcomb
  rw [ENNReal.ofReal_le_ofReal_iff'] at hle
  rcases hle with h | h
  · have := le_max_left c₀ 0
    linarith
  · have := le_max_right c₀ 0
    linarith

## Key steps

1. μ ≪ Hⁿ⌞M and μ-a.e. x ∈ M, so the conclusion of lower_density_mult holds μ-a.e.
2. If θ(x) ≥ 2 at such an x ∈ S, take c = (max(c₀, 0) + 2)/2 < θ(x).
3. Some t > 0 gives cω_ntⁿ ≤ μ(B_t(x)) ≤ c₀ω_ntⁿ; cancelling 0 < ω_ntⁿ < ∞ gives a contradiction.
4. Hence θ = 1 μ-a.e. on S.

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
