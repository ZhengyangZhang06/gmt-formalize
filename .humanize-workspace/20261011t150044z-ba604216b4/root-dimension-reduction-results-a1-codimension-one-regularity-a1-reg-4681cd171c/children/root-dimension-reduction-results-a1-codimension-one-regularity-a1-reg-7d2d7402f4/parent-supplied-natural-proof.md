# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.rectifiable_criterion-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.rectifiable_criterion-a1.cone_exclusion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent proof, step 4 (Cone exclusion). This is the printed claim (10) of Simon Ch. 3, proof of 1.6 “⇐” (chapter-03.txt lines 220–246: a point y ∈ X_{1/4}(π_j, x) ∩ E_j ∩ ∂B_σ(x) with σ ≤ δ/2 forces B_{σ/8}(y) ⊆ X_{1/2}(π_x, x) ∩ B_{2σ}(x), contradicting (9) with ε = 1/16^n). It is taken in the parent's codimension-one normalization: the cone C(x) = X_{1/4}(ν(x), x) around the normal line, a reference direction v with |ν(x) − v| ≤ 1/16, and the threshold (1 + 16^m)ε < 1 (the parent takes ε = 1/(2(1 + 16^m))). The hypotheses are used only at x (cone bound, radius 2ρ) and at x′ (ball bound, radius ρ/8).

1. Trivial case and setup. If x′ = x both sides vanish. Otherwise let w := x′ − x and ρ := |w| > 0, and suppose, for a contradiction, that |⟨w, v⟩| > ρ/2. Since 0 < ρ < δ/2 we have δ > 0, 0 < ρ/8 < δ and 0 < 2ρ < δ.

2. Normal component. By Cauchy–Schwarz, |⟨w, v − ν(x)⟩| ≤ |w||v − ν(x)| ≤ ρ/16, so |⟨w, ν(x)⟩| ≥ |⟨w, v⟩| − |⟨w, v − ν(x)⟩| > ρ/2 − ρ/16 = 7ρ/16.

3. Inclusion B̄_{ρ/8}(x′) ⊆ C(x) ∩ B̄_{2ρ}(x). Let |z − x′| ≤ ρ/8. Then z − x = w + (z − x′), so |z − x| ≤ ρ + ρ/8 = 9ρ/8 ≤ 2ρ. Also |⟨z − x′, ν(x)⟩| ≤ |z − x′||ν(x)| ≤ ρ/8 (|ν(x)| = 1), hence |⟨z − x, ν(x)⟩| ≥ |⟨w, ν(x)⟩| − |⟨z − x′, ν(x)⟩| > 7ρ/16 − ρ/8 = 5ρ/16 = 10ρ/32 > 9ρ/32 ≥ ¼|z − x|. So z ∈ C(x) ∩ B̄_{2ρ}(x).

4. Measure comparison. By the ball bound at x′ ∈ K with radius ρ/8 ∈ (0, δ), monotonicity of μ together with step 3, and the cone bound at x ∈ K with radius 2ρ ∈ (0, δ):
(1 − ε)⁺ ω_m (ρ/8)^m ≤ μ(B̄_{ρ/8}(x′)) ≤ μ(C(x) ∩ B̄_{2ρ}(x)) ≤ ε ω_m (2ρ)^m.

5. Arithmetic contradiction. From (1 + 16^m)ε < 1 and ε ≥ 0 we get 1 − ε > 16^m ε ≥ 0, so (1 − ε)⁺ = 1 − ε. Write a := ω_m ∈ (0, ∞). Every quantity in step 4 is then a finite nonnegative real, so (1 − ε) a (ρ/8)^m ≤ ε a (2ρ)^m = ε 16^m a (ρ/8)^m. Dividing by a (ρ/8)^m > 0 gives 1 − ε ≤ 16^m ε, i.e. (1 + 16^m)ε ≥ 1, contradicting the hypothesis. Therefore |⟨w, v⟩| ≤ ρ/2 = ½|x′ − x|. ∎

Lean note (non-normative aid). The following tactic proof of `Submission.codim1_rdo_dg_rc_cone_exclusion` (the frozen type above, followed by `:= by`) compiles against the frozen contract: `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's `open`s, Lean v4.35.0-rc3, Mathlib 25730c7c; `#print axioms` gives only propext, Classical.choice, Quot.sound.
```lean
  intro m μ ν K δ ε hν1 hε0 hε1 hlow hup x hx x' hx' v hv hxx'
  by_contra hcon
  push Not at hcon
  set w := x' - x with hw
  set ρ := ‖w‖ with hρ
  have hρ0 : 0 < ρ := by
    rcases (norm_nonneg w).lt_or_eq with h | h
    · exact h
    · exfalso
      have hw0 : w = 0 := norm_eq_zero.1 h.symm
      rw [hw0] at hcon
      simp at hcon
      linarith [h, hρ]
  have hδ : 0 < δ := by linarith
  -- step 2: the normal component along `ν x` is large
  have h2 : 7 * ρ / 16 < |inner ℝ w (ν x)| := by
    have e1 : |inner ℝ w (v - ν x)| ≤ ρ * ‖ν x - v‖ := by
      calc |inner ℝ w (v - ν x)| ≤ ‖w‖ * ‖v - ν x‖ := abs_real_inner_le_norm _ _
        _ = ρ * ‖ν x - v‖ := by rw [norm_sub_rev v (ν x)]
    have e2 : inner ℝ w v = inner ℝ w (ν x) + inner ℝ w (v - ν x) := by
      rw [inner_sub_right]; ring
    have e3 : |inner ℝ w v| ≤ |inner ℝ w (ν x)| + |inner ℝ w (v - ν x)| := by
      rw [e2]; exact abs_add_le _ _
    have e4 : ρ * ‖ν x - v‖ ≤ ρ * (1 / 16) := mul_le_mul_of_nonneg_left hv hρ0.le
    linarith
  -- step 3: the small ball around `x'` lies in the cone around `x`
  have hsub : closedBall x' (ρ / 8) ⊆
      {z | (1 / 4 : ℝ) * ‖z - x‖ ≤ |inner ℝ (z - x) (ν x)|} ∩ closedBall x (2 * ρ) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have hzx : z - x = w + (z - x') := by rw [hw]; abel
    have hnorm : ‖z - x‖ ≤ 9 * ρ / 8 := by
      calc ‖z - x‖ = ‖w + (z - x')‖ := by rw [hzx]
        _ ≤ ‖w‖ + ‖z - x'‖ := norm_add_le _ _
        _ ≤ ρ + ρ / 8 := by linarith
        _ = 9 * ρ / 8 := by ring
    have hin : |inner ℝ (z - x') (ν x)| ≤ ρ / 8 := by
      calc |inner ℝ (z - x') (ν x)| ≤ ‖z - x'‖ * ‖ν x‖ := abs_real_inner_le_norm _ _
        _ = ‖z - x'‖ := by rw [hν1 x, mul_one]
        _ ≤ ρ / 8 := hz
    have hinner : inner ℝ (z - x) (ν x) = inner ℝ w (ν x) + inner ℝ (z - x') (ν x) := by
      rw [hzx, inner_add_left]
    have hbig : 5 * ρ / 16 < |inner ℝ (z - x) (ν x)| := by
      rw [hinner]
      have h' : |inner ℝ w (ν x)| ≤
          |inner ℝ w (ν x) + inner ℝ (z - x') (ν x)| + |inner ℝ (z - x') (ν x)| := by
        have := abs_sub (inner ℝ w (ν x) + inner ℝ (z - x') (ν x)) (inner ℝ (z - x') (ν x))
        simpa using this
      linarith
    refine ⟨?_, ?_⟩
    · show (1 / 4 : ℝ) * ‖z - x‖ ≤ |inner ℝ (z - x) (ν x)|
      linarith
    · rw [mem_closedBall, dist_eq_norm]; linarith
  -- step 4: measure comparison
  have hlow' := hlow x' hx' (ρ / 8) (by positivity) (by linarith)
  have hup' := hup x hx (2 * ρ) (by positivity) (by linarith)
  have hchain : ENNReal.ofReal (1 - ε) * unitBallVolume m * ENNReal.ofReal ((ρ / 8) ^ m) ≤
      ENNReal.ofReal ε * unitBallVolume m * ENNReal.ofReal ((2 * ρ) ^ m) :=
    hlow'.trans ((measure_mono hsub).trans hup')
  -- step 5: arithmetic
  have hω0 : unitBallVolume m ≠ 0 := by
    unfold unitBallVolume; exact (measure_ball_pos _ _ one_pos).ne'
  have hωt : unitBallVolume m ≠ ∞ := by
    unfold unitBallVolume; exact measure_ball_lt_top.ne
  set a := (unitBallVolume m).toReal with ha_def
  have ha : 0 < a := ENNReal.toReal_pos hω0 hωt
  have hωeq : unitBallVolume m = ENNReal.ofReal a := (ENNReal.ofReal_toReal hωt).symm
  have h1ε : 0 ≤ 1 - ε := by
    have : 0 ≤ (16 : ℝ) ^ m * ε := by positivity
    nlinarith
  have hL : ENNReal.ofReal (1 - ε) * unitBallVolume m * ENNReal.ofReal ((ρ / 8) ^ m) =
      ENNReal.ofReal ((1 - ε) * a * (ρ / 8) ^ m) := by
    rw [hωeq, ← ENNReal.ofReal_mul h1ε, ← ENNReal.ofReal_mul (by positivity)]
  have hR : ENNReal.ofReal ε * unitBallVolume m * ENNReal.ofReal ((2 * ρ) ^ m) =
      ENNReal.ofReal (ε * a * (2 * ρ) ^ m) := by
    rw [hωeq, ← ENNReal.ofReal_mul hε0, ← ENNReal.ofReal_mul (by positivity)]
  rw [hL, hR, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hchain
  have hpow : (2 * ρ) ^ m = 16 ^ m * (ρ / 8) ^ m := by
    rw [← mul_pow]; congr 1; ring
  rw [hpow] at hchain
  have hpos : 0 < a * (ρ / 8) ^ m := by positivity
  have h16 : (1 - ε) * (a * (ρ / 8) ^ m) ≤ (ε * 16 ^ m) * (a * (ρ / 8) ^ m) := by
    calc (1 - ε) * (a * (ρ / 8) ^ m) = (1 - ε) * a * (ρ / 8) ^ m := by ring
      _ ≤ ε * a * (16 ^ m * (ρ / 8) ^ m) := hchain
      _ = (ε * 16 ^ m) * (a * (ρ / 8) ^ m) := by ring
  have h17 : 1 - ε ≤ ε * 16 ^ m := le_of_mul_le_mul_right h16 hpos
  nlinarith
```

## Key steps

1. If |⟨x′ − x, v⟩| > ρ/2 with ρ = |x′ − x| > 0, then |⟨x′ − x, ν(x)⟩| > 7ρ/16 because |ν(x) − v| ≤ 1/16.
2. Then B̄_{ρ/8}(x′) ⊆ C(x) ∩ B̄_{2ρ}(x): the normal component exceeds 5ρ/16 > ¼ · 9ρ/8.
3. The ball bound at x′ (radius ρ/8) and the cone bound at x (radius 2ρ) give (1 − ε) ω_m (ρ/8)^m ≤ ε ω_m (2ρ)^m.
4. Cancelling ω_m (ρ/8)^m ∈ (0, ∞) gives 1 − ε ≤ 16^m ε, contradicting (1 + 16^m)ε < 1.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; sha256sum <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `python3 scans of dag.json: selected node (depth 5, no children), sibling flat_tangent_density frozen type, collision check of the 7 codim1_rdo_dg_rc_* names, statements mentioning CountablyRectifiable or 16 ^ (cbrr_*, dpf*, codim1_rdo_*)`
- `rg -n 'theorem measurable_measure_prodMk_left|theorem LipschitzOnWith.extend_real|isClosed_range|finite_cover_balls|exists_isCompact_diff_lt|orthogonal_span_singleton|fromOrthogonalSpanSingleton|isOpen_biUnion_countable|isOpen_iUnion_countable|tendsto_measure_iUnion_atTop|Measurable.inner|instance.*InnerRegularCompactLTTop' <snapshot>/mathlib/Mathlib`
- `grep -n '^theorem|^def' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `sed -n 100,280p book/chapter-03.txt (printed proof of Simon Ch. 3, 1.6 ⇐)`
- `lake env lean -DautoImplicit=false /tmp/rc-split-check/Names.lean and Names2.lean (#check of the lemmas above inside the import closure of GMT.Ch07.Submission)`
- `lake env lean -DautoImplicit=false /tmp/rc-split-check/Types.lean, Assembly.lean, Full.lean and /tmp/rc-final/Verify.lean (7 child types, child proofs rebuilt from the returned JSON, parent assembly with a sorry stub of the uncle; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Antilipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/SpecialFunctions/Inner.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-4681cd171c/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/rc-split-check/Full.lean`
- `/tmp/rc-final/Verify.lean`

Pins: the snapshot manifest pins project b4d606db and Mathlib 25730c7c, and the snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f9503aa28…).

No local declaration states any of the seven children. SimonGMT Chapter03/Rectifiable.lean supplies only the definition CountablyRectifiable and the lemmas countablyRectifiable_range, _iUnion, _sUnion, _of_measure_zero and CountablyRectifiable.mono, which the children use. The related general-codimension DAG branch (cbr_rectifiable_of_approx_tangent → cbrr_cone_claim, cbrr_rectifiable_of_uniform_density) is unaccepted and has different types, so nothing is reused.

Snapshot Mathlib supplies:
- measurable_measure_prodMk_left (Prod.lean:97);
- LipschitzOnWith.extend_real (Lipschitz.lean:308);
- AntilipschitzWith.isClosed_range (Antilipschitz.lean:175);
- OrthonormalBasis.fromOrthogonalSpanSingleton (PiL2.lean:1157);
- MeasurableSet.exists_isCompact_sdiff_lt (Regular.lean:843), with an InnerRegularCompactLTTop instance for every measure on Euclid (RegularityCompacts.lean:186);
- tendsto_measure_iUnion_atTop (Continuity.lean:198);
- IsCompact.finite_cover_balls (Pseudo/Basic.lean:260);
- TopologicalSpace.isOpen_biUnion_countable.
Measurable.inner (SpecialFunctions/Inner.lean) is outside the import closure, so Continuous.measurable2 is used instead.

Lean: all 7 child types elaborate after import GMT.Ch07.Submission in namespace GMT.Ch07 with the contract opens. Every child is proved with axioms propext, Classical.choice, Quot.sound only. The selected frozen type is proved from halving_step, of_halving and a sorry stub of the uncle Submission.codim1_rdo_dg_flat_tangent_density_cone; the only extra axiom is sorryAx, from that stub.

Names: the 7 codim1_rdo_dg_rc_* identifiers occur nowhere in dag.json (945 nodes), GMT/, SimonGMT or Mathlib.
