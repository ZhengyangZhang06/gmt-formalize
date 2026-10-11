# Parent-supplied natural-language proof

- Parent DAG node: `root.eilenberg_inequality-a1`
- Child DAG node: `root.eilenberg_inequality-a1.volume_diameter_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source and role. This is Step 1 of the parent proof (the elementary volume bound). In Simon's proof of Ch. 2, Theorem 1.9 (chapter-02.txt lines 401–406) the corresponding estimate Lᵐ(f(C_{ij})) ≤ ωₘ(diam f(C_{ij})/2)ᵐ is taken from the isodiametric inequality 2.10. As in the parent, it is replaced here by the cruder inclusion S ⊆ B̄_{diam S}(s₀); only the constant changes, and any constant suffices for the parent. The closure is taken so that the set is Borel (Simon instead uses σ-compactness to see that f(C_{ij}) is Borel, lines 375–377).

Notation. λₘ = volume on ℝᵐ = EuclideanSpace ℝ (Fin m); ωₘ := λₘ(B₁(0)), B₁(0) the open unit ball; powers are taken in [0, ∞].

Proof.
1. S = ∅. Then closure S = ∅ and λₘ(∅) = 0 ≤ right side.
2. m = 0. ℝ⁰ has exactly one point, the zero vector. So B₁(0) = ℝ⁰ (that point is at distance 0 < 1 from 0), (diam S)⁰ = 1, and the right side is λ₀(ℝ⁰) ≥ λ₀(closure S) by monotonicity. From now on S ≠ ∅ (fix s₀ ∈ S) and m ≥ 1.
3. ωₘ > 0. B₁(0) is a nonempty open set, and Lebesgue measure, an additive Haar measure, is positive on nonempty open sets.
4. diam S = ∞. Then (diam S)ᵐ = ∞ (since m ≥ 1) and ωₘ·∞ = ∞ (since ωₘ ≠ 0); the inequality is trivial.
5. diam S < ∞: inclusion. Then S is bounded. Let D := (diam S).toReal ≥ 0 be its real diameter, so ofReal(D) = diam S. The closure of S is bounded and has the same diameter. For x ∈ closure S, both x and s₀ lie in closure S, so dist(x, s₀) ≤ diam(closure S) = D. Hence closure S ⊆ B̄_D(s₀).
6. diam S < ∞: volume of the ball. λₘ is translation invariant, scales by ρᵐ under x ↦ ρx, and dim ℝᵐ = m, so λₘ(B̄_D(s₀)) = Dᵐ·λₘ(B₁(0)) (Mathlib: MeasureTheory.Measure.addHaar_closedBall, whose right side is ofReal(D^finrank)·μ(ball 0 1), together with finrank_euclideanSpace_fin). Moreover ofReal(Dᵐ) = ofReal(D)ᵐ = (diam S)ᵐ, because D ≥ 0 (ENNReal.ofReal_pow) and ofReal((diam S).toReal) = diam S since diam S ≠ ∞ (ENNReal.ofReal_toReal).
7. Conclusion. By monotonicity and steps 5–6, λₘ(closure S) ≤ λₘ(B̄_D(s₀)) = (diam S)ᵐ·ωₘ = ωₘ·(diam S)ᵐ. ∎

Formalization notes. Set.eq_empty_or_nonempty; for m = 0, Subsingleton.elim x 0 gives Metric.ball (0 : Rn 0) 1 = univ; Metric.measure_ball_pos; ENNReal.top_pow; ENNReal.mul_top; Metric.isBounded_iff_ediam_ne_top; Metric.diam_closure; Metric.dist_le_diam_of_mem; Measure.addHaar_closedBall volume s₀ Metric.diam_nonneg; finrank_euclideanSpace_fin; ENNReal.ofReal_pow; Metric.diam (the toReal of Metric.ediam); ENNReal.ofReal_toReal.

Appendix (non-normative formalization aid). The Lean proof below compiled with the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c) in a scratch file outside the repository. The file begins with import GMT.Ch03.Submission and replays the frozen Contract scope exactly as the comparator does: open Filter MeasureTheory Module Set; open scoped CompactlySupported ENNReal NNReal Topology; namespace GMT.Ch03; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt HasWeightedApproximateTangentSpaceAt PurelyUnrectifiable blowUpMap). A scratch copy of the comparator's child target (theorem _root_.HumanizeNodeComparator.target : (frozen statement) := by exact Submission.X) accepted it, and the whole chain uses only the axioms propext, Classical.choice and Quot.sound. Measurable.ennreal_tsum emits only a deprecation warning.

theorem Submission.volume_closure_le_unitBall_mul_ediam_pow : ∀ (m : ℕ) (S : Set (Rn m)), volume (closure S) ≤ volume (Metric.ball (0 : Rn m) 1) * Metric.ediam S ^ m := by
  intro m S
  rcases S.eq_empty_or_nonempty with rfl | ⟨s₀, hs₀⟩
  · simp
  by_cases hm : m = 0
  · subst hm
    have hball : Metric.ball (0 : Rn 0) 1 = univ := by
      ext x; simp [Subsingleton.elim x 0]
    rw [pow_zero, mul_one, hball]
    exact measure_mono (subset_univ _)
  have hω0 : volume (Metric.ball (0 : Rn m) 1) ≠ 0 := (Metric.measure_ball_pos volume (0 : Rn m) one_pos).ne'
  by_cases hD : Metric.ediam S = ∞
  · rw [hD, ENNReal.top_pow hm, ENNReal.mul_top hω0]
    exact le_top
  have hb : Bornology.IsBounded S := Metric.isBounded_iff_ediam_ne_top.2 hD
  have hsub : closure S ⊆ Metric.closedBall s₀ (Metric.diam S) := by
    intro x hx
    rw [Metric.mem_closedBall, ← Metric.diam_closure]
    exact Metric.dist_le_diam_of_mem hb.closure hx (subset_closure hs₀)
  calc volume (closure S) ≤ volume (Metric.closedBall s₀ (Metric.diam S)) := measure_mono hsub
    _ = ENNReal.ofReal (Metric.diam S ^ m) * volume (Metric.ball (0 : Rn m) 1) := by
        rw [Measure.addHaar_closedBall volume s₀ Metric.diam_nonneg, finrank_euclideanSpace_fin]
    _ = volume (Metric.ball (0 : Rn m) 1) * Metric.ediam S ^ m := by
        rw [mul_comm, ENNReal.ofReal_pow Metric.diam_nonneg, Metric.diam, ENNReal.ofReal_toReal hD]

## Key steps

1. Trivial cases: S = ∅; m = 0, where B₁(0) = ℝ⁰ and the power is 1.
2. m ≥ 1 and diam S = ∞: the right side is ∞ because ωₘ > 0.
3. Bounded S: closure S ⊆ B̄_{diam S}(s₀) for any s₀ ∈ S, because diam(closure S) = diam S.
4. λₘ(B̄_D(s₀)) = Dᵐ·ωₘ (addHaar_closedBall, finrank = m) and ofReal(D)ᵐ = (diam S)ᵐ.

## Reference use

### local-project

Queries:
- `rg -n 'μHE|euclideanHausdorffMeasure' mathlib/Mathlib (snapshot)`
- `rg -n '^theorem|^lemma|^def|^noncomputable def' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'def ediam|def EMetric.diam' mathlib/Mathlib/Topology/EMetricSpace mathlib/Mathlib/Topology/MetricSpace`
- `rg -n 'theorem lintegral_liminf_le|theorem Measurable.liminf|theorem tendsto_inv_nat_nhds_zero|theorem lintegral_tsum|theorem lintegral_indicator_const|theorem addHaar_closedBall |theorem measure_closedBall_lt_top|theorem measure_closedBall_pos|theorem lintegral_const_mul |theorem Measurable.ennreal_tsum|theorem finrank_euclideanSpace_fin' mathlib/Mathlib`
- `rg -n 'ediam_closure|diam_closure' mathlib/Mathlib/Topology`
- `rg -n 'theorem ediam_image_le' mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `rg -n -i 'eilenberg|coarea inequality|upper integral' simongmt/Poincare mathlib/Mathlib`
- `rg -ln for the terms 1.9, 1.8, hausdorffMeasure_image_le, μH[ in simongmt/Poincare/SimonGMT/Chapter01, Chapter02, Chapter03`
- `rg -n '^theorem|^lemma' simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean simongmt/Poincare/SimonGMT/Chapter02/LipschitzMeasurability.lean simongmt/Poincare/SimonGMT/Chapter02/UpperIntegral.lean`
- `grep -rl hausdorffMeasure_exists_cover_tsum_le_add / volume_closure_le_unitBall_mul_ediam_pow / eilenberg_hausdorff_upper_integral_of_ne_top over .humanize, simongmt/Poincare and mathlib/Mathlib (name-collision check)`
- `cmp snapshot project/GMT/Ch03/Contract.lean with workspace GMT/Ch03/Contract.lean`
- `lake env lean on scratch files replaying the Contract scope from gmt-compare.py contract_scope (elaboration and proofs of children and parent assembly)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/EMetricSpace/Diam.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/UpperIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/LipschitzMeasurability.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`

Snapshot is project d09bc8a with Mathlib 25730c7c; the snapshot Contract is byte-identical to the workspace Contract.

Available and used:
- Normalization: μHE[d] = addHaarScalarFactor(volume, μH[d]) • μH[d] (euclideanHausdorffMeasure_def). So μHE[d] S = c_d·μH[d] S by rfl, and c_d ≠ 0 by addHaarScalarFactor_volume_hausdorffMeasure_ne_zero.
- Hausdorff measure: hausdorffMeasure_apply (sup over r > 0 of inf over countable covers, with cost ⨆ _ : Nonempty, ediam^d), which gives child A; hausdorffMeasure_le_liminf_tsum with dependent countable index types, used for child C's pointwise bound.
- Diameter: Metric.ediam lives in namespace Metric, which the Contract does not open, so the statements write Metric.ediam. Also Metric.ediam_closure, Metric.diam_closure and LipschitzWith.ediam_image_le.
- Ball volume: Measure.addHaar_closedBall, whose right side is ofReal(r^finrank)·μ(ball 0 1); this is why Metric.ball appears in the frozen statements. Also finrank_euclideanSpace_fin, measure_ball_ne_top and Metric.measure_ball_pos.
- Integration: lintegral_liminf_le (Fatou), lintegral_tsum, lintegral_indicator_const, lintegral_const_mul, Measurable.liminf, Measurable.ennreal_tsum (a deprecated alias) and ENNReal.tendsto_inv_nat_nhds_zero.

No match: neither Mathlib nor SimonGMT has an Eilenberg/coarea inequality, a near-optimal Hausdorff cover lemma in ∃-form, or a lemma bounding volume by ωₘ·diamᵐ. SimonGMT Chapter02 has only Theorem 1.8(i) (hausdorffMeasure_image_le_of_lipschitzOn, nullMeasurableSet_image_of_lipschitzOn*) and the Remark 1.10 upper integral (UpperIntegral.lean). Neither is needed, because the frozen type asks for a measurable majorant directly.

The three proposed names collide with nothing in the run's .humanize tree, SimonGMT or Mathlib.

Scratch Lean checks: A and B proved; C proved from A and B; the parent proved from C; comparator-style exact Submission.X targets accepted; the parent uses only the axioms propext, Classical.choice and Quot.sound.
