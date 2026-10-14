# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.regular_point_density-a1`
- Child DAG node: `root.dimension_reduction_results-a1.regular_point_density-a1.bilipschitz_measure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the measure comparison used in step 4 of the supplied parent proof ("H^n(M ∩ B_s(z)) = ω_n s^n(1 + o(1))"). In this decomposition the graph and area-formula computation of step 4 is replaced by a bi-Lipschitz squeeze, and this lemma is the measure-theoretic half of it.
Notation. μH[d] is Mathlib's Hausdorff measure. By definition (Measure.euclideanHausdorffMeasure_def), μHE[n] = c·μH[n] on every metric space, with the same constant c := addHaarScalarFactor(volume on EuclideanSpace ℝ (Fin n), μH[n]) ∈ [0, ∞). On ℝ^n itself, μHE[n] = volume (EuclideanSpace.euclideanHausdorffMeasure_eq_volume).
1. (Upper bound.) By hypothesis, χ is c₂-Lipschitz on E (LipschitzOnWith.of_dist_le_mul). By the Lipschitz image inequality for Hausdorff measures (LipschitzOnWith.hausdorffMeasure_image_le with d = n ≥ 0), μH[n](χ(E)) ≤ c₂ⁿ·μH[n](E). Multiplying by c gives μHE[n](χ(E)) ≤ c₂ⁿ·μHE[n](E) = c₂ⁿ·volume(E). Here c₂ⁿ = ofReal(c₂ⁿ) = (toNNReal c₂)^(n : ℝ) in [0, ∞].
2. (χ is injective on E.) If a, b ∈ E and χ(a) = χ(b), then c₁|a − b| ≤ 0. Since c₁ > 0, this forces a = b.
3. (Lower bound.) Let g := invFunOn χ E. By step 2, g(χ(a)) = a for all a ∈ E (InjOn.leftInvOn_invFunOn). Hence g maps χ(E) onto E (LeftInvOn.image_image). For a, b ∈ E, |g(χ(a)) − g(χ(b))| = |a − b| ≤ c₁⁻¹|χ(a) − χ(b)|, so g is c₁⁻¹-Lipschitz on χ(E). The Lipschitz image inequality gives μH[n](E) = μH[n](g(χ(E))) ≤ c₁^{−n}·μH[n](χ(E)). Multiply by c and by c₁ⁿ ∈ (0, ∞): c₁ⁿ·volume(E) = c₁ⁿ·μHE[n](E) ≤ μHE[n](χ(E)).
4. Steps 1 and 3 together are the claim.

Lean reference proof (verified). The declaration below was compiled with `lake env lean` (Lean v4.35.0-rc3, Mathlib 25730c7c) inside a copy of GMT/Ch07/Submission.lean at this node's proof base (ee11750), placed after the contract definitions (namespace GMT.Ch07, contract `open`s, noncomputable section). `#print axioms` reports only propext, Classical.choice and Quot.sound. It follows the numbered proof above step by step.

```lean
theorem Submission.dimred_rpd_bilipschitz_image_measure : ∀ (P n : ℕ) (χ : Euclid n → Euclid P) (E : Set (Euclid n)) (c₁ c₂ : ℝ), 0 < c₁ → 0 ≤ c₂ → (∀ a ∈ E, ∀ b ∈ E, c₁ * ‖a - b‖ ≤ ‖χ a - χ b‖ ∧ ‖χ a - χ b‖ ≤ c₂ * ‖a - b‖) → ENNReal.ofReal (c₁ ^ n) * volume E ≤ μHE[n] (χ '' E) ∧ μHE[n] (χ '' E) ≤ ENNReal.ofReal (c₂ ^ n) * volume E := by
  intro P n χ E c₁ c₂ hc₁ hc₂ h
  have hvol : (volume : Measure (Euclid n)) = μHE[n] := (EuclideanSpace.euclideanHausdorffMeasure_eq_volume n).symm
  have hscale : ∀ {X : Type} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (S : Set X),
      (μHE[n] : Measure X) S = (Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin n))) μH[n] : ℝ≥0∞) * μH[(n : ℝ)] S := by
    intro X _ _ _ S
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  constructor
  · have hinj : InjOn χ E := by
      intro a ha b hb hab
      have := (h a ha b hb).1
      rw [hab, sub_self, norm_zero] at this
      have : ‖a - b‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (a - b)]) (norm_nonneg _)
      exact sub_eq_zero.1 (norm_eq_zero.1 this)
    set g := Function.invFunOn χ E
    have hleft : LeftInvOn g χ E := hinj.leftInvOn_invFunOn
    have hgL : LipschitzOnWith (Real.toNNReal c₁⁻¹) g (χ '' E) := by
      apply LipschitzOnWith.of_dist_le_mul
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [hleft ha, hleft hb, dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (inv_nonneg.2 hc₁.le)]
      have := (h a ha b hb).1
      rw [inv_mul_eq_div, le_div_iff₀ hc₁]
      linarith
    have himg : g '' (χ '' E) = E := hleft.image_image
    have hle := hgL.hausdorffMeasure_image_le (d := (n : ℝ)) (Nat.cast_nonneg n)
    rw [himg] at hle
    rw [hvol, hscale, hscale (χ '' E)]
    set c : ℝ≥0∞ := (Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin n))) μH[n] : ℝ≥0∞)
    have hK : ((Real.toNNReal c₁⁻¹ : NNReal) : ℝ≥0∞) ^ (n : ℝ) = ENNReal.ofReal (c₁ ^ n)⁻¹ := by
      rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ (inv_nonneg.2 hc₁.le),
        ← ENNReal.ofReal_pow (inv_nonneg.2 hc₁.le), inv_pow]
    rw [hK] at hle
    have hpos : ENNReal.ofReal (c₁ ^ n) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos hc₁ n)).ne'
    have hinv : ENNReal.ofReal (c₁ ^ n)⁻¹ = (ENNReal.ofReal (c₁ ^ n))⁻¹ :=
      ENNReal.ofReal_inv_of_pos (pow_pos hc₁ n)
    rw [hinv] at hle
    calc ENNReal.ofReal (c₁ ^ n) * (c * μH[(n : ℝ)] E)
        ≤ ENNReal.ofReal (c₁ ^ n) * (c * ((ENNReal.ofReal (c₁ ^ n))⁻¹ * μH[(n : ℝ)] (χ '' E))) := by
          gcongr
      _ = c * μH[(n : ℝ)] (χ '' E) := by
          rw [← mul_assoc, mul_comm (ENNReal.ofReal (c₁ ^ n)) c, mul_assoc, ← mul_assoc (ENNReal.ofReal (c₁ ^ n)),
            ENNReal.mul_inv_cancel hpos ENNReal.ofReal_ne_top, one_mul]
  · have hL : LipschitzOnWith (Real.toNNReal c₂) χ E := by
      apply LipschitzOnWith.of_dist_le_mul
      intro a ha b hb
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hc₂]
      exact (h a ha b hb).2
    have hle := hL.hausdorffMeasure_image_le (d := (n : ℝ)) (Nat.cast_nonneg n)
    rw [hvol, hscale, hscale E]
    have hK : ((Real.toNNReal c₂ : NNReal) : ℝ≥0∞) ^ (n : ℝ) = ENNReal.ofReal (c₂ ^ n) := by
      rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hc₂,
        ← ENNReal.ofReal_pow hc₂]
    rw [hK] at hle
    calc _ ≤ (Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin n))) μH[n] : ℝ≥0∞) *
          (ENNReal.ofReal (c₂ ^ n) * μH[(n : ℝ)] E) := by gcongr
      _ = _ := by ring
```

## Key steps

1. μHE[n] = c·μH[n] with one constant c on every metric space, and μHE[n] = volume on ℝⁿ.
2. Upper bound: the Lipschitz image inequality for χ (constant c₂).
3. Lower bound: χ is injective on E, and its inverse on χ(E) is c₁⁻¹-Lipschitz; apply the Lipschitz image inequality to it.

## Reference use

### local-project

Queries:
- `sha256sum GMT/Ch07/Contract.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean; diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical; manifest pins project b4d606d, mathlib 25730c7c)`
- `grep -n 'def massOn|def massAdmissibleOn|covectorEuclideanNorm|le_massOn' simongmt/Poincare/SimonGMT/Chapter06/Mass.lean; grep -n 'zeroRegion|def GeometricCurrentOn.support|VanishesOn' Chapter06/CurrentLocalEquality.lean; grep -n 'TestFormOn|structure GeometricCurrentOn' Chapter06/Currents.lean; grep -n 'IsTestForm|DifferentialForm|Covector' Chapter06/Forms.lean`
- `sed -n 1,200p <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (euclideanHausdorffMeasure_def, euclideanHausdorffMeasure_zero, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Isometry.euclideanHausdorffMeasure_image)`
- `grep -n 'hausdorffMeasure_image_le|hausdorffMeasure_zero_singleton' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `grep -rn 'InnerRegularCompactLTTop|exists_isCompact_sdiff_lt' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean Mathlib/MeasureTheory/Measure/RegularityCompacts.lean; Lean: `μHE[n].InnerRegularCompactLTTop` fails under the contract imports but `(μHE[n].restrict A).InnerRegularCompactLTTop` succeeds for finite restrictions`
- `grep -n 'setIntegral_eq_zero_of_forall_eq_zero|setIntegral_union|setIntegral_ge_of_const_le_real|norm_setIntegral_le_of_norm_le_const' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `grep -rn 'theorem ContDiffAt.hasStrictFDerivAt|theorem addHaar_ball_of_pos|theorem IsOpen.inter_closure|theorem IsCompact.image_of_continuousOn|theorem finrank_euclideanSpace_fin|theorem LinearMap.finrank_range_of_inj|theorem invFunOn_eq' <snapshot>/mathlib/Mathlib`
- `grep -n '^theorem|^def' simongmt/Poincare/SimonGMT/Chapter02/{Submanifold,SubmanifoldTopology,AreaFormula,AreaNormalization}.lean (IsSimonLocalRepresentation, isEmbedding_chartMap, injective_area_formula_of_injective_derivative; none imported by the contract)`
- `python3 over dag.json: nodes whose lean_statement mentions IsEmbeddedSubmanifold, regularSet, covectorEuclideanNorm, IsUnitOrientationOf, μHE or massOn; accepted statuses; duplicate lean_names; grep -c dimred_rpd dag.json (0)`
- `git diff <proof_base> <candidate> -- GMT/Ch07/Submission.lean for 9c8432cb (dor_ims_unitOrientation_dual), 89e4c45c (dor_ims_smooth_unit_approx + dor_ims_sua_* helpers), 5e4b2158 (dsmc_chart_inverse_continuity): pure additions after RegularComponentsAreMinimizing`
- `nodes/root-dimension-reduction-results-a1-one-dim-cones-a1/decomposition-v2.json (sibling precedent for reusing accepted declarations)`
- `lake env lean /tmp/rpd-check/Check.lean (types + assembly); /tmp/rpd-check/{C1,C4,C7}.lean; /tmp/rpd-final/Final.lean (stubs for reused); /tmp/rpd-final/Full.lean and /tmp/rpd-final/SubmissionCopy.lean (accepted reused proofs spliced in; #print axioms = propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaFormula.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaNormalization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Neighborhoods.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-unit-or-24edf309fb/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-smooth-49478a38c9/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ch-0f11358db9/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-one-dim-cones-a1/decomposition-v2.json`
- `/tmp/rpd-final/Final.lean`
- `/tmp/rpd-final/SubmissionCopy.lean`

Pins match: the snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean (sha256 e4148e7f…), and the manifest pins project b4d606d and mathlib 25730c7c.

Available under the contract imports:
- μHE[d] = c_d·μH[d] with one constant on every metric space, and μHE[n] = volume on Euclid n;
- LipschitzOnWith.hausdorffMeasure_image_le;
- ContDiffAt.hasStrictFDerivAt;
- Measure.addHaar_ball_of_pos;
- inner regularity (InnerRegularCompactLTTop) for finite restrictions μHE[n]⌞A, though not for μHE[n] itself.

Not available: SimonGMT's chart-embedding and area-formula modules (Chapter02) are not imported by the contract. No library lemma gives the mass of a local m₀[[M]] current or the density of a C¹ submanifold.

Reused building blocks: Submission.dor_ims_unitOrientation_dual, Submission.dor_ims_smooth_unit_approx and Submission.dsmc_chart_inverse_continuity are accepted DAG nodes with candidate commits. Their frozen types are reused byte-for-byte, following the sibling precedent one_dim_cones-a1 v2. No new name collides: there are 0 hits for dimred_rpd_.

Lean evidence: all child types and the parent assembly elaborate. With the accepted reused proofs spliced in, the selected theorem compiles inside a copy of Submission.lean with axioms propext, Classical.choice and Quot.sound only.
