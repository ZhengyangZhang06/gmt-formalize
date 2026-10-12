# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.allard_lemma-a1.weighted_radial_monotonicity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-weighted-radial-monotonicity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.allard_lemma-a1`
- Child key: `weighted_radial_monotonicity`
- Declaration: `Submission.intcpt_allard_weighted_radial_monotonicity`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (W : Varifold N n U) (P : Grassmannian N n) (y : Euclidean N) (ε K M A : ℝ) (h : Euclidean N → ℝ) (φ : ℝ → ℝ), W.HasLocallyBoundedFirstVariation → ball y 1 ⊆ U → 0 < ε → 0 ≤ K → 0 ≤ M → (∀ r : ℝ, 0 < r → r < 1 → variationMeasure W (closedBall y r) ≤ ENNReal.ofReal ε * W.weight (closedBall y r)) → (∀ r : ℝ, 0 < r → r < 1 → (∫⁻ z in closedBall y r ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖ ∂W.measure) ≤ ENNReal.ofReal (ε * r ^ n)) → (∀ r : ℝ, 0 < r → r < 1 → W.weight (closedBall y r) ≤ ENNReal.ofReal (K * r ^ n)) → ContDiff ℝ 1 h → (∀ z, 0 ≤ h z ∧ h z ≤ 1) → (∀ (z : Euclidean N) (S : Grassmannian N n), |fderiv ℝ h z (Grassmannian.project S (z - y))| ≤ M * ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap S - Grassmannian.projectionLinearMap P)‖ * ‖z - y‖) → ContDiff ℝ 1 φ → Antitone φ → (∀ s, 0 ≤ φ s ∧ φ s ≤ 1) → 0 < A → A ≤ 2 → (∀ s, A ^ 2 ≤ s → φ s = 0) → ∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ → ρ * A < 1 → (∫ z, φ (‖z - y‖ ^ 2 / σ ^ 2) * h z ∂W.weight) / σ ^ n ≤ (∫ z, φ (‖z - y‖ ^ 2 / ρ ^ 2) * h z ∂W.weight) / ρ ^ n + 2 ^ (n + 1) * (M + K) * ε * ρ`

## Sibling prerequisites

- `root.integral_compactness-a1.allard_lemma-a1.first_variation_bound-a1`
- `root.integral_compactness-a1.allard_lemma-a1.radial_field_divergence-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
