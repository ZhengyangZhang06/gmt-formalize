# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.allard_lemma-a1.cylinder_monotonicity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-cylinder-monotonicity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.allard_lemma-a1`
- Child key: `cylinder_monotonicity`
- Declaration: `Submission.intcpt_allard_cylinder_monotonicity`
- Exact Lean type: `∀ (N n : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Set (Euclidean N)) (W : Varifold N n U) (P : Grassmannian N n) (y : Euclidean N) (ε K : ℝ), W.HasLocallyBoundedFirstVariation → ball y 1 ⊆ U → 0 < ε → 0 ≤ K → (∀ r : ℝ, 0 < r → r < 1 → variationMeasure W (closedBall y r) ≤ ENNReal.ofReal ε * W.weight (closedBall y r)) → (∀ r : ℝ, 0 < r → r < 1 → (∫⁻ z in closedBall y r ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖ ∂W.measure) ≤ ENNReal.ofReal (ε * r ^ n)) → (∀ r : ℝ, 0 < r → r < 1 → W.weight (closedBall y r) ≤ ENNReal.ofReal (K * r ^ n)) → ∀ τ σ ρ : ℝ, 0 < τ → τ ≤ 1 → 0 < σ → σ ≤ ρ → ρ < 1 → W.weight (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) / ENNReal.ofReal σ ^ n ≤ W.weight (closedBall y ρ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 2 * τ}) / ENNReal.ofReal ρ ^ n + ENNReal.ofReal (C * (1 + K) * ε * ρ / τ)`

## Sibling prerequisites

- `root.integral_compactness-a1.allard_lemma-a1.weighted_radial_monotonicity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
