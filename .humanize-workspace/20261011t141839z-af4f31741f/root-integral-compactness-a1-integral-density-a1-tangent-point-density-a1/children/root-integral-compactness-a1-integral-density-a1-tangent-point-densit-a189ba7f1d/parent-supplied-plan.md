# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.integral_density-a1.tangent_point_density-a1.ball_sandwich-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-integral-density-a1-tangent-point-densit-a189ba7f1d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.integral_density-a1.tangent_point_density-a1`
- Child key: `ball_sandwich`
- Declaration: `Submission.intcpt_id_tpd_ball_sandwich`
- Exact Lean type: `∀ (N n : ℕ) (M : Set (Euclidean N)) (θ : Euclidean N → ℝ) (x : Euclidean N) (f : C_c(Euclidean N, ℝ)) (r₀ a R r : ℝ), NullMeasurableSet M (μHE[n] : Measure (Euclidean N)) → (∀ y ∈ M, 0 ≤ θ y) → IntegrableOn θ (M ∩ closedBall x r₀) μHE[n] → (∀ y, 0 ≤ f y) → (∀ y, f y ≤ 1) → (∀ y, ‖y‖ ≤ a → f y = 1) → (∀ y, R < ‖y‖ → f y = 0) → 0 < r → r * R ≤ r₀ → (((μHE[n] : Measure (Euclidean N)).restrict M).withDensity fun y ↦ ENNReal.ofReal (θ y)) (closedBall x (r * a)) ≤ ENNReal.ofReal (r ^ n * ∫ y in Chapter03.blowUpMap x r '' M, f y * θ (x + r • y) ∂μHE[n]) ∧ ENNReal.ofReal (r ^ n * ∫ y in Chapter03.blowUpMap x r '' M, f y * θ (x + r • y) ∂μHE[n]) ≤ (((μHE[n] : Measure (Euclidean N)).restrict M).withDensity fun y ↦ ENNReal.ofReal (θ y)) (closedBall x (r * R))`

## Sibling prerequisites

- `root.integral_compactness-a1.integral_density-a1.tangent_point_density-a1.blowup_cov-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
