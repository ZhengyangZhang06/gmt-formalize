# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_semicontinuity-a1.monotonicity_mass_lower_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-density-semicontinuity-a1-monotonicity-mass-lower-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_semicontinuity-a1`
- Child key: `monotonicity_mass_lower_bound`
- Declaration: `Submission.weight_closedBall_lower_bound_of_density_ge_one`
- Exact Lean type: `MonotonicityFormula → ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (ρ₀ Λ : ℝ) (θ : ℝ≥0∞), V.HasLocallyBoundedFirstVariation → 0 < ρ₀ → ball x ρ₀ ⊆ U → 0 ≤ Λ → (∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → variationMeasure V (closedBall x ρ) ≤ ENNReal.ofReal Λ * V.weight (closedBall x ρ)) → HasDensity n V.weight x θ → 1 ≤ θ → ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → ENNReal.ofReal (Real.exp (-(Λ * ρ))) * unitBallVolume n * ENNReal.ofReal ρ ^ n ≤ V.weight (closedBall x ρ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
