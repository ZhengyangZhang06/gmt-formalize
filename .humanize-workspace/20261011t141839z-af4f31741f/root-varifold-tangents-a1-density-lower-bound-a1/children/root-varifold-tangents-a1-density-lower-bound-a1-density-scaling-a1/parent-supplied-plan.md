# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.varifold_tangents-a1.density_lower_bound-a1.density_scaling-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-varifold-tangents-a1-density-lower-bound-a1-density-scaling-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.varifold_tangents-a1.density_lower_bound-a1`
- Child key: `density_scaling`
- Declaration: `Submission.varifold_tangents_dlb_hasDensity_of_closedBall_scaling`
- Exact Lean type: `∀ (N n : ℕ) (μ ν : Measure (Euclidean N)) (y z : Euclidean N) (t δ : ℝ) (c θ : ℝ≥0∞), 0 < t → 0 < δ → c ≠ ∞ → (∀ ρ : ℝ, 0 < ρ → ρ < δ → ν (closedBall y ρ) = c * (ENNReal.ofReal (t⁻¹ ^ n) * μ (closedBall z (t * ρ)))) → HasDensity n μ z θ → HasDensity n ν y (c * θ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
