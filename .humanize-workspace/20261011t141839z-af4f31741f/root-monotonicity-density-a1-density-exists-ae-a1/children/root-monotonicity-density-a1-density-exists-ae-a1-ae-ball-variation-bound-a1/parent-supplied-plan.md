# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.monotonicity_density-a1.density_exists_ae-a1.ae_ball_variation_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-monotonicity-density-a1-density-exists-ae-a1-ae-ball-variation-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.monotonicity_density-a1.density_exists_ae-a1`
- Child key: `ae_ball_variation_bound`
- Declaration: `Submission.dea_ae_variationMeasure_ball_bound`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U), V.HasLocallyBoundedFirstVariation → ∀ᵐ x ∂V.weight, ∃ R Λ : ℝ, 0 < R ∧ 0 ≤ Λ ∧ closedBall x R ⊆ U ∧ ∀ r : ℝ, 0 < r → r < R → variationMeasure V (closedBall x r) ≤ ENNReal.ofReal Λ * V.weight (closedBall x r)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
