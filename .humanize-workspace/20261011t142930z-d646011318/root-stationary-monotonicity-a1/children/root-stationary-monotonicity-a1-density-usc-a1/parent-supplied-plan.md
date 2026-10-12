# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.stationary_monotonicity-a1.density_usc-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-stationary-monotonicity-a1-density-usc-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.stationary_monotonicity-a1`
- Child key: `density_usc`
- Declaration: `Submission.stationary_density_usc_of_ratio_bound`
- Exact Lean type: `∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)), IsOpen U → IsFiniteMeasureOnCompacts V.weight → (∀ ξ ∈ U, V.HasDensityAt ξ (V.density ξ)) → (∀ (η : Ambient n ℓ) (R ρ : ℝ), closedBall η R ⊆ U → 0 < ρ → ρ < R → V.density η ≤ V.weight.real (closedBall η ρ) / (omega n * ρ ^ n)) → UpperSemicontinuousOn V.density U`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
