# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.radial_first_variation-a1.pointwise_divergence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-radial-first-variation-a1-pointwise-divergence-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.radial_first_variation-a1`
- Child key: `pointwise_divergence`
- Declaration: `Submission.tangentialDiv_weighted_radial_field`
- Exact Lean type: `∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (h : Ambient n ℓ → ℝ) (γ : ℝ → ℝ) (ξ x : Ambient n ℓ), Module.finrank ℝ (V.tangentSpace x) = n → DifferentiableAt ℝ h x → ContDiff ℝ 1 γ → V.tangentialDiv (fun y ↦ (h y * γ ‖y - ξ‖) • (y - ξ)) x = h x * ((n : ℝ) * γ ‖x - ξ‖ + ‖x - ξ‖ * deriv γ ‖x - ξ‖ * (1 - V.normalRadialSq ξ x)) + γ ‖x - ξ‖ * inner ℝ (x - ξ) (V.tangentialGradient h x)`

## Sibling prerequisites

- `root.radial_first_variation-a1.radial_derivative-a1`
- `root.radial_first_variation-a1.projection_trace-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
