# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.radial_first_variation-a1.radial_derivative-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-radial-first-variation-a1-radial-derivative-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.radial_first_variation-a1`
- Child key: `radial_derivative`
- Declaration: `Submission.radial_vector_field_hasFDerivAt`
- Exact Lean type: `∀ (n ℓ : ℕ) (γ : ℝ → ℝ) (ξ x : Ambient n ℓ), ContDiff ℝ 1 γ → HasFDerivAt (fun y : Ambient n ℓ ↦ γ ‖y - ξ‖ • (y - ξ)) (γ ‖x - ξ‖ • ContinuousLinearMap.id ℝ (Ambient n ℓ) + (deriv γ ‖x - ξ‖ / ‖x - ξ‖) • (innerSL ℝ (x - ξ)).smulRight (x - ξ)) x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
