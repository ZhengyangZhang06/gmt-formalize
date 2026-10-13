# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiability-a1.projection_null-a1.potential_estimate-a1.ray_ftc-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1-potential-estimate-a1-ray-ftc-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiability-a1.projection_null-a1.potential_estimate-a1`
- Child key: `ray_ftc`
- Declaration: `Submission.rpn_pe_ray_ftc`
- Exact Lean type: `∀ (n : ℕ) (a : Eucl n → ℝ), ContDiff ℝ 1 a → HasCompactSupport a → ∀ y θ : Eucl n, θ ≠ 0 → ∫ r in Ioi (0 : ℝ), fderiv ℝ a (y - r • θ) θ = a y`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
