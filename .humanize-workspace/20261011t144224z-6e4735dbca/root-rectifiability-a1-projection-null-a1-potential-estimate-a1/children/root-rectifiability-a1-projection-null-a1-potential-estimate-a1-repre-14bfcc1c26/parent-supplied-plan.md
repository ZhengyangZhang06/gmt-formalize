# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiability-a1.projection_null-a1.potential_estimate-a1.representation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1-potential-estimate-a1-repre-14bfcc1c26/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiability-a1.projection_null-a1.potential_estimate-a1`
- Child key: `representation`
- Declaration: `Submission.rpn_pe_kernel_representation`
- Exact Lean type: `∀ (m : ℕ) (a : Eucl (m + 1) → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a → ∀ y : Eucl (m + 1), ∑ j : Fin (m + 1), ∫ t, t j / (((m : ℝ) + 1) * (volume (ball (0 : Eucl (m + 1)) 1)).toReal * ‖t‖ ^ (m + 1)) * fderiv ℝ a (y - t) (EuclideanSpace.single j (1 : ℝ)) = a y`

## Sibling prerequisites

- `root.rectifiability-a1.projection_null-a1.potential_estimate-a1.polar_integral-a1`
- `root.rectifiability-a1.projection_null-a1.potential_estimate-a1.kernel_local_integrable-a1`
- `root.rectifiability-a1.projection_null-a1.potential_estimate-a1.convolution_smooth-a1`
- `root.rectifiability-a1.projection_null-a1.potential_estimate-a1.ray_ftc-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
