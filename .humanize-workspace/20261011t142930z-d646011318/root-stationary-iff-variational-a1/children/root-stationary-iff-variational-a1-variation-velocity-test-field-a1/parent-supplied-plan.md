# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.stationary_iff_variational-a1.variation_velocity_test_field-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-stationary-iff-variational-a1-variation-velocity-test-field-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.stationary_iff_variational-a1`
- Child key: `variation_velocity_test_field`
- Declaration: `Submission.compactVariation_velocity_isTestField`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Ambient n ℓ)) (φ : ℝ → Ambient n ℓ → Ambient n ℓ) (ε : ℝ) (K : Set (Ambient n ℓ)), IsCompactVariation φ ε K → K ⊆ U → IsTestField U (fun y ↦ deriv (fun t ↦ φ t y) 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
