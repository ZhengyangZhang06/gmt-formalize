# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.section3_consequences-a1.coordinate_projection_injective-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-section3-consequences-a1-coordinate-projection-injective-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.section3_consequences-a1`
- Child key: `coordinate_projection_injective`
- Declaration: `Submission.section3_exists_coordinateProjection_injOn`
- Exact Lean type: `∀ (N n : ℕ) (L : Submodule ℝ (Rn N)), finrank ℝ L = n → ∃ J : Finset (Fin N), J.card = n ∧ Set.InjOn (coordinateProjection J) (L : Set (Rn N))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
