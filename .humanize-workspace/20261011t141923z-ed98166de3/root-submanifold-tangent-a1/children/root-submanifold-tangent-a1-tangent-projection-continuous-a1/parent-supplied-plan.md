# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.submanifold_tangent-a1.tangent_projection_continuous-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-submanifold-tangent-a1-tangent-projection-continuous-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.submanifold_tangent-a1`
- Child key: `tangent_projection_continuous`
- Declaration: `Submission.simon_submanifold_tangentProjection_continuousOn`
- Exact Lean type: `∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)), Chapter02.IsSimonSubmanifold (E := Rn n) r M → ContinuousOn (tangentProjection M) M`

## Sibling prerequisites

- `root.submanifold_tangent-a1.chart_inverse_continuous-a1`
- `root.submanifold_tangent-a1.tangent_space_eq_range-a1`
- `root.submanifold_tangent-a1.range_projection_continuous-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
