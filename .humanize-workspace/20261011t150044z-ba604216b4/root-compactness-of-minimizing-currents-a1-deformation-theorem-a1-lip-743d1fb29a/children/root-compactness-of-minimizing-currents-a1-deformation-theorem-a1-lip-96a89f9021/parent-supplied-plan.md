# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.piece_current-a1.measurable_inverse-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-96a89f9021/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.piece_current-a1`
- Child key: `measurable_inverse`
- Declaration: `Submission.cmcdt_lpi_pc_measurable_inverse`
- Exact Lean type: `∀ (P n : ℕ) (H : Euclid n → Euclid P) (B : Set (Euclid n)), ContinuousOn H B → MeasurableSet B → InjOn H B → MeasurableSet (H '' B) ∧ ∃ h : Euclid P → Euclid n, Measurable h ∧ ∀ u ∈ B, h (H u) = u`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
