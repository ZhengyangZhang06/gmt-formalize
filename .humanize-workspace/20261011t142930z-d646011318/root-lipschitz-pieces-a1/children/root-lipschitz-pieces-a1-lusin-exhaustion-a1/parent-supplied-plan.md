# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pieces-a1.lusin_exhaustion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-lipschitz-pieces-a1-lusin-exhaustion-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pieces-a1`
- Child key: `lusin_exhaustion`
- Declaration: `Submission.lusin_compact_exhaustion_of_measurable`
- Exact Lean type: `∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y] (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → Y) (S : Set (EuclideanSpace ℝ (Fin n))), Measurable g → MeasurableSet S → volume S ≠ ⊤ → ∃ C : ℕ → Set (EuclideanSpace ℝ (Fin n)), (∀ j, IsCompact (C j) ∧ C j ⊆ S ∧ ContinuousOn g (C j)) ∧ volume (S \ ⋃ j, C j) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
