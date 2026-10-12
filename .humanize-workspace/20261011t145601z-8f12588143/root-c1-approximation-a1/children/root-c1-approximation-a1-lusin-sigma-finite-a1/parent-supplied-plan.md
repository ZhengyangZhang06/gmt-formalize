# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.c1_approximation-a1.lusin_sigma_finite-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-c1-approximation-a1-lusin-sigma-finite-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.c1_approximation-a1`
- Child key: `lusin_sigma_finite`
- Declaration: `Submission.lusin_closed_subset_continuousOn_volume`
- Exact Lean type: `∀ (n : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (u : Rn n → F) (S : Set (Rn n)), Measurable u → MeasurableSet S → ∀ ε : ℝ≥0∞, 0 < ε → ∃ C ⊆ S, IsClosed C ∧ volume (S \ C) < ε ∧ ContinuousOn u C`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
