# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.c1_approximation-a1.lusin_sigma_finite-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-c1-approximation-a1-lusin-sigma-finite-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.c1_approximation-a1`
- Child key: `lusin_sigma_finite`
- Declaration: `Submission.c1approx_lusin_closed_continuousOn`
- Exact Lean type: `∀ (n m : ℕ) (S : Set (Rn n)) (ν : Rn n → Rn m), MeasurableSet S → Measurable ν → ∀ ε : ℝ, 0 < ε → ∃ C ⊆ S, IsClosed C ∧ ContinuousOn ν C ∧ volume (S \ C) < ENNReal.ofReal ε`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
