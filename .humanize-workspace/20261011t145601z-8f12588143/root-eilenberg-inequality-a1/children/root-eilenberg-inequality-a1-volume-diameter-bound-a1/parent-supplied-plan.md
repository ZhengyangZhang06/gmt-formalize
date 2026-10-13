# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.eilenberg_inequality-a1.volume_diameter_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-eilenberg-inequality-a1-volume-diameter-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.eilenberg_inequality-a1`
- Child key: `volume_diameter_bound`
- Declaration: `Submission.volume_closure_le_unitBall_mul_ediam_pow`
- Exact Lean type: `∀ (m : ℕ) (S : Set (Rn m)), volume (closure S) ≤ volume (Metric.ball (0 : Rn m) 1) * Metric.ediam S ^ m`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
