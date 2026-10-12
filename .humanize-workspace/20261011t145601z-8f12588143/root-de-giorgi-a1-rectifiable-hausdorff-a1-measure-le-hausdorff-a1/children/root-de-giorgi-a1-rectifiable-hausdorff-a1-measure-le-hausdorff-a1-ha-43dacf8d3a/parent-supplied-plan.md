# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.rectifiable_hausdorff-a1.measure_le_hausdorff-a1.hausdorff_normalization-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-rectifiable-hausdorff-a1-measure-le-hausdorff-a1-ha-43dacf8d3a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.rectifiable_hausdorff-a1.measure_le_hausdorff-a1`
- Child key: `hausdorff_normalization`
- Declaration: `Submission.deGiorgiRH_unitBall_mul_hausdorffMeasure_eq_two_pow_mul`
- Exact Lean type: `∀ (n N : ℕ) (s : Set (Rn N)), volume (Metric.ball (0 : Rn n) 1) * μH[(n : ℝ)] s = 2 ^ n * μHE[n] s`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
