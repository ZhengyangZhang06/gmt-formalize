# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.besicovitch_federer-a1.infinite_fibres-a1.hausdorff_zero_counting-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-besicovitch-federer-a1-infinite-fibres-a1-hausdorff-zero-counting-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.besicovitch_federer-a1.infinite_fibres-a1`
- Child key: `hausdorff_zero_counting`
- Declaration: `Submission.bf_hausdorffZero_eq_encard`
- Exact Lean type: `∀ (N : ℕ) (S : Set (Rn N)), μHE[0] S = (S.encard : ℝ≥0∞)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
