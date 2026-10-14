# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.chart_image_rectifiable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1-chart-ima-e2d21dad87/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1`
- Child key: `chart_image_rectifiable`
- Declaration: `Submission.lpf_pi_chart_image_rectifiable`
- Exact Lean type: `∀ (Q n : ℕ) (G : Eucl n → Eucl Q) (O : Set (Eucl n)), IsOpen O → ContDiffOn ℝ 1 G O → CountablyRectifiable n (G '' O)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
