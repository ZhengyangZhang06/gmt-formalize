# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.section3_consequences-a1.chart_projection_positive-a1.antilipschitz_measure_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-section3-consequences-a1-chart-projection-positive-a1-antilipsch-891ac20fd1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.section3_consequences-a1.chart_projection_positive-a1`
- Child key: `antilipschitz_measure_bound`
- Declaration: `Submission.section3_antilipschitzOn_volume_le_euclideanHausdorff_image`
- Exact Lean type: `∀ (n p : ℕ) (f : Rn n → Rn p) (S : Set (Rn n)) (K : ℝ≥0), (∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ K * ‖f x - f y‖) → volume S ≤ (K : ℝ≥0∞) ^ n * μHE[n] (f '' S)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
