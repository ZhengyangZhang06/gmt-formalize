# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_image_hausdorff-a1.image_measure_le-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-lipschitz-image-hausdorff-a1-image-measure-le-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_image_hausdorff-a1`
- Child key: `image_measure_le`
- Declaration: `Submission.lipschitzImage_hausdorff_image_le`
- Exact Lean type: `∀ (X Y : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] (m : ℝ) (E : Set X) (f : X → Y) (K : ℝ≥0), 0 ≤ m → LipschitzOnWith K f E → Chapter01.simonHausdorffMeasureReal m (f '' E) ≤ (K : ℝ≥0∞) ^ m * Chapter01.simonHausdorffMeasureReal m E`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
