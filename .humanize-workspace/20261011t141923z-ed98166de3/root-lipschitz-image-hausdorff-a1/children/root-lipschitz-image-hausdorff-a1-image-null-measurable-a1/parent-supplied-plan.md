# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_image_hausdorff-a1.image_null_measurable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-lipschitz-image-hausdorff-a1-image-null-measurable-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_image_hausdorff-a1`
- Child key: `image_null_measurable`
- Declaration: `Submission.lipschitzImage_nullMeasurableSet_image`
- Exact Lean type: `∀ (X Y : Type) [MetricSpace X] [SigmaCompactSpace X] [MeasurableSpace X] [BorelSpace X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] (m : ℝ) (A : Set X) (f : X → Y) (K : ℝ≥0), 0 ≤ m → NullMeasurableSet A (Chapter01.simonHausdorffMeasureReal m) → Chapter01.simonHausdorffMeasureReal m A < ⊤ → LipschitzOnWith K f A → NullMeasurableSet (f '' A) (Chapter01.simonHausdorffMeasureReal m)`

## Sibling prerequisites

- `root.lipschitz_image_hausdorff-a1.image_measure_le-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
