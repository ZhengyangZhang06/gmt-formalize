# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.eilenberg_inequality-a1.covering_majorant-a1.lipschitz_image_volume-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-eilenberg-inequality-a1-covering-majorant-a1-lipschitz-image-volume-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.eilenberg_inequality-a1.covering_majorant-a1`
- Child key: `lipschitz_image_volume`
- Declaration: `Submission.eilenberg_covering_lipschitz_image_volume_le`
- Exact Lean type: `∀ (X : Type) [MetricSpace X] (m : ℕ) (D : Set X) (f : X → Rn m) (K : ℝ≥0), LipschitzOnWith K f D → volume (closure (f '' D)) ≤ Chapter01.realUnitBallVolume (m : ℝ) * (K : ℝ≥0∞) ^ m * ediam D ^ m / (2 : ℝ≥0∞) ^ m`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
