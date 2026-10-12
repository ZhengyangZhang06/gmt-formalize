# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.mean_curvature_of_stationary-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-mean-curvature-of-stationary-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1`
- Child key: `mean_curvature_of_stationary`
- Declaration: `Submission.meanCurvature_bounded_of_stationaryAlong`
- Exact Lean type: `∀ (P n d : ℕ) (U N : Set (Euclid P)) (R : IMRep U n), IsOpen U → IsEmbeddedSubmanifold 2 d N → (closure N \ N) ∩ U = ∅ → μHE[n] (R.carrier \ N) = 0 → R.IsStationaryAlong N → R.HasLocallyBoundedMeanCurvature`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.chart_tangent_space-a1`
- `root.minimizing_implies_stationary-a1.tangent_projection_measurable-a1`
- `root.minimizing_implies_stationary-a1.approx_tangent_in_submanifold-a1`
- `root.minimizing_implies_stationary-a1.tangent_projection_extension-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
