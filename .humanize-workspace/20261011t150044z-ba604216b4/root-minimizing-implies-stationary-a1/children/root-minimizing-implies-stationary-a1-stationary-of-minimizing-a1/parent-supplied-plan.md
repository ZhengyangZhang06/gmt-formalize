# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.stationary_of_minimizing-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-stationary-of-minimizing-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1`
- Child key: `stationary_of_minimizing`
- Declaration: `Submission.stationaryAlong_of_minimizing_in_submanifold`
- Exact Lean type: `∀ (P n d : ℕ) (U N : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → IsEmbeddedSubmanifold 2 d N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (N ∩ U) → BoundaryVanishes T → R.Represents T → μHE[n] (R.carrier \ N) = 0 → R.IsStationaryAlong N`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.mass_equals_measure-a1`
- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1`
- `root.minimizing_implies_stationary-a1.tangential_deformation-a1`
- `root.minimizing_implies_stationary-a1.first_variation_mass_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
