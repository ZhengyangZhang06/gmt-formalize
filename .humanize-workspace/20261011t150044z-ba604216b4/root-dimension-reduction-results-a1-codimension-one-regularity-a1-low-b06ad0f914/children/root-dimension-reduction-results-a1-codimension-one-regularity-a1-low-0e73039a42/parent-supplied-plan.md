# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.low_density_regular-a1.stationary_of_minimizing-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-low-0e73039a42/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.low_density_regular-a1`
- Child key: `stationary_of_minimizing`
- Declaration: `Submission.codim1_ldr_stationaryAlong_of_minimizing`
- Exact Lean type: `∀ (P n d : ℕ) (U N : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → IsEmbeddedSubmanifold 2 d N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (N ∩ U) → BoundaryVanishes T → R.Represents T → μHE[n] (R.carrier \ N) = 0 → R.IsStationaryAlong N`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.low_density_regular-a1.diffeo_pushforward-a1`
- `root.minimizing_implies_stationary-a1.tangential_deformation-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.low_density_regular-a1.first_variation_mass_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
