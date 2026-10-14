# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.boundary_rectifiability-a1.finite_mass_boundary_im-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-finite-mass-boundary-im-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.boundary_rectifiability-a1`
- Child key: `finite_mass_boundary_im`
- Declaration: `Submission.br_boundary_isIntegerMultiplicity_of_finite_mass`
- Exact Lean type: `DeformationTheorem → IntegralityOfWeakLimits → ∀ (P m : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), IsIntegerMultiplicity X → X.mass < ∞ → X.boundary.mass < ∞ → IsIntegerMultiplicity X.boundary`

## Sibling prerequisites

- `root.boundary_rectifiability-a1.zero_dim_weak_limit-a1`
- `root.boundary_rectifiability-a1.lattice_boundary_im-a1`
- `root.boundary_rectifiability-a1.lattice_approximation-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
