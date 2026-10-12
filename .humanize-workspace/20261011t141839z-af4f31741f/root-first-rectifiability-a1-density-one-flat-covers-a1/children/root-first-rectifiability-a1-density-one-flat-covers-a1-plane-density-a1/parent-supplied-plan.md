# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.first_rectifiability-a1.density_one_flat_covers-a1.plane_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-density-one-flat-covers-a1-plane-density-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.first_rectifiability-a1.density_one_flat_covers-a1`
- Child key: `plane_density`
- Declaration: `Submission.frt_plane_subset_hasDensity_one`
- Exact Lean type: `∀ (N n : ℕ) (P : Grassmannian N n) (T : Set (Euclidean N)), T ⊆ (P.plane : Set (Euclidean N)) → ∃ Z : Set (Euclidean N), (μHE[n] : Measure (Euclidean N)) Z = 0 ∧ ∀ a ∈ T, a ∉ Z → HasDensity n ((μHE[n] : Measure (Euclidean N)).restrict T) a 1`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
