# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.isoperimetric-a1.lattice_mass_lower_bound-a1.coord_covector-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-isoperimetric-a1-lattice-mass-lower-bound-a1-coord-covector-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.isoperimetric-a1.lattice_mass_lower_bound-a1`
- Child key: `coord_covector`
- Declaration: `Submission.isoperimetric_coord_covector_eval`
- Exact Lean type: `∀ (n N : ℕ) (α : SimonMultiIndex n N), (wedgeCovectors n (fun i => EuclideanSpace.proj (α i)) : Covector (Eucl N) n) (fun j => EuclideanSpace.single (α j) (1 : ℝ)) = 1 ∧ (∀ α' : SimonMultiIndex n N, α' ≠ α → (wedgeCovectors n (fun i => EuclideanSpace.proj (α i)) : Covector (Eucl N) n) (fun j => EuclideanSpace.single (α' j) (1 : ℝ)) = 0) ∧ ∀ c : ℝ, covectorEuclideanNorm (c • (wedgeCovectors n (fun i => EuclideanSpace.proj (α i)) : Covector (Eucl N) n)) = |c|`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
