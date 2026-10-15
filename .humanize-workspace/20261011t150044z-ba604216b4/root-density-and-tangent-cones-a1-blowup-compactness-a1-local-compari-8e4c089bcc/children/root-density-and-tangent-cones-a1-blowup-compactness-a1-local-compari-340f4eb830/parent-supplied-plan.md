# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.boundary_im-a1.layers-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-340f4eb830/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.boundary_im-a1`
- Child key: `layers`
- Declaration: `Submission.dtc_bc_lc_fd_bim_layers`
- Exact Lean type: `∀ (n : ℕ) (R : GeometricCurrentOn (univ : Set (Euclid (n + 1))) (n + 1)), IsIntegerMultiplicity R → IsCompact R.support → ∃ (U : ℤ → Set (Euclid (n + 1))) (X : ℤ → GeometricCurrentOn (univ : Set (Euclid (n + 1))) (n + 1)), (∀ j, MeasurableSet (U j)) ∧ (∀ j, U (j + 1) ⊆ U j) ∧ (∀ (j : ℤ) (ω : TestFormOn (univ : Set (Euclid (n + 1))) (n + 1)), X j ω = ∫ x in U j, (ω : DifferentialForm (Euclid (n + 1)) (n + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ))) ∧ (∀ η : TestFormOn (univ : Set (Euclid (n + 1))) n, HasSum (fun j => (X j).boundary η) (R.boundary η)) ∧ (∀ j, (X j).boundary.mass ≤ R.boundary.mass) ∧ ∀ (N : ℕ) (Y : GeometricCurrentOn (univ : Set (Euclid (n + 1))) n), (∀ η : TestFormOn (univ : Set (Euclid (n + 1))) n, Y η = ∑ j ∈ Finset.Icc (-(N : ℤ)) N, (X j).boundary η) → Y.mass ≤ R.boundary.mass`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.vanish_off_support-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.sobolev_perimeter-a1.mollify_variation-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
