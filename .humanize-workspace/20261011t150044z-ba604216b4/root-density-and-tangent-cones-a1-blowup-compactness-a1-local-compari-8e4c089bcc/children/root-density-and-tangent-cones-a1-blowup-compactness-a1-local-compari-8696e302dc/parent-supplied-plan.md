# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.boundary_im-a1.nested_im-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-8696e302dc/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.boundary_im-a1`
- Child key: `nested_im`
- Declaration: `Submission.dtc_bc_lc_fd_bim_nested_im`
- Exact Lean type: `∀ (n : ℕ) (U : ℤ → Set (Euclid (n + 1))) (X : ℤ → GeometricCurrentOn (univ : Set (Euclid (n + 1))) (n + 1)) (T : GeometricCurrentOn (univ : Set (Euclid (n + 1))) n) (C : ℝ≥0∞), 1 ≤ n → (∀ j, MeasurableSet (U j)) → (∀ j, U (j + 1) ⊆ U j) → (∀ (j : ℤ) (ω : TestFormOn (univ : Set (Euclid (n + 1))) (n + 1)), X j ω = ∫ x in U j, (ω : DifferentialForm (Euclid (n + 1)) (n + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ))) → (∀ j, (X j).boundary.mass < ∞) → (∀ η : TestFormOn (univ : Set (Euclid (n + 1))) n, HasSum (fun j => (X j).boundary η) (T η)) → C < ∞ → (∀ (N : ℕ) (Y : GeometricCurrentOn (univ : Set (Euclid (n + 1))) n), (∀ η : TestFormOn (univ : Set (Euclid (n + 1))) n, Y η = ∑ j ∈ Finset.Icc (-(N : ℤ)) N, (X j).boundary η) → Y.mass ≤ C) → IsIntegerMultiplicity T`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.boundary_im-a1.de_giorgi-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.normal_orientation-a1`
- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.oriented_piece_mass-a1.oriented_mass_lower-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
