# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.no_infinite_planar_pieces-a1.local_comparison-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-2a7a97cacf/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.no_infinite_planar_pieces-a1`
- Child key: `local_comparison`
- Declaration: `Submission.idtp_tdc_nipp_local_comparison`
- Exact Lean type: `∀ (P : ℕ) (μ ν : Measure (Euclid P)) (D : Set (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → μ K ≠ ∞) → MeasurableSet D → (∀ w ∈ D, ∃ ε : ℝ, 0 < ε ∧ ∀ W : Set (Euclid P), IsOpen W → W ⊆ ball w ε → ν W ≤ μ W) → ν D ≤ μ D`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
