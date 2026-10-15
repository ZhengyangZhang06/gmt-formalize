# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_splitting-a1.split_off_spine-a1.lipschitz_tangent-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-aad3a33660/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_splitting-a1.split_off_spine-a1`
- Child key: `lipschitz_tangent`
- Declaration: `Submission.idtp_fons_cs_sos_lipschitz_approx_tangent`
- Exact Lean type: `∀ (P k : ℕ) (F : Euclid k → Euclid P) (Y : Set (Euclid P)) (K : NNReal), 0 < k → LipschitzWith K F → MeasurableSet Y → (∀ C : Set (Euclid P), IsCompact C → μHE[k] (Y ∩ C) ≠ ∞) → ∀ᵐ u ∂(volume : Measure (Euclid k)), F u ∈ Y → DifferentiableAt ℝ F u → Function.Injective (fderiv ℝ F u) → HasApproximateTangentSpaceAt k Y (F u) (LinearMap.range (fderiv ℝ F u : Euclid k →ₗ[ℝ] Euclid P))`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.piece_tangent_density-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
