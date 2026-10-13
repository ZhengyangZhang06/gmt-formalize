# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.lipschitz_tangent-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-8c1b7724be/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1`
- Child key: `lipschitz_tangent`
- Declaration: `Submission.dimred_cs_sos_lipschitz_approx_tangent`
- Exact Lean type: `∀ (P k : ℕ) (F : Euclid k → Euclid P) (Y : Set (Euclid P)) (K : NNReal), 0 < k → LipschitzWith K F → MeasurableSet Y → (∀ C : Set (Euclid P), IsCompact C → μHE[k] (Y ∩ C) ≠ ∞) → ∀ᵐ u ∂(volume : Measure (Euclid k)), F u ∈ Y → DifferentiableAt ℝ F u → Function.Injective (fderiv ℝ F u) → HasApproximateTangentSpaceAt k Y (F u) (LinearMap.range (fderiv ℝ F u : Euclid k →ₗ[ℝ] Euclid P))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
