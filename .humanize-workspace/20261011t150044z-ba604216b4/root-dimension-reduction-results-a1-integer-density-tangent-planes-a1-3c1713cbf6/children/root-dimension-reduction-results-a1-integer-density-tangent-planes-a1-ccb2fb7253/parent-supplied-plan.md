# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.carrier_area_formula-a1.piece_image_tangent-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-ccb2fb7253/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.carrier_area_formula-a1`
- Child key: `piece_image_tangent`
- Declaration: `Submission.idtp_caf_piece_image_approxTangent_ae`
- Exact Lean type: `∀ (P n : ℕ) (g : Euclid n → Euclid P) (A : Set (Euclid n)) (L : NNReal) (c : ℝ), 1 ≤ n → LipschitzWith L g → MeasurableSet A → 0 < c → (∀ a ∈ A, ∀ a' ∈ A, c * ‖a - a'‖ ≤ ‖g a - g a'‖) → (∀ a ∈ A, DifferentiableAt ℝ g a ∧ Injective (fderiv ℝ g a)) → ∀ᵐ a ∂(volume.restrict A), HasApproximateTangentSpaceAt n (g '' A) (g a) (LinearMap.range (fderiv ℝ g a : Euclid n →ₗ[ℝ] Euclid P))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
