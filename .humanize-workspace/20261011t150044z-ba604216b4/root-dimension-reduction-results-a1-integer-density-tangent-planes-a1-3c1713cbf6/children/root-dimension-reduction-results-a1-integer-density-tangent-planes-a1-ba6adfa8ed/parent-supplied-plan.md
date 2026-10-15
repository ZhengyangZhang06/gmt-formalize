# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.carrier_area_formula-a1.piece_tangent_plane-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-ba6adfa8ed/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.carrier_area_formula-a1`
- Child key: `piece_tangent_plane`
- Declaration: `Submission.idtp_caf_piece_approxTangentPlane_ae`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Euclid P)) (g : Euclid n → Euclid P) (A : Set (Euclid n)) (L : NNReal) (c : ℝ), 1 ≤ n → MeasurableSet M → (∀ K : Set (Euclid P), IsCompact K → μHE[n] (M ∩ K) ≠ ∞) → LipschitzWith L g → MeasurableSet A → 0 < c → (∀ a ∈ A, ∀ a' ∈ A, c * ‖a - a'‖ ≤ ‖g a - g a'‖) → (∀ a ∈ A, DifferentiableAt ℝ g a ∧ Injective (fderiv ℝ g a)) → g '' A ⊆ M → ∀ᵐ a ∂(volume.restrict A), approxTangentPlane n M (g a) = LinearMap.range (fderiv ℝ g a : Euclid n →ₗ[ℝ] Euclid P)`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.carrier_area_formula-a1.piece_image_tangent-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_tangent-a1.tangent_transfer-a1`
- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.piece_tangent_density-a1.piece_pullback-a1`
- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.image_tangent_transport-a1.chosen_tangent_plane-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
