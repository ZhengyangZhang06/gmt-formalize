# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.edge_tangent_plane-a1.cusp-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-cda04c6cd0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.edge_tangent_plane-a1`
- Child key: `cusp`
- Declaration: `Submission.idtp_cse_etp_cusp`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)) (Z : Set (Euclid P)) (Q : Submodule ℝ (Euclid P)) (a : Euclid P) (m : ℝ), a ∈ Q → (∀ K : Set (Euclid P), IsCompact K → μ K ≠ ∞) → (∀ y ∈ Z, ∀ ρ : ℝ, 0 < ρ → unitBallVolume 2 * ENNReal.ofReal (ρ ^ 2) ≤ μ (ball y ρ)) → (∀ lams : ℕ → ℝ, (∀ j, 0 < lams j) → Tendsto lams atTop (𝓝 0) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ g : Euclid P → ℝ, Continuous g → HasCompactSupport g → Tendsto (fun j => (lams (φ j))⁻¹ ^ 2 * ∫ x, g (dilation a (lams (φ j)) x) ∂μ) atTop (𝓝 (m * ∫ x in (Q : Set (Euclid P)), g x ∂μHE[2]))) → ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ ∀ x ∈ Z, dist x a < s → ‖x - Q.starProjection x‖ ≤ ε * dist x a`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.edge_tangent_plane-a1.rescaled_limit_mem-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
