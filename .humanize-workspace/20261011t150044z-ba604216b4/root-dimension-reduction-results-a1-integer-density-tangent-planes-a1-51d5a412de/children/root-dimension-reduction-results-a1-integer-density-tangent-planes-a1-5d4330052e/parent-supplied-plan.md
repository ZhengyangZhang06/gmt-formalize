# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.edge_tangent_plane-a1.rescaled_limit_mem-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-5d4330052e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.edge_tangent_plane-a1`
- Child key: `rescaled_limit_mem`
- Declaration: `Submission.idtp_cse_etp_rescaled_limit_mem`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)) (S : Set (Euclid P)) (a w : Euclid P) (m : ℝ) (lams : ℕ → ℝ) (ws : ℕ → Euclid P), IsClosed S → (∀ K : Set (Euclid P), IsCompact K → μ K ≠ ∞) → (∀ j, 0 < lams j) → Tendsto ws atTop (𝓝 w) → (∀ g : Euclid P → ℝ, Continuous g → HasCompactSupport g → Tendsto (fun j => (lams j)⁻¹ ^ 2 * ∫ x, g (dilation a (lams j) x) ∂μ) atTop (𝓝 (m * ∫ x in S, g x ∂μHE[2]))) → (∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, unitBallVolume 2 * ENNReal.ofReal ((lams j * r) ^ 2) ≤ μ (ball (a + lams j • ws j) (lams j * r))) → w ∈ S`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
