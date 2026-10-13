# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_graph_corollary-a1.height_cone-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-graph-corollary-a1-height-cone-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_graph_corollary-a1`
- Child key: `height_cone`
- Declaration: `Submission.lgc_height_cone`
- Exact Lean type: `AffineApproximationLemma → ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ δ₁ C₁ : ℝ, 0 < δ₁ ∧ 0 < C₁ ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δ₁ → V.AllardHypotheses H p δ ρ → ∀ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (τ : ℝ), δ ^ (1 / (2 * (n : ℝ) + 2)) ≤ τ → (∀ ξ ∈ V.support ∩ closedBall 0 (δ * ρ / 2), ∀ σ : ℝ, 0 < σ → σ ≤ δ * ρ / 2 → V.tiltExcess ξ σ (rotatedPlane q) ≤ τ ^ 2) → (∀ x ∈ V.support ∩ closedBall 0 (δ * ρ), infDist x (rotatedPlane q : Set (Amb n ℓ)) ≤ C₁ * τ * (δ * ρ)) ∧ (∀ y ∈ V.support ∩ closedBall 0 (δ * ρ / 2), ∀ z ∈ V.support ∩ closedBall 0 (δ * ρ / 2), infDist (y - z) (rotatedPlane q : Set (Amb n ℓ)) ≤ C₁ * τ * ‖y - z‖)`

## Sibling prerequisites

- `root.lipschitz_graph_corollary-a1.tangent_plane_ae-a1`
- `root.lipschitz_graph_corollary-a1.density_monotonicity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
