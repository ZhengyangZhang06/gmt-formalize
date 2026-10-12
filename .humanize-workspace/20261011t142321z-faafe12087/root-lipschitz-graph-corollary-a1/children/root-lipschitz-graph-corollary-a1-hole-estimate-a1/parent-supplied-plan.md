# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_graph_corollary-a1.hole_estimate-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-graph-corollary-a1-hole-estimate-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_graph_corollary-a1`
- Child key: `hole_estimate`
- Declaration: `Submission.lgc_hole_estimate`
- Exact Lean type: `∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ δ₂ ε₂ C₂ : ℝ, 0 < δ₂ ∧ 0 < ε₂ ∧ 0 < C₂ ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δ₂ → V.AllardHypotheses H p δ ρ → ∀ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ) (ε : ℝ), 0 ≤ ε → ε ≤ ε₂ → LipschitzWith (Real.toNNReal ε) f → ∀ ζ ∈ q '' graphOver f univ, ‖ζ‖ ≤ 2 * (δ * ρ) → 0 < infDist ζ V.support → infDist ζ V.support ≤ δ * ρ → ∃ y ∈ V.support, dist y ζ = infDist ζ V.support ∧ (infDist ζ V.support / 2) ^ n ≤ C₂ * ((V.weight (closedBall ζ (3 * (infDist ζ V.support / 2)) \ q '' graphOver f univ)).toReal + ∫ x in closedBall ζ (3 * (infDist ζ V.support / 2)), hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection) ∂V.weight)`

## Sibling prerequisites

- `root.lipschitz_graph_corollary-a1.tangent_plane_ae-a1`
- `root.lipschitz_graph_corollary-a1.density_monotonicity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
