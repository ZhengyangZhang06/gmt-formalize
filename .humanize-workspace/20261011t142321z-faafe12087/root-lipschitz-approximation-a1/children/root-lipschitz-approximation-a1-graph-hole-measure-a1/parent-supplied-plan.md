# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_approximation-a1.graph_hole_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-approximation-a1-graph-hole-measure-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_approximation-a1`
- Child key: `graph_hole_measure`
- Declaration: `Submission.lip_approx_graph_hole_measure`
- Exact Lean type: `∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ ε δ₀ C₀ : ℝ, 0 < ε ∧ 0 < δ₀ ∧ 0 ≤ C₀ ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δ₀ → V.AllardHypotheses H p δ ρ → ∀ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ), (∀ x z, ‖f x - f z‖ ≤ ε * ‖x - z‖) → (∀ x ∈ closedBall (0 : Rn n) (δ * ρ / 2), ‖f x‖ ≤ δ * ρ / 32) → (μHE[n] : Measure (Amb n ℓ)) (closedBall 0 (δ * ρ / 2) ∩ (q '' graphOver f (closedBall 0 (δ * ρ / 2)) \ V.support)) ≤ ENNReal.ofReal C₀ * (V.weight (closedBall 0 (3 * (δ * ρ) / 4) \ q '' graphOver f univ) + ENNReal.ofReal (∫ x in closedBall 0 (δ * ρ), hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection) ∂V.weight))`

## Sibling prerequisites

- `root.lipschitz_approximation-a1.graph_coordinates-a1`
- `root.lipschitz_approximation-a1.tangent_structure-a1`
- `root.lipschitz_approximation-a1.vitali_bound-a1`
- `root.lipschitz_approximation-a1.graph_measure-a1`
- `root.lipschitz_approximation-a1.hole_estimate-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
