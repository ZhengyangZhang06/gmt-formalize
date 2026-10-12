# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_structure-a1.piece_weighted_blowup-a1.density_point_image-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-weighted-blowup-a1-density-point-image-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_structure-a1.piece_weighted_blowup-a1`
- Child key: `density_point_image`
- Declaration: `Submission.ts_pwb_density_points_of_image_ae`
- Exact Lean type: `∀ (n ℓ : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → Ambient n ℓ), MeasurableSet C → (∃ K : NNReal, LipschitzWith K F) → ∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)), ∀ w ∈ C, F w = x → Tendsto (fun r : ℝ ↦ volume (C ∩ closedBall w r) / volume (closedBall w r)) (𝓝[>] 0) (𝓝 1)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
