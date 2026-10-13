# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.affine_approximation-a1.height_bound_small_delta-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-height-bound-small-delta-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.affine_approximation-a1`
- Child key: `height_bound_small_delta`
- Declaration: `Submission.aal_height_bound_small_delta`
- Exact Lean type: `∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ δ₁ C₁ : ℝ, 0 < δ₁ ∧ 0 < C₁ ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δ₁ → V.AllardHypotheses H p δ ρ → ∀ ξ ∈ V.support ∩ closedBall (0 : Amb n ℓ) (δ * ρ), ∀ σ : ℝ, 0 < σ → σ ≤ 2 * δ * ρ → ∃ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n ∧ ∀ x ∈ V.support ∩ closedBall ξ σ, infDist (x - ξ) (T : Set (Amb n ℓ)) ≤ C₁ * δ ^ (1 / (2 * (n : ℝ) + 2)) * σ`

## Sibling prerequisites

- `root.affine_approximation-a1.tangent_structure-a1`
- `root.affine_approximation-a1.pinched_density_bounds-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
