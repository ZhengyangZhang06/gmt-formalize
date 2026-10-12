# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.excess_iteration-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-excess-iteration-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1`
- Child key: `excess_iteration`
- Declaration: `Submission.allard52_excess_iteration`
- Exact Lean type: `TiltExcessDecayTheorem → ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ δ₁ C : ℝ, 0 < δ₁ ∧ 0 ≤ C ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δ₁ → V.AllardHypotheses H p δ ρ → ∀ ξ ∈ V.support ∩ closedBall 0 (δ * ρ), ∀ σ : ℝ, 0 < σ → σ ≤ δ * ρ / 2 → ∀ S₀ : Submodule ℝ (Amb n ℓ), Module.finrank ℝ S₀ = n → ∃ S : Submodule ℝ (Amb n ℓ), Module.finrank ℝ S = n ∧ hsNormSq (S.starProjection - S₀.starProjection) ≤ C * V.tiltExcessStar H p δ ξ σ S₀ ∧ ∀ s : ℝ, 0 < s → s ≤ σ → V.tiltExcess ξ s S ≤ C * (s / σ) ^ (2 * (1 - n / p)) * V.tiltExcessStar H p δ ξ σ S₀`

## Sibling prerequisites

- `root.allard_regularity-a1.tangent_ae-a1`
- `root.allard_regularity-a1.density_bounds-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
