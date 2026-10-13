# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.graph_rate-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1`
- Child key: `graph_rate`
- Declaration: `Submission.any_radius_graph_rate`
- Exact Lean type: `TiltExcessDecayTheorem → ConicalApproximationTheorem → ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ γ₁ γ₂ c₁ C₀ : ℝ, 0 < γ₁ → γ₁ < γ₂ → γ₂ < 1 → 0 < c₁ → c₁ < γ₂ → 0 ≤ C₀ → ∃ δR CR : ℝ, 0 < δR ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δR → V.AllardHypotheses H p δ ρ → ∀ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ), ContDiffOn ℝ 1 u (ball 0 (γ₂ * ρ)) → u 0 = 0 → (∀ x ∈ ball (0 : Rn n) (γ₂ * ρ), ‖fderiv ℝ u x‖ ≤ 1 / 7) → q '' graphOver u (ball 0 (γ₂ * ρ)) ⊆ V.support ∩ ball 0 ρ → V.support ∩ ball 0 (γ₂ * ρ) ⊆ q '' graphOver u (ball 0 (γ₂ * ρ)) → (∀ x ∈ ball (0 : Rn n) (c₁ * ρ), ‖u x‖ ≤ C₀ * δ ^ (1 / (2 * (n : ℝ) + 2)) * ‖x‖) → (∀ x ∈ closedBall (0 : Rn n) (γ₁ * ρ), ‖u x‖ ≤ CR * δ ^ (1 / (2 * (n : ℝ) + 2)) * ‖x‖) ∧ (∀ x ∈ closedBall (0 : Rn n) (γ₁ * ρ), hsNorm (fderiv ℝ u x) ≤ CR * δ ^ (1 / (2 * (n : ℝ) + 2))) ∧ ∀ x ∈ closedBall (0 : Rn n) (γ₁ * ρ), ∀ y ∈ closedBall (0 : Rn n) (γ₁ * ρ), hsNorm (fderiv ℝ u x - fderiv ℝ u y) ≤ CR * δ ^ (1 / (2 * (n : ℝ) + 2)) * (‖x - y‖ / ρ) ^ (1 - (n : ℝ) / p)`

## Sibling prerequisites

- `root.allard_any_radius-a1.tangent_ae-a1`
- `root.allard_any_radius-a1.rescaled_varifold-a1`
- `root.allard_any_radius-a1.monotonicity_bounds-a1`
- `root.allard_any_radius-a1.pinching-a1`
- `root.allard_any_radius-a1.tilt_height_l1-a1`
- `root.allard_any_radius-a1.tilt_iteration-a1`
- `root.allard_any_radius-a1.graph_comparison-a1`
- `root.allard_any_radius-a1.radial_height-a1`
- `root.allard_any_radius-a1.campanato-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
