# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.cone-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-cone-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1`
- Child key: `cone`
- Declaration: `Submission.any_radius_cone`
- Exact Lean type: `ConicalApproximationTheorem → ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ γ κ c₀ : ℝ, 0 < γ → γ < 1 → 0 < κ → κ ≤ (1 - γ) / 8 → 0 < c₀ → c₀ ≤ 1 / 4 → ∃ δC : ℝ, 0 < δC ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δC → V.AllardHypotheses H p δ ρ → ∀ T : Submodule ℝ (Amb n ℓ), (∀ x ∈ V.support ∩ closedBall 0 (c₀ * ρ), infDist x (T : Set (Amb n ℓ)) ≤ κ / 2 * ‖x‖) → ∀ y ∈ V.support ∩ closedBall 0 ((1 + γ) / 2 * ρ), infDist y (T : Set (Amb n ℓ)) ≤ κ * ‖y‖`

## Sibling prerequisites

- `root.allard_any_radius-a1.rescaled_varifold-a1`
- `root.allard_any_radius-a1.monotonicity_bounds-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
