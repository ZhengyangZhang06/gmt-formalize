# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.density_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1`
- Child key: `density_bounds`
- Declaration: `Submission.allard52_density_bounds`
- Exact Lean type: `∀ (n : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ δP CP : ℝ, 0 < δP ∧ δP ≤ 1 / 8 ∧ 0 < CP ∧ CP * δP ≤ 1 / 2 ∧ ∀ (ℓ : ℕ) (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δP → V.AllardHypotheses H p δ ρ → ∀ y : Amb n ℓ, ‖y‖ ≤ 3 * δ * ρ → ∀ s : ℝ, 0 < s → s ≤ ρ / 2 → V.weight (closedBall y s) ≤ ENNReal.ofReal ((1 + CP * δ) * (unitBallVolume n * s ^ n)) ∧ (y ∈ V.support → ENNReal.ofReal ((1 - CP * δ) * (unitBallVolume n * s ^ n)) ≤ V.weight (closedBall y s) ∧ ∫⁻ x in closedBall y s, ENNReal.ofReal (‖x - y - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂V.weight ≤ ENNReal.ofReal (CP * unitBallVolume n * δ))`

## Sibling prerequisites

- `root.allard_regularity-a1.tangent_ae-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
