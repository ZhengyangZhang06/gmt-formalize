# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.allard_density_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-allard-density-bounds-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1`
- Child key: `allard_density_bounds`
- Declaration: `Submission.ted_allard_density_bounds`
- Exact Lean type: `∀ n ℓ : ℕ, 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ C δP : ℝ, 1 ≤ C ∧ 0 < δP ∧ δP ≤ 1 / 8 ∧ C * δP ≤ 1 / 2 ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δP → V.AllardHypotheses H p δ ρ → (∀ y : Amb n ℓ, ‖y‖ ≤ 3 * δ * ρ → ∀ s : ℝ, 0 < s → s ≤ ρ / 2 → V.weight (closedBall y s) ≤ ENNReal.ofReal ((1 + C * δ) * (unitBallVolume n * s ^ n))) ∧ (∀ y ∈ V.support, ‖y‖ ≤ 3 * δ * ρ → ∀ s : ℝ, 0 < s → s ≤ ρ / 2 → ENNReal.ofReal ((1 - C * δ) * (unitBallVolume n * s ^ n)) ≤ V.weight (closedBall y s)) ∧ (∀ᵐ x ∂V.weight, ‖x‖ ≤ 3 * δ * ρ → V.mult x ≤ 1 + C * δ) ∧ (μHE[n] : Measure (Amb n ℓ)) ((V.support ∩ ball 0 ρ) \ V.carrier) = 0`

## Sibling prerequisites

- `root.tilt_excess_decay-a1.lp_monotonicity-a1`
- `root.tilt_excess_decay-a1.density_ge_one-a1`
- `root.tilt_excess_decay-a1.tangent_plane_facts-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
