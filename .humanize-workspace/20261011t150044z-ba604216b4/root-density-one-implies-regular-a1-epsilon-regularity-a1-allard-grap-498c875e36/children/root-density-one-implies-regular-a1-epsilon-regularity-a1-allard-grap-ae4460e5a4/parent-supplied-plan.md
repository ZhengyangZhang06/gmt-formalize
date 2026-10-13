# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.density_bounds-a1.sharp_ratio-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-ae4460e5a4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.density_bounds-a1`
- Child key: `sharp_ratio`
- Declaration: `Submission.dorag_dbs_sharp_mass_ratio`
- Exact Lean type: `∀ (P n : ℕ) (μ : Measure (Euclid P)) (W : Set (Euclid P)) (κ δ ρ : ℝ) (z : Euclid P), 0 < ρ → 0 ≤ δ → δ ≤ 1 / 8 → 0 ≤ κ → κ * ρ ≤ δ → closedBall z ρ ⊆ W → μ (closedBall z ρ) ≤ ENNReal.ofReal (1 + δ) * unitBallVolume n * ENNReal.ofReal (ρ ^ n) → (∀ (y : Euclid P) (s t : ℝ), 0 < s → s < t → closedBall y t ⊆ W → ENNReal.ofReal (Real.exp (κ * s) / s ^ n) * μ (closedBall y s) ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * μ (closedBall y t)) → ∀ y ∈ closedBall z (4 * δ * ρ), ∀ t : ℝ, 0 < t → t ≤ (1 - 4 * δ) * ρ → ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * μ (closedBall y t) ≤ ENNReal.ofReal (Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n) * unitBallVolume n ∧ μ (closedBall y t) ≤ ENNReal.ofReal (Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n) * unitBallVolume n * ENNReal.ofReal (t ^ n)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
