# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.affine_approximation-a1.mass_upper_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-mass-upper-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.affine_approximation-a1`
- Child key: `mass_upper_bound`
- Declaration: `Submission.aal_mass_upper_bound`
- Exact Lean type: `∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ 1 / 4 → V.AllardHypotheses H p δ ρ → ∀ y : Amb n ℓ, ‖y‖ ≤ ρ / 4 → ∀ s : ℝ, 0 < s → s ≤ ρ / 2 → V.weight (closedBall y s) ≤ ENNReal.ofReal (C₀ * (unitBallVolume n * s ^ n))`

## Sibling prerequisites

- `root.affine_approximation-a1.lp_monotonicity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
