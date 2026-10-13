# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.density_bounds-a1.center_density_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1-center-density-bounds-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.density_bounds-a1`
- Child key: `center_density_bounds`
- Declaration: `Submission.allard52_center_density_bounds`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (g : Amb n ℓ → ℝ) (F : ℝ → ℝ) (y : Amb n ℓ) (ω R Λ M : ℝ), 0 < R → 0 < Λ → 0 ≤ M → g y = 0 → (∀ r ∈ Ioo 0 R, μ (closedBall y r) ≤ ENNReal.ofReal M) → (∀ r ∈ Ioo 0 R, Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ ∧ |F r - 1| ≤ Λ) → (∀ s r : ℝ, 0 < s → s ≤ r → r < R → F s * (s ^ n)⁻¹ * (μ (closedBall y s)).toReal + F s - 1 ≤ F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1 ∧ ∫⁻ x in closedBall y r \ closedBall y s, ENNReal.ofReal (g x) ∂μ ≤ ENNReal.ofReal (Real.exp Λ * ((F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1) - (F s * (s ^ n)⁻¹ * (μ (closedBall y s)).toReal + F s - 1)))) → ∀ s : ℝ, 0 < s → s < R → μ (closedBall y s) ≤ ENNReal.ofReal ((Real.exp (2 * Λ) * (M / R ^ n) + 2 * Real.exp Λ * Λ) * s ^ n) ∧ ((∀ t ∈ Ioo 0 R, ω ≤ F t * (t ^ n)⁻¹ * (μ (closedBall y t)).toReal + F t - 1) → ENNReal.ofReal (Real.exp (-Λ) * (ω - Λ) * s ^ n) ≤ μ (closedBall y s) ∧ ∫⁻ x in closedBall y s, ENNReal.ofReal (g x) ∂μ ≤ ENNReal.ofReal (Real.exp Λ * (Real.exp Λ * (M / R ^ n) + Λ - ω)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
