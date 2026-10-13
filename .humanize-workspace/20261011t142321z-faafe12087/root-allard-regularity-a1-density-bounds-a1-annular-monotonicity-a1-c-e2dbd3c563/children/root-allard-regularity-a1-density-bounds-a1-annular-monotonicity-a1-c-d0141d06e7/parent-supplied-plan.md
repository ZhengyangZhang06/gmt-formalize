# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.cutoff_limit-a1.annular_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1-annular-monotonicity-a1-c-d0141d06e7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.cutoff_limit-a1`
- Child key: `annular_limit`
- Declaration: `Submission.allard52_amcl_annular_lintegral_le`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (g : Amb n ℓ → ℝ≥0∞) (y : Amb n ℓ) (ε c : ℕ → ℝ) (s r L : ℝ), 0 < s → Tendsto ε atTop (𝓝 0) → Tendsto c atTop (𝓝 L) → (∀ᶠ k in atTop, ∫⁻ x in closedBall y r \ ball y ((1 + ε k) * s), g x ∂μ ≤ ENNReal.ofReal (c k)) → ∫⁻ x in closedBall y r \ closedBall y s, g x ∂μ ≤ ENNReal.ofReal L`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
