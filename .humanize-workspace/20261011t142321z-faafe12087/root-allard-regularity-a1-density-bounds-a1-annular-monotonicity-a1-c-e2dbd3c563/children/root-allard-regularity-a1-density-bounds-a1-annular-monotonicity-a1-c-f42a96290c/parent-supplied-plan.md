# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.cutoff_limit-a1.interval_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1-annular-monotonicity-a1-c-f42a96290c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.cutoff_limit-a1`
- Child key: `interval_limit`
- Declaration: `Submission.allard52_amcl_interval_limit`
- Exact Lean type: `∀ (n : ℕ) (p R Λ t : ℝ) (a : ℕ → ℝ → ℝ) (g : ℝ → ℝ), (n : ℝ) < p → 0 < R → 0 < Λ → 0 < t → (∀ᶠ k in atTop, ∀ τ : ℝ, 0 < τ → τ ≤ t → ContinuousAt (a k) τ ∧ |a k τ| ≤ 2 * ((p - n) / (4 * p)) * Λ / R * (τ / R) ^ (-((n : ℝ) / p))) → (∀ τ : ℝ, 0 < τ → τ ≤ t → Tendsto (fun k => a k τ) atTop (𝓝 (g τ))) → Tendsto (fun k => ∫ τ in (0)..t, a k τ) atTop (𝓝 (∫ τ in (0)..t, g τ)) ∧ |∫ τ in (0)..t, g τ| ≤ Λ / 2 * (t / R) ^ (1 - (n : ℝ) / p)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
