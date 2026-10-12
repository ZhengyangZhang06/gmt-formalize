# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.integrating_factor-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1-annular-monotonicity-a1-i-2ee61175b0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1`
- Child key: `integrating_factor`
- Declaration: `Submission.allard52_am_integrating_factor`
- Exact Lean type: `∀ (n : ℕ) (I I' E Q a : ℝ → ℝ) (R M β : ℝ), β < 1 → (∀ t ∈ Ioo 0 R, HasDerivAt I (I' t) t) → (∀ t ∈ Ioo 0 R, ContinuousAt E t) → (∀ t ∈ Ioo 0 R, ContinuousAt Q t) → (∀ t ∈ Ioo 0 R, 0 ≤ I t) → (∀ t ∈ Ioo 0 R, (n : ℝ) * I t - t * I' t + t * Q t = -E t) → (∀ t, a t = E t / t ^ (n + 1) / (1 + I t / t ^ n)) → (∀ t ∈ Ioo 0 R, |a t| ≤ M * t ^ (-β)) → ∀ s r : ℝ, 0 < s → s ≤ r → r < R → Real.exp (-∫ τ in (0)..r, a τ) * (1 + I r / r ^ n) - Real.exp (-∫ τ in (0)..s, a τ) * (1 + I s / s ^ n) = ∫ t in s..r, Real.exp (-∫ τ in (0)..t, a τ) * (Q t / t ^ n)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
