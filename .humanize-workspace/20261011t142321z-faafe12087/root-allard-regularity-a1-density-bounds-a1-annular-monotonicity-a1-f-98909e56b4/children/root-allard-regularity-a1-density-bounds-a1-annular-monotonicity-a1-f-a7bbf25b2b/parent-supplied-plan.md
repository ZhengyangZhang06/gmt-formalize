# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.fixed_cutoff-a1.a_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1-annular-monotonicity-a1-f-a7bbf25b2b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.fixed_cutoff-a1`
- Child key: `a_bound`
- Declaration: `Submission.allard52_am_fc_a_bound`
- Exact Lean type: `∀ (n : ℕ), 1 ≤ n → ∀ (p R Λ ε t I E N : ℝ), (n : ℝ) < p → 0 < R → 0 < Λ → 0 < ε → ε ≤ 1 → 0 < t → 0 ≤ I → 0 ≤ N → N ≤ (p - n) / (4 * p) * Λ * R ^ ((n : ℝ) / p - 1) → |E| ≤ (1 + ε) * t * N * I ^ (1 - 1 / p) → |E / t ^ (n + 1) / (1 + I / t ^ n)| ≤ 2 * ((p - n) / (4 * p)) * Λ / R * (t / R) ^ (-((n : ℝ) / p))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
