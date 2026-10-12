# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.density_estimates-a1.lipschitz_sobolev-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1-lipschitz-sobolev-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.density_estimates-a1`
- Child key: `lipschitz_sobolev`
- Declaration: `Submission.deGiorgiDens_lipschitz_sobolev`
- Exact Lean type: `∀ (n : ℕ), ∃ c : ℝ, 0 < c ∧ ∀ (u : Rn (n + 1) → ℝ) (K : ℝ≥0), LipschitzWith K u → HasCompactSupport u → eLpNorm u ((n + 1 : ℝ≥0∞) / n) volume ≤ ENNReal.ofReal (c * ∫ y, ‖fderiv ℝ u y‖)`

## Sibling prerequisites

- `root.de_giorgi-a1.density_estimates-a1.lipschitz_smooth_approx-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
