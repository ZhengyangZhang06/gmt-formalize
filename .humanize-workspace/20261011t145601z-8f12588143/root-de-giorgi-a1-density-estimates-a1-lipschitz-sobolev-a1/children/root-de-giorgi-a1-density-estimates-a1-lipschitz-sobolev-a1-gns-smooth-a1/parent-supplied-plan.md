# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.density_estimates-a1.lipschitz_sobolev-a1.gns_smooth-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1-lipschitz-sobolev-a1-gns-smooth-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.density_estimates-a1.lipschitz_sobolev-a1`
- Child key: `gns_smooth`
- Declaration: `Submission.deGiorgiDensSob_gns_contDiff`
- Exact Lean type: `∀ (n : ℕ), 0 < n → ∃ c : ℝ, 0 < c ∧ ∀ v : Rn (n + 1) → ℝ, ContDiff ℝ 1 v → HasCompactSupport v → eLpNorm v ((n + 1 : ℝ≥0∞) / n) volume ≤ ENNReal.ofReal (c * ∫ y, ‖fderiv ℝ v y‖)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
