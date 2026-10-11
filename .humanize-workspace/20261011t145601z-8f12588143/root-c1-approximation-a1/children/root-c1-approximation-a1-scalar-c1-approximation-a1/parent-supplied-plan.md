# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.c1_approximation-a1.scalar_c1_approximation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-c1-approximation-a1-scalar-c1-approximation-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.c1_approximation-a1`
- Child key: `scalar_c1_approximation`
- Declaration: `Submission.lipschitz_real_c1_approximation`
- Exact Lean type: `∀ (n : ℕ) (f : Rn n → ℝ) (K : ℝ≥0), LipschitzWith K f → ∀ ε : ℝ≥0∞, 0 < ε → ∃ g : Rn n → ℝ, ContDiff ℝ 1 g ∧ volume {x | f x ≠ g x ∨ fderiv ℝ f x ≠ fderiv ℝ g x} < ε`

## Sibling prerequisites

- `root.c1_approximation-a1.lusin_sigma_finite-a1`
- `root.c1_approximation-a1.uniform_remainder-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
