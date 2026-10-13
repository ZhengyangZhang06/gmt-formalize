# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.integer_density-a1.mass_density-a1.ae_ball_growth-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-mass-density-a1-ae-f7d60da3e2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.integer_density-a1.mass_density-a1`
- Child key: `ae_ball_growth`
- Declaration: `Submission.ind_md_ae_closedBall_growth`
- Exact Lean type: `∀ (P n : ℕ) (ν : Measure (Eucl P)), ν univ < ∞ → ∀ᵐ x ∂(μHE[n] : Measure (Eucl P)), ∃ C r₀ : ℝ, 0 < r₀ ∧ ∀ r ∈ Ioo (0 : ℝ) r₀, ν (closedBall x r) < ENNReal.ofReal (C * r ^ n)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
