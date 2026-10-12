# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.poincare_inequality-a1.smooth_truncation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-poincare-inequality-a1-smooth-truncation-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.poincare_inequality-a1`
- Child key: `smooth_truncation`
- Declaration: `Submission.smooth_step_truncation_exists`
- Exact Lean type: `∀ ε : ℝ, 0 < ε → ∃ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ ∧ (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) ∧ (∀ x, x ≤ 0 → ψ x = 0) ∧ (∀ x, ε ≤ x → ψ x = 1) ∧ (∀ x, 0 ≤ deriv ψ x) ∧ (∃ M : ℝ, ∀ x, deriv ψ x ≤ M) ∧ ∀ a : ℝ, ∫⁻ t in Ioi 0, ENNReal.ofReal (deriv ψ (a - t)) ≤ 1`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
