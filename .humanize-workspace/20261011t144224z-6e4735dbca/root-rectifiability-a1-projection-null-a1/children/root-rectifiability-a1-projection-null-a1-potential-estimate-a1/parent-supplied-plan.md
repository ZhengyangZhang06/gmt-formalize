# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiability-a1.projection_null-a1.potential_estimate-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1-potential-estimate-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiability-a1.projection_null-a1`
- Child key: `potential_estimate`
- Declaration: `Submission.rpn_potential_estimate`
- Exact Lean type: `∀ m : ℕ, ∃ C : ℝ, ∀ a : Eucl (m + 1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a → ∀ M : ℝ, (∀ y, |a y| ≤ M) → ∃ ψ : Fin (m + 1) → Eucl (m + 1) → ℝ, (∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ j)) ∧ (∀ y, ∑ j : Fin (m + 1), fderiv ℝ (ψ j) y (EuclideanSpace.single j (1 : ℝ)) = a y) ∧ ∀ j y, |ψ j y| ≤ C * M * ((volume (tsupport a)).toReal) ^ ((1 : ℝ) / ((m : ℝ) + 1))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
