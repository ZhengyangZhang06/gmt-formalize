# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.density_rep-a1.dual_norm-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-8f5edb5104/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.density_rep-a1`
- Child key: `dual_norm`
- Declaration: `Submission.cbr_ci_dr_multivector_dual_norm`
- Exact Lean type: `∀ (P n : ℕ), ∃ N : MultiVector P n → ℝ, Continuous N ∧ (∀ ζ : MultiVector P n, 0 ≤ N ζ) ∧ (∀ (ζ : MultiVector P n) (α : Covector (Euclid P) n), |ζ α| ≤ N ζ * covectorEuclideanNorm α) ∧ (∀ ζ : MultiVector P n, ∃ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 ∧ ζ β = N ζ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
