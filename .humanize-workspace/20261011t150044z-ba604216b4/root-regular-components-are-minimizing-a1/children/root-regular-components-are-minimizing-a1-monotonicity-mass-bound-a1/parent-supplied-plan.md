# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_components_are_minimizing-a1.monotonicity_mass_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-monotonicity-mass-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_components_are_minimizing-a1`
- Child key: `monotonicity_mass_bound`
- Declaration: `Submission.regcomp_monotonicity_mass_bound`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), IsOpen U → R.HasLocallyBoundedMeanCurvature → ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ C r₁ : ℝ, 0 < r₁ ∧ ∀ x ∈ K, ∀ r : ℝ, 0 < r → r < r₁ → R.measure (ball x r) ≤ ENNReal.ofReal (C * r ^ n)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
