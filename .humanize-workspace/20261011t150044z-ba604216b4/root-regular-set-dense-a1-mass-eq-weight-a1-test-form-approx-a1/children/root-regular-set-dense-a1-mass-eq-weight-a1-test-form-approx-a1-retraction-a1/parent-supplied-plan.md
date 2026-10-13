# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_dense-a1.mass_eq_weight-a1.test_form_approx-a1.retraction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1-test-form-approx-a1-retraction-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_dense-a1.mass_eq_weight-a1.test_form_approx-a1`
- Child key: `retraction`
- Declaration: `Submission.rsd_mw_tfa_retraction`
- Exact Lean type: `∀ (P n : ℕ), ∃ ρ : Covector (Euclid P) n → Covector (Euclid P) n, Continuous ρ ∧ ρ 0 = 0 ∧ (∀ a, covectorEuclideanNorm (ρ a) ≤ 1) ∧ ∀ a b, covectorEuclideanNorm b ≤ 1 → covectorEuclideanNorm (ρ a - b) ≤ 2 * covectorEuclideanNorm (a - b)`

## Sibling prerequisites

- `root.regular_set_dense-a1.mass_eq_weight-a1.test_form_approx-a1.norm_props-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
