# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.near_maximizer-a1.first_hit_selection-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-imrep-mass-formula-a1-near-34b4d5acc0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.near_maximizer-a1`
- Child key: `first_hit_selection`
- Declaration: `Submission.regcomp_covector_first_hit_selection`
- Exact Lean type: `∀ (P n : ℕ) (A : ℕ → Set (Euclid P)) (b : ℕ → Covector (Euclid P) n), (∀ k, MeasurableSet (A k)) → ∃ g : Euclid P → Covector (Euclid P) n, StronglyMeasurable g ∧ ∀ x, (g x = 0 ∧ ∀ k, x ∉ A k) ∨ ∃ k, x ∈ A k ∧ g x = b k`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
