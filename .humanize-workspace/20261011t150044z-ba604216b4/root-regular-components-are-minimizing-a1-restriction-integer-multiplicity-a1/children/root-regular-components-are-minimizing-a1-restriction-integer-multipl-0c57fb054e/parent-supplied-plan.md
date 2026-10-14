# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_components_are_minimizing-a1.restriction_integer_multiplicity-a1.imrep_split-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-restriction-integer-multipl-0c57fb054e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_components_are_minimizing-a1.restriction_integer_multiplicity-a1`
- Child key: `imrep_split`
- Declaration: `Submission.regcomp_rim_imrep_split`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (R R₁ R₂ : IMRep U n), R₁.carrier ⊆ R.carrier → R₂.carrier ⊆ R.carrier → R₁.orient = R.orient → R₂.orient = R.orient → (∀ x ∈ R.carrier, R.mult x = R₁.carrier.indicator R₁.mult x + R₂.carrier.indicator R₂.mult x) → R.measure = R₁.measure + R₂.measure ∧ ∀ ω : TestFormOn U n, R.action (ω : DifferentialForm (Euclid P) n) = R₁.action (ω : DifferentialForm (Euclid P) n) + R₂.action (ω : DifferentialForm (Euclid P) n)`

## Sibling prerequisites

- `root.regular_components_are_minimizing-a1.restriction_integer_multiplicity-a1.action_integrable-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
