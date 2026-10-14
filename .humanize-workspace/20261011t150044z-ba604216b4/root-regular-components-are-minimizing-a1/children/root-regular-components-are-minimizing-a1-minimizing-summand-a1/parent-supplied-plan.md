# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_components_are_minimizing-a1.minimizing_summand-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-minimizing-summand-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_components_are_minimizing-a1`
- Child key: `minimizing_summand`
- Declaration: `Submission.regcomp_minimizing_summand`
- Exact Lean type: `∀ (P n : ℕ) (U A : Set (Euclid P)) (T T₁ : GeometricCurrentOn U n), IsOpen U → IsMinimizingIn T A → IsIntegerMultiplicity T₁ → IsIntegerMultiplicity (T - T₁) → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T₁.massOn W + (T - T₁).massOn W ≤ T.massOn W) → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → (T - T₁).massOn W ≠ ∞) → IsMinimizingIn T₁ A`

## Sibling prerequisites

- `root.regular_components_are_minimizing-a1.integer_multiplicity_sub-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
