# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.retraction_comparison-a1.push_add-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-compariso-94d5dab86b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.retraction_comparison-a1`
- Child key: `push_add`
- Declaration: `Submission.dimred_mbl_lc_rc_push_add`
- Exact Lean type: `∀ (P n : ℕ) (O : Set (Euclid P)) (push : GeometricCurrentOn (univ : Set (Euclid P)) n → GeometricCurrentOn (univ : Set (Euclid P)) n) (X Y : GeometricCurrentOn (univ : Set (Euclid P)) n), (∀ X₁ X₂ : GeometricCurrentOn (univ : Set (Euclid P)) n, IsIntegerMultiplicity X₁ → IsIntegerMultiplicity X₂ → IsCompact X₁.support → X₁.support ⊆ O → IsCompact X₂.support → X₂.support ⊆ O → push (X₁ - X₂) = push X₁ - push X₂) → IsIntegerMultiplicity X → IsIntegerMultiplicity Y → IsCompact X.support → X.support ⊆ O → IsCompact Y.support → Y.support ⊆ O → ∃ S : GeometricCurrentOn (univ : Set (Euclid P)) n, IsIntegerMultiplicity S ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) n, S ω = X ω + Y ω) ∧ S.support ⊆ X.support ∪ Y.support ∧ IsCompact S.support ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) n, push S ω = push X ω + push Y ω`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
