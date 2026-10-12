# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.im_closure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-im-closure-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1`
- Child key: `im_closure`
- Declaration: `Submission.iwl_im_closure`
- Exact Lean type: `(∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ X : GeometricCurrentOn U k, IsIntegerMultiplicity X → ∀ W, CompactlyContainedOpen W U → X.massOn W < ∞) ∧ (∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (X : GeometricCurrentOn U k) (A : Set (Eucl P)) (S : GeometricCurrentOn U k), IsIntegerMultiplicity X → IsRestriction X A S → IsIntegerMultiplicity S) ∧ (∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (X Y Z : GeometricCurrentOn U k) (a b : ℤ), IsIntegerMultiplicity X → IsIntegerMultiplicity Y → (∀ ω : TestFormOn U k, Z ω = (a : ℝ) * X ω + (b : ℝ) * Y ω) → IsIntegerMultiplicity Z)`

## Sibling prerequisites

- `root.integrality_weak_limits-a1.tangent_locality-a1`
- `root.integrality_weak_limits-a1.restriction_theory-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
