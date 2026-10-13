# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.total_boundedness-a1.flat_sub-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-flat-sub-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.total_boundedness-a1`
- Child key: `flat_sub`
- Declaration: `Submission.fiw_tb_flat_sub`
- Exact Lean type: `(∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T₁ T₂ S : GeometricCurrentOn U n) (a b : ℤ), IsIntegerMultiplicity T₁ → IsIntegerMultiplicity T₂ → (∀ ω, S ω = (a : ℝ) * T₁ ω + (b : ℝ) * T₂ ω) → IsIntegerMultiplicity S) → ∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (R₁ R₂ : GeometricCurrentOn U (n + 1)) (S₁ S₂ : GeometricCurrentOn U n), IsIntegerMultiplicity R₁ → IsIntegerMultiplicity R₂ → IsIntegerMultiplicity S₁ → IsIntegerMultiplicity S₂ → ∃ (R : GeometricCurrentOn U (n + 1)) (S : GeometricCurrentOn U n), IsIntegerMultiplicity R ∧ IsIntegerMultiplicity S ∧ (∀ ω, R.boundary ω + S ω = (R₁.boundary ω + S₁ ω) - (R₂.boundary ω + S₂ ω)) ∧ R.mass + S.mass ≤ (R₁.mass + S₁.mass) + (R₂.mass + S₂.mass)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
