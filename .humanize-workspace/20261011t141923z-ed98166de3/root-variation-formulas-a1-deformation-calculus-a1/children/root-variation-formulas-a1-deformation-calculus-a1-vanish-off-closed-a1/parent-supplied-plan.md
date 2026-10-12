# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.variation_formulas-a1.deformation_calculus-a1.vanish_off_closed-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-variation-formulas-a1-deformation-calculus-a1-vanish-off-closed-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.variation_formulas-a1.deformation_calculus-a1`
- Child key: `vanish_off_closed`
- Declaration: `Submission.variation_deformation_vanish_off_closed`
- Exact Lean type: `∀ (N : ℕ) (K : Set (Rn N)) (φ : ℝ → Rn N → Rn N), IsClosed K → (∀ t ∈ Ioo (-1 : ℝ) 1, ∀ x, x ∉ K → φ t x = x) → ∀ x, x ∉ K → initialVelocity φ x = 0 ∧ initialAcceleration φ x = 0 ∧ fderiv ℝ (initialVelocity φ) x = 0 ∧ fderiv ℝ (initialAcceleration φ) x = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
