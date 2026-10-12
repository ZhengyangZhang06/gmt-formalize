# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pieces-a1.regular_set_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-lipschitz-pieces-a1-regular-set-cover-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pieces-a1`
- Child key: `regular_set_cover`
- Declaration: `Submission.regular_set_lower_lipschitz_cover`
- Exact Lean type: `∀ (n ℓ : ℕ) (f : EuclideanSpace ℝ (Fin n) → Ambient n ℓ), Continuous f → ∃ T : ℕ → Set (EuclideanSpace ℝ (Fin n)), {w | DifferentiableAt ℝ f w ∧ Function.Injective (fderiv ℝ f w)} ⊆ ⋃ p, T p ∧ ∀ p, MeasurableSet (T p) ∧ Bornology.IsBounded (T p) ∧ (∀ w ∈ T p, DifferentiableAt ℝ f w ∧ Function.Injective (fderiv ℝ f w)) ∧ ∃ c : ℝ, 0 < c ∧ ∀ v ∈ T p, ∀ w ∈ T p, c * ‖v - w‖ ≤ ‖f v - f w‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
