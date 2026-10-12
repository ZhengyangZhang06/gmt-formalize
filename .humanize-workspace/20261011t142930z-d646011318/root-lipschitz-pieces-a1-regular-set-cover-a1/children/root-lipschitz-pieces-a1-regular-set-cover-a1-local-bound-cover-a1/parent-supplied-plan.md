# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pieces-a1.regular_set_cover-a1.local_bound_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-lipschitz-pieces-a1-regular-set-cover-a1-local-bound-cover-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pieces-a1.regular_set_cover-a1`
- Child key: `local_bound_cover`
- Declaration: `Submission.lower_lipschitz_cover_of_local_bound`
- Exact Lean type: `∀ (n : ℕ) {F : Type} [NormedAddCommGroup F] (f : EuclideanSpace ℝ (Fin n) → F) (R : Set (EuclideanSpace ℝ (Fin n))), Continuous f → MeasurableSet R → (∀ w ∈ R, ∃ c : ℝ, 0 < c ∧ ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ c → c * ‖u‖ ≤ ‖f (w + u) - f w‖) → ∃ T : ℕ → Set (EuclideanSpace ℝ (Fin n)), R ⊆ ⋃ p, T p ∧ ∀ p, MeasurableSet (T p) ∧ Bornology.IsBounded (T p) ∧ T p ⊆ R ∧ ∃ c : ℝ, 0 < c ∧ ∀ v ∈ T p, ∀ w ∈ T p, c * ‖v - w‖ ≤ ‖f v - f w‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
