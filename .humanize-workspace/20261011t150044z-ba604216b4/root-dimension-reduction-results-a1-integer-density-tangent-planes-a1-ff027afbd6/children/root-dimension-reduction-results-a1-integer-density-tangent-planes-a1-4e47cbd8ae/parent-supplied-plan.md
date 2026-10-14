# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.class_reduction-a1.nonflat_closed-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-4e47cbd8ae/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.class_reduction-a1`
- Child key: `nonflat_closed`
- Declaration: `Submission.idtp_fons_cr_nonflat_closed`
- Exact Lean type: `∀ (P n : ℕ) (β : ℝ) (S Dset : Set (Euclid P)), 0 < β → IsClosed S → IsOpen Dset → IsClosed (((S ∩ Dset) \ {w | ∃ ρ : ℝ, 0 < ρ ∧ ball w ρ ⊆ Dset ∧ ∃ Q : Submodule ℝ (Euclid P), Module.finrank ℝ Q = n ∧ ∃ s : ℝ, s < β * ρ ∧ ∀ y ∈ S, y ∈ ball w ρ → ‖(y - w) - Q.starProjection (y - w)‖ ≤ s}) ∪ Dsetᶜ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
