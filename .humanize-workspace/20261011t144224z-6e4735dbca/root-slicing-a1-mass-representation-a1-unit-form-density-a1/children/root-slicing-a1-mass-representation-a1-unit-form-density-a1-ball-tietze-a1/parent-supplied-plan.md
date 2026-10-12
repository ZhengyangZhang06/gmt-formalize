# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.mass_representation-a1.unit_form_density-a1.ball_tietze-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-mass-representation-a1-unit-form-density-a1-ball-tietze-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.mass_representation-a1.unit_form_density-a1`
- Child key: `ball_tietze`
- Declaration: `Submission.smr_ufd_ball_tietze`
- Exact Lean type: `∀ (P N : ℕ) (C : Set (Eucl P)) (u : Eucl P → EuclideanSpace ℝ (Fin N)), IsClosed C → ContinuousOn u C → (∀ x ∈ C, ‖u x‖ ≤ 1) → ∃ w : Eucl P → EuclideanSpace ℝ (Fin N), Continuous w ∧ (∀ x, ‖w x‖ ≤ 1) ∧ ∀ x ∈ C, w x = u x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
