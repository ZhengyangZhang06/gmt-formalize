# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1.lipschitz_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-3cccb9cfc9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1`
- Child key: `lipschitz_cover`
- Declaration: `Submission.cbrr_lipschitz_cover_of_cone_condition`
- Exact Lean type: `∀ (P n : ℕ) (T : Submodule ℝ (Euclid P)) (D : Set (Euclid P)) (C : ℝ), Module.finrank ℝ T = n → (∀ x ∈ D, ∀ y ∈ D, ‖y - x‖ ≤ C * ‖T.starProjection (y - x)‖) → ∃ F : Euclid n → Euclid P, (∃ K : NNReal, LipschitzWith K F) ∧ D ⊆ range F`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
