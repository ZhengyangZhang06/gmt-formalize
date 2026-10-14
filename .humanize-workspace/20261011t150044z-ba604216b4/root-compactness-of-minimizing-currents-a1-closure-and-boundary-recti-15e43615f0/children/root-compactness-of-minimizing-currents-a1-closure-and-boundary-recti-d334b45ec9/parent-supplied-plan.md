# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.growth_dimension-a1.ball_count-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-d334b45ec9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.growth_dimension-a1`
- Child key: `ball_count`
- Declaration: `Submission.cbr_ci_cp_gd_translated_ball_count`
- Exact Lean type: `∀ (P : ℕ) (ν : Measure (Euclid P)) (V : Submodule ℝ (Euclid P)) (S : Finset (Euclid P)) (ρ : ℝ), (∀ v ∈ V, ∀ A : Set (Euclid P), MeasurableSet A → ν ((fun x => v + x) ⁻¹' A) = ν A) → (∀ x ∈ S, x ∈ V) → (∀ x ∈ S, ‖x‖ ≤ ρ) → (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 2 ≤ dist x y) → (S.card : ℝ≥0∞) * ν (ball 0 1) ≤ ν (ball 0 (ρ + 1))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
