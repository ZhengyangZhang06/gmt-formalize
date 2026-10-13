# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.mass_representation-a1.top_dim_null-a1.ball_average_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-top-af5e2dc451/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.top_dim_null-a1`
- Child key: `ball_average_bound`
- Declaration: `Submission.cmr_tdn_ball_average_bound`
- Exact Lean type: `∀ (n : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X) (q : X → Euclid n) (h : X → ℝ) (Λ : ℝ) (a : Euclid n → ℝ) (r : ℝ), IsFiniteMeasure ν → Measurable q → Integrable h ν → 0 ≤ Λ → Continuous a → HasCompactSupport a → (∀ y, 0 ≤ a y) → (∀ y, a y ≤ 1) → (∀ z : Euclid n, |∫ x, h x * (a (q x + z) - a (q x)) ∂ν| ≤ Λ * ‖z‖) → 0 < r → |∫ x, h x * a (q x) ∂ν| ≤ r * Λ + (volume (ball (0 : Euclid n) r)).toReal⁻¹ * (∫ x, |h x| ∂ν) * ∫ y, a y`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
