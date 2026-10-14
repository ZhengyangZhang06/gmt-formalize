# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.mass_representation-a1.top_dim_null-a1.directional_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-top-b3432083f5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.top_dim_null-a1`
- Child key: `directional_bound`
- Declaration: `Submission.cmr_tdn_directional_bound`
- Exact Lean type: `∀ (n : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X) (q : X → Euclid n) (h : X → ℝ) (Λ : ℝ), IsFiniteMeasure ν → Measurable q → Integrable h ν → (∀ g : Euclid n → Euclid n, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → (∀ y, ‖g y‖ ≤ 1) → |∫ x, h x * LinearMap.trace ℝ (Euclid n) (fderiv ℝ g (q x)).toLinearMap ∂ν| ≤ Λ) → ∀ a : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) a → HasCompactSupport a → (∀ y, |a y| ≤ 1) → ∀ z : Euclid n, |∫ x, h x * (a (q x + z) - a (q x)) ∂ν| ≤ Λ * ‖z‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
