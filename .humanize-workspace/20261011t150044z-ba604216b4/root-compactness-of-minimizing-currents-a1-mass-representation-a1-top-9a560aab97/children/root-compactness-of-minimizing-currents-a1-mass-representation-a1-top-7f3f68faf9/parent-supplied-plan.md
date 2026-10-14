# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.mass_representation-a1.top_dim_null-a1.null_of_average_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-top-7f3f68faf9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.top_dim_null-a1`
- Child key: `null_of_average_bound`
- Declaration: `Submission.cmr_tdn_null_of_average_bound`
- Exact Lean type: `∀ (n : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X) (q : X → Euclid n) (h : X → ℝ), Measurable q → Integrable h ν → (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ a : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) a → HasCompactSupport a → (∀ y, 0 ≤ a y) → (∀ y, a y ≤ 1) → |∫ x, h x * a (q x) ∂ν| ≤ ε + C * ∫ y, a y) → ∀ K : Set (Euclid n), IsCompact K → volume K = 0 → ∫ x in q ⁻¹' K, h x ∂ν = 0`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.mass_representation-a1.top_dim_null-a1.null_set_cutoffs-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
