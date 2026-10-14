# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.piece_representation-a1.lintegral_pullback-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-fcd819fff8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.piece_representation-a1`
- Child key: `lintegral_pullback`
- Declaration: `Submission.cmcdt_lpi_pr_lintegral_pullback`
- Exact Lean type: `∀ (P n : ℕ) (G : Euclid n → Euclid P) (A : Set (Euclid n)) (L : NNReal) (m : ℝ), LipschitzWith L G → MeasurableSet A → 0 < m → (∀ a ∈ A, ∀ a' ∈ A, m * ‖a - a'‖ ≤ ‖G a - G a'‖) → ∀ f : Euclid P → ℝ≥0∞, Measurable f → ∫⁻ u in A, f (G u) ≤ ENNReal.ofReal ((m ^ n)⁻¹) * ∫⁻ x in G '' A, f x ∂μHE[n]`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.regular_point_density-a1.bilipschitz_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
