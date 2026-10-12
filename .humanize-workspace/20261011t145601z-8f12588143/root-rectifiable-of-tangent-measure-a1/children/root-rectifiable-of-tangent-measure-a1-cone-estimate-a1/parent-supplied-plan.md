# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiable_of_tangent_measure-a1.cone_estimate-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-rectifiable-of-tangent-measure-a1-cone-estimate-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiable_of_tangent_measure-a1`
- Child key: `cone_estimate`
- Declaration: `Submission.tangentMeasure_projection_lower_bound`
- Exact Lean type: `∀ (N n : ℕ) (μ : Measure (Rn N)) (Q : Submodule ℝ (Rn N)) (E : Set (Rn N)) (a b δ : ℝ), 0 < a → 32 ^ n * b < a → (∀ x ∈ E, ∀ ρ ∈ Set.Ioo 0 δ, ENNReal.ofReal (a * ρ ^ n) ≤ μ (Metric.ball x ρ) ∧ μ ({z | ‖Q.starProjection (z - x)‖ ≤ ‖z - x‖ / 3} ∩ Metric.ball x ρ) ≤ ENNReal.ofReal (b * ρ ^ n)) → ∀ x ∈ E, ∀ y ∈ E, ‖y - x‖ < δ / 2 → ‖y - x‖ ≤ 4 * ‖Q.starProjection (y - x)‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
