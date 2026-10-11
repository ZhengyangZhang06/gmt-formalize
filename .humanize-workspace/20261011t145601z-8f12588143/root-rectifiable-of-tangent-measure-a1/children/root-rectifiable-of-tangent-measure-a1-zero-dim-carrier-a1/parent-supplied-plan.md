# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiable_of_tangent_measure-a1.zero_dim_carrier-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-rectifiable-of-tangent-measure-a1-zero-dim-carrier-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiable_of_tangent_measure-a1`
- Child key: `zero_dim_carrier`
- Declaration: `Submission.tangentMeasure_zero_dim_carrier`
- Exact Lean type: `∀ (N : ℕ) (μ : Measure (Rn N)), (∀ K : Set (Rn N), IsCompact K → μ K < ∞) → (∀ᵐ x ∂μ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ENNReal.ofReal c ≤ μ (Metric.ball x ρ)) → ∃ R : Set (Rn N), MeasurableSet R ∧ CountablyRectifiable 0 R ∧ μ Rᶜ = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
