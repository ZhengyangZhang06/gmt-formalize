# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.density_eq_multiplicity_ae-a1.upper_density_zero-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-5625b30197/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.density_eq_multiplicity_ae-a1`
- Child key: `upper_density_zero`
- Declaration: `Submission.idtp_dema_upper_density_zero`
- Exact Lean type: `∀ (P n : ℕ) (μ : Measure (Euclid P)) (A : Set (Euclid P)), MeasurableSet A → (∀ K : Set (Euclid P), IsCompact K → μ K ≠ ∞) → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∉ A → Tendsto (fun ρ : ℝ => μ (A ∩ ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
