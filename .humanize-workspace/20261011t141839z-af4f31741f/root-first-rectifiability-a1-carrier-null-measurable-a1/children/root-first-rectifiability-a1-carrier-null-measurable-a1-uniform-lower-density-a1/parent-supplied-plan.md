# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.first_rectifiability-a1.carrier_null_measurable-a1.uniform_lower_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-carrier-null-measurable-a1-uniform-lower-density-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.first_rectifiability-a1.carrier_null_measurable-a1`
- Child key: `uniform_lower_density`
- Declaration: `Submission.frt_cnm_exists_uniform_densityRatio_lower`
- Exact Lean type: `∀ (N n : ℕ) (μ : Measure (Euclidean N)) (x : Euclidean N) (t : ℝ≥0∞), 0 < t → HasDensity n μ x t → ∃ m k : ℕ, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / ((k : ℝ) + 1) → (2 * ((m : ℝ≥0∞) + 1))⁻¹ ≤ densityRatio n μ x ρ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
