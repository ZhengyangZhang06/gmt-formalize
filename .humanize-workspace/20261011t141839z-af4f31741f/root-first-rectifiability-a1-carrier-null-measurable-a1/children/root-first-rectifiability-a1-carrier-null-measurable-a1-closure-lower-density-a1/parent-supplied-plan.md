# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.first_rectifiability-a1.carrier_null_measurable-a1.closure_lower_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-carrier-null-measurable-a1-closure-lower-density-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.first_rectifiability-a1.carrier_null_measurable-a1`
- Child key: `closure_lower_density`
- Declaration: `Submission.frt_cnm_densityRatio_lower_closure`
- Exact Lean type: `∀ (N n : ℕ) (μ : Measure (Euclidean N)) (E : Set (Euclidean N)) (c : ℝ≥0∞) (δ : ℝ), (∀ x ∈ E, ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ → c ≤ densityRatio n μ x ρ) → ∀ y ∈ closure E, ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ → c ≤ densityRatio n μ y ρ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
