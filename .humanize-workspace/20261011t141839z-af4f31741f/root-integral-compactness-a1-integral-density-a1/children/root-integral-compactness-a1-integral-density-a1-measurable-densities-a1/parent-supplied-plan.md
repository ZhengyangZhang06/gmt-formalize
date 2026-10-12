# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.integral_density-a1.measurable_densities-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-integral-density-a1-measurable-densities-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.integral_density-a1`
- Child key: `measurable_densities`
- Declaration: `Submission.intcpt_id_measurable_densities`
- Exact Lean type: `∀ (N n : ℕ) (μ : Measure (Euclidean N)) [SFinite μ], Measurable (fun x ↦ limsup (densityRatio n μ x) (𝓝[>] 0)) ∧ Measurable (fun x ↦ liminf (densityRatio n μ x) (𝓝[>] 0)) ∧ ∀ c : ℝ≥0∞, MeasurableSet {x | HasDensity n μ x c}`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
