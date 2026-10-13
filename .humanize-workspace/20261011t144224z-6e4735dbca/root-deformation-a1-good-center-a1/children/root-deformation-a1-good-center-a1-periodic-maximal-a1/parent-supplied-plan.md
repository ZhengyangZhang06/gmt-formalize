# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.good_center-a1.periodic_maximal-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-good-center-a1-periodic-maximal-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.good_center-a1`
- Child key: `periodic_maximal`
- Declaration: `Submission.dgc_periodic_maximal`
- Exact Lean type: `∀ (ι : Type) [Fintype ι] (X : Type) [MeasurableSpace X] (μ : Measure X), IsFiniteMeasure μ → ∀ p : X → EuclideanSpace ℝ ι, Measurable p → ∀ (g₀ : EuclideanSpace ℝ ι) (β : ℝ), 0 < β → volume {g : EuclideanSpace ℝ ι | dist g g₀ < 1 / 4 ∧ ∃ σ : ℝ, 0 < σ ∧ σ < 1 / 4 ∧ ENNReal.ofReal (β * σ ^ Fintype.card ι) * μ univ < μ {x | ∃ z : ι → ℤ, ∑ i, (p x i - g i - z i) ^ 2 < σ ^ 2}} ≤ ENNReal.ofReal (10 ^ Fintype.card ι / β)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
