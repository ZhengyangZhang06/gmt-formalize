# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.chart_tangent_differential-a1.chart_differential-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-chart-tangent-differential-a1-chart-differential-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.chart_tangent_differential-a1`
- Child key: `chart_differential`
- Declaration: `Submission.chartTD_comp_differentiable_lineDeriv_ae`
- Exact Lean type: `∀ (n N p : ℕ) (U : Set (Rn N)) (f : Rn N → Rn p) (V : Set (Rn n)) (ψ : Rn n → Rn N), IsOpen U → LocallyLipschitzOn U f → IsOpen V → ContDiffOn ℝ 1 ψ V → ∀ᵐ u ∂(volume : Measure (Rn n)), u ∈ V → ψ u ∈ U → DifferentiableAt ℝ (f ∘ ψ) u ∧ ∀ w : Rn n, HasLineDerivAt ℝ f (fderiv ℝ (f ∘ ψ) u w) (ψ u) (fderiv ℝ ψ u w)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
