# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1.chart_integral_eq-a1.weighted_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-ta-24d92287e3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1.chart_integral_eq-a1`
- Child key: `weighted_transfer`
- Declaration: `Submission.slicing_im_ll_twl_cie_weighted_transfer`
- Exact Lean type: `∀ (X Y E : Type) [MeasurableSpace X] [MeasurableSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (μ : Measure X) (ν : Measure Y) (Φ : X → Y) (J : X → ℝ) (F : Y → E), AEMeasurable Φ μ → AEMeasurable J μ → (∀ x, 0 ≤ J x) → (∀ g : Y → ℝ≥0∞, Measurable g → ∫⁻ y, g y ∂ν = ∫⁻ x, g (Φ x) * ENNReal.ofReal (J x) ∂μ) → Integrable F ν → Integrable (fun x => J x • F (Φ x)) μ ∧ ∫ y, F y ∂ν = ∫ x, J x • F (Φ x) ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
