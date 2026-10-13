# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_completeness-a1.l1_cauchy_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-completeness-a1-l1-cauchy-limit-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.im_completeness-a1`
- Child key: `l1_cauchy_limit`
- Declaration: `Submission.imc_ae_tendsto_of_summable_lintegral`
- Exact Lean type: `∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (E : Type) [NormedAddCommGroup E] [CompleteSpace E] (f : ℕ → X → E), (∀ n, AEStronglyMeasurable (f n) μ) → (∑' n, ∫⁻ x, ‖f (n + 1) x - f n x‖ₑ ∂μ) ≠ ∞ → ∃ g : X → E, AEStronglyMeasurable g μ ∧ (∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) ∧ Tendsto (fun n => ∫⁻ x, ‖f n x - g x‖ₑ ∂μ) atTop (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
