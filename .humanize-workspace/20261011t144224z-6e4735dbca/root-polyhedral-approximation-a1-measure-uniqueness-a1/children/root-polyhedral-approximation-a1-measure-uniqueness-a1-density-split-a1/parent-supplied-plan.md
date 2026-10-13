# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.polyhedral_approximation-a1.measure_uniqueness-a1.density_split-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1-measure-uniqueness-a1-density-split-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.polyhedral_approximation-a1.measure_uniqueness-a1`
- Child key: `density_split`
- Declaration: `Submission.polyhedral_approx_density_split`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Eucl P)) (g : Eucl P → ℝ), Integrable g μ → ∃ νpos νneg : Measure (Eucl P), IsFiniteMeasure νpos ∧ IsFiniteMeasure νneg ∧ ∀ b : Eucl P → ℝ, Measurable b → (∃ C : ℝ, ∀ x, |b x| ≤ C) → ∫ x, b x ∂νpos - ∫ x, b x ∂νneg = ∫ x, b x * g x ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
