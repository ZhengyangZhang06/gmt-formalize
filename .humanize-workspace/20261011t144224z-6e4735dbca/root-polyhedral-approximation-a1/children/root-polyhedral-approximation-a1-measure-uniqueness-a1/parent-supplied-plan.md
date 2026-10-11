# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.polyhedral_approximation-a1.measure_uniqueness-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1-measure-uniqueness-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.polyhedral_approximation-a1`
- Child key: `measure_uniqueness`
- Declaration: `Submission.polyhedral_approx_measure_uniqueness`
- Exact Lean type: `∀ (P : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (μ₁ μ₂ : Measure (Eucl P)) (g₁ g₂ : Eucl P → ℝ), (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn g₁ K μ₁ ∧ IntegrableOn g₂ K μ₂) → (∀ ψ : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ U → ∫ x, ψ x * g₁ x ∂μ₁ = ∫ x, ψ x * g₂ x ∂μ₂) → ∀ A : Set (Eucl P), MeasurableSet A → ∀ u : Eucl P → ℝ, Continuous u → HasCompactSupport u → tsupport u ⊆ U → ∫ x in A, u x * g₁ x ∂μ₁ = ∫ x in A, u x * g₂ x ∂μ₂`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
