# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.polyhedral_approximation-a1.measure_uniqueness-a1.integrable_smooth_ext-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1-measure-uniqueness-a1-integrable-smooth-ext-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.polyhedral_approximation-a1.measure_uniqueness-a1`
- Child key: `integrable_smooth_ext`
- Declaration: `Submission.polyhedral_approx_integrable_smooth_ext`
- Exact Lean type: `∀ (P : ℕ) (μ₁ μ₂ : Measure (Eucl P)) (g₁ g₂ : Eucl P → ℝ), Integrable g₁ μ₁ → Integrable g₂ μ₂ → ∀ O : Set (Eucl P), IsOpen O → (∀ ψ : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ O → ∫ x, ψ x * g₁ x ∂μ₁ = ∫ x, ψ x * g₂ x ∂μ₂) → ∀ b : Eucl P → ℝ, Measurable b → (∃ C : ℝ, ∀ x, |b x| ≤ C) → (∀ x, x ∉ O → b x = 0) → ∫ x, b x * g₁ x ∂μ₁ = ∫ x, b x * g₂ x ∂μ₂`

## Sibling prerequisites

- `root.polyhedral_approximation-a1.measure_uniqueness-a1.density_split-a1`
- `root.polyhedral_approximation-a1.measure_uniqueness-a1.finite_smooth_ext-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
