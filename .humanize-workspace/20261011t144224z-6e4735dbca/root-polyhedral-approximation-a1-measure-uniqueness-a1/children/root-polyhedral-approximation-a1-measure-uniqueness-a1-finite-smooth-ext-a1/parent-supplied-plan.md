# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.polyhedral_approximation-a1.measure_uniqueness-a1.finite_smooth_ext-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1-measure-uniqueness-a1-finite-smooth-ext-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.polyhedral_approximation-a1.measure_uniqueness-a1`
- Child key: `finite_smooth_ext`
- Declaration: `Submission.polyhedral_approx_finite_smooth_ext`
- Exact Lean type: `∀ (P : ℕ) (ν₁ ν₂ : Measure (Eucl P)), IsFiniteMeasure ν₁ → IsFiniteMeasure ν₂ → ∀ O : Set (Eucl P), IsOpen O → (∀ ψ : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ O → ∫ x, ψ x ∂ν₁ = ∫ x, ψ x ∂ν₂) → ∀ b : Eucl P → ℝ, (∀ x, x ∉ O → b x = 0) → ∫ x, b x ∂ν₁ = ∫ x, b x ∂ν₂`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
