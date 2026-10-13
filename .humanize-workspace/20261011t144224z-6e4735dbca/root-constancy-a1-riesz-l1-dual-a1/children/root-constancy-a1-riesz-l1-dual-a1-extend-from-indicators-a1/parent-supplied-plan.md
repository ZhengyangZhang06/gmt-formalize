# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.constancy-a1.riesz_l1_dual-a1.extend_from_indicators-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-riesz-l1-dual-a1-extend-from-indicators-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.constancy-a1.riesz_l1_dual-a1`
- Child key: `extend_from_indicators`
- Declaration: `Submission.constancy_riesz_eq_integral_mul_of_indicator_eq`
- Exact Lean type: `∀ {α : Type} [MeasurableSpace α] (μ : Measure α), IsFiniteMeasure μ → ∀ (F : (α → ℝ) → ℝ) (C : ℝ), (∀ f g : α → ℝ, Integrable f μ → Integrable g μ → F (f + g) = F f + F g) → (∀ (c : ℝ) (f : α → ℝ), Integrable f μ → F (c • f) = c * F f) → (∀ f : α → ℝ, Integrable f μ → |F f| ≤ C * ∫ x, |f x| ∂μ) → ∀ (θ : α → ℝ) (M : ℝ), Measurable θ → (∀ x, |θ x| ≤ M) → (∀ A : Set α, MeasurableSet A → F (A.indicator 1) = ∫ x in A, θ x ∂μ) → ∀ f : α → ℝ, Integrable f μ → F f = ∫ x, f x * θ x ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
