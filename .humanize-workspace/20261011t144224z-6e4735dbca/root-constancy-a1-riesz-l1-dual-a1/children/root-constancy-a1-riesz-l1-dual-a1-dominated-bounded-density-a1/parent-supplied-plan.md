# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.constancy-a1.riesz_l1_dual-a1.dominated_bounded_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-riesz-l1-dual-a1-dominated-bounded-density-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.constancy-a1.riesz_l1_dual-a1`
- Child key: `dominated_bounded_density`
- Declaration: `Submission.constancy_riesz_bounded_density_of_dominated_additive`
- Exact Lean type: `∀ {α : Type} [MeasurableSpace α] (μ : Measure α), IsFiniteMeasure μ → ∀ (ν : Set α → ℝ) (C : ℝ), 0 ≤ C → (∀ A B : Set α, MeasurableSet A → MeasurableSet B → Disjoint A B → ν (A ∪ B) = ν A + ν B) → (∀ A : Set α, MeasurableSet A → |ν A| ≤ C * μ.real A) → ∃ θ : α → ℝ, Measurable θ ∧ (∀ x, |θ x| ≤ C) ∧ ∀ A : Set α, MeasurableSet A → ν A = ∫ x in A, θ x ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
