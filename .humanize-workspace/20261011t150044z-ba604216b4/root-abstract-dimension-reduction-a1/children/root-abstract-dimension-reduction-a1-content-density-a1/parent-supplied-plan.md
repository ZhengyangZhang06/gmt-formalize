# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.abstract_dimension_reduction-a1.content_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1-content-density-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.abstract_dimension_reduction-a1`
- Child key: `content_density`
- Declaration: `Submission.adr_content_density`
- Exact Lean type: `∀ (P : ℕ) (ℓ : ℝ) (A : Set (Euclid P)), 0 < ℓ → MeasurableSet A → Bornology.IsBounded A → μH[ℓ] {x | x ∈ A ∧ ¬ ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧ ∀ C : ℕ → Set (Euclid P), A ∩ ball x ρ ⊆ ⋃ j, C j → ENNReal.ofReal ρ ^ ℓ ≤ 2 * ∑' j, Metric.ediam (C j) ^ ℓ} = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
