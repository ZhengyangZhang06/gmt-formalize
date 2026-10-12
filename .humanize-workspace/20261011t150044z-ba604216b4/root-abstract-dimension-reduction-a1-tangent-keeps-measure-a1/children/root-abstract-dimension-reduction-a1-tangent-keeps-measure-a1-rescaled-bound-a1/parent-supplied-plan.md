# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.abstract_dimension_reduction-a1.tangent_keeps_measure-a1.rescaled_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1-tangent-keeps-measure-a1-rescaled-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.abstract_dimension_reduction-a1.tangent_keeps_measure-a1`
- Child key: `rescaled_bound`
- Declaration: `Submission.adr_rescaled_content_lower_bound`
- Exact Lean type: `∀ (P : ℕ) (ℓ : ℝ) (A : Set (Euclid P)) (x : Euclid P) (ρ : ℝ) (U : ℕ → Set (Euclid P)), 0 < ℓ → 0 < ρ → (∀ C : ℕ → Set (Euclid P), A ∩ ball x ρ ⊆ ⋃ j, C j → ENNReal.ofReal ρ ^ ℓ ≤ 2 * ∑' j, Metric.ediam (C j) ^ ℓ) → (∀ z : Euclid P, x + (2 * ρ) • z ∈ A → ‖z‖ < 1 / 2 → z ∈ ⋃ j, U j) → (2 : ℝ≥0∞) ^ (-ℓ) / 8 ≤ ∑' j, Metric.ediam (U j) ^ ℓ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
