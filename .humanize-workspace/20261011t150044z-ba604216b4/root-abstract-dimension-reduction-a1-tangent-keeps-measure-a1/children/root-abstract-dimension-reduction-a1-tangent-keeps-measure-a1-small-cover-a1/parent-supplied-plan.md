# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.abstract_dimension_reduction-a1.tangent_keeps_measure-a1.small_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1-tangent-keeps-measure-a1-small-cover-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.abstract_dimension_reduction-a1.tangent_keeps_measure-a1`
- Child key: `small_cover`
- Declaration: `Submission.adr_eventually_subset_small_cover`
- Exact Lean type: `∀ (P : ℕ) (ℓ : ℝ) (S : Set (Euclid P)) (Ts : ℕ → Set (Euclid P)) (ε : ℝ≥0∞), 0 < ℓ → IsClosed S → μH[ℓ] (S ∩ ball (0 : Euclid P) 1) = 0 → 0 < ε → (∀ η : ℝ, 0 < η → ∃ k₀ : ℕ, ∀ k ≥ k₀, ball (0 : Euclid P) 1 ∩ Ts k ⊆ {x | ∃ z ∈ S, dist x z < η}) → ∃ (U : ℕ → Set (Euclid P)) (k₀ : ℕ), ∑' j, Metric.ediam (U j) ^ ℓ < ε ∧ ∀ k ≥ k₀, ball (0 : Euclid P) (1 / 2) ∩ Ts k ⊆ ⋃ j, U j`

## Sibling prerequisites

- `root.abstract_dimension_reduction-a1.tangent_keeps_measure-a1.null_open_cover-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
