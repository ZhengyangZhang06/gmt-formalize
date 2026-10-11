# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.stationary_results-a1.divergence_identity-a1.partition_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-divergence-identity-a1-partition-identity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.stationary_results-a1.divergence_identity-a1`
- Child key: `partition_identity`
- Declaration: `Submission.tangentialDivergence_add_inner_eq_sum_partition`
- Exact Lean type: `∀ (N p : ℕ) (M S O : Set (Rn N)) (Y : Rn N → Rn N) (ζ : Fin p → Rn N → ℝ), ContDiff ℝ 1 Y → (∀ q, ContDiff ℝ 1 (ζ q)) → IsClosed S → (∀ x ∉ S, Y x = 0) → IsOpen O → M ∩ S ⊆ O → (∀ z ∈ O, ∑ q, ζ q z = 1) → ∀ y ∈ M, tangentialDivergence M Y y + inner ℝ (Y y) (meanCurvature M y) = ∑ q, (tangentialDivergence M (fun z ↦ ζ q z • Y z) y + inner ℝ (ζ q y • Y y) (meanCurvature M y))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
