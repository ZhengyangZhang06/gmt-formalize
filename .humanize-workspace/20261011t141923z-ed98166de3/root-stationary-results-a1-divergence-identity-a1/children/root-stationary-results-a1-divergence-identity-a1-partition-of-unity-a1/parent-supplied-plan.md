# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.stationary_results-a1.divergence_identity-a1.partition_of_unity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-divergence-identity-a1-partition-of-unity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.stationary_results-a1.divergence_identity-a1`
- Child key: `partition_of_unity`
- Declaration: `Submission.exists_finite_contDiff_partition_near_compact`
- Exact Lean type: `∀ (N : ℕ) (C : Set (Rn N)) (P : Set (Rn N) → Prop), IsCompact C → (∀ y ∈ C, ∃ U : Set (Rn N), IsOpen U ∧ y ∈ U ∧ P U) → ∃ (p : ℕ) (ζ : Fin p → Rn N → ℝ) (O : Set (Rn N)), IsOpen O ∧ C ⊆ O ∧ (∀ z ∈ O, ∑ q, ζ q z = 1) ∧ ∀ q, ContDiff ℝ 1 (ζ q) ∧ HasCompactSupport (ζ q) ∧ ∃ U : Set (Rn N), P U ∧ tsupport (ζ q) ⊆ U`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
