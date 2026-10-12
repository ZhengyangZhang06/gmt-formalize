# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.whitney_extension-a1.whitney_partition-a1.cover_finite_overlap-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-whitney-extension-a1-whitney-partition-a1-cover-finite-overlap-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.whitney_extension-a1.whitney_partition-a1`
- Child key: `cover_finite_overlap`
- Declaration: `Submission.whitney_cover_finite_overlap`
- Exact Lean type: `∀ (n : ℕ) (A : Set (Rn n)), IsClosed A → A.Nonempty → ∃ (J : Set (Rn n)) (N : ℕ), J ⊆ Aᶜ ∧ (∀ x ∉ A, ∃ s ∈ J, ‖x - s‖ ≤ 5 * (min 1 (Metric.infDist s A) / 20)) ∧ (∀ x ∉ A, Set.Finite {s : Rn n | s ∈ J ∧ ‖x - s‖ < 10 * (min 1 (Metric.infDist s A) / 20)} ∧ Set.ncard {s : Rn n | s ∈ J ∧ ‖x - s‖ < 10 * (min 1 (Metric.infDist s A) / 20)} ≤ N) ∧ (∀ x ∉ A, Set.Finite {s : Rn n | s ∈ J ∧ ∃ z : Rn n, ‖z - s‖ < 10 * (min 1 (Metric.infDist s A) / 20) ∧ ‖z - x‖ < min 1 (Metric.infDist x A) / 20})`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
