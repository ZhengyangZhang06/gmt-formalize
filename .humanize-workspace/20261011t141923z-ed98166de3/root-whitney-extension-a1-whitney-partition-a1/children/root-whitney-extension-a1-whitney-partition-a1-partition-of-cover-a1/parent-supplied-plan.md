# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.whitney_extension-a1.whitney_partition-a1.partition_of_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-whitney-extension-a1-whitney-partition-a1-partition-of-cover-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.whitney_extension-a1.whitney_partition-a1`
- Child key: `partition_of_cover`
- Declaration: `Submission.whitney_partition_of_finite_overlap_cover`
- Exact Lean type: `∀ (n : ℕ) (A J : Set (Rn n)) (N : ℕ), IsClosed A → A.Nonempty → J ⊆ Aᶜ → (∀ x ∉ A, ∃ s ∈ J, ‖x - s‖ ≤ 5 * (min 1 (Metric.infDist s A) / 20)) → (∀ x ∉ A, Set.Finite {s : Rn n | s ∈ J ∧ ‖x - s‖ < 10 * (min 1 (Metric.infDist s A) / 20)} ∧ Set.ncard {s : Rn n | s ∈ J ∧ ‖x - s‖ < 10 * (min 1 (Metric.infDist s A) / 20)} ≤ N) → (∀ x ∉ A, Set.Finite {s : Rn n | s ∈ J ∧ ∃ z : Rn n, ‖z - s‖ < 10 * (min 1 (Metric.infDist s A) / 20) ∧ ‖z - x‖ < min 1 (Metric.infDist x A) / 20}) → ∃ (ι : Type) (φ : ι → Rn n → ℝ) (p : ι → Rn n) (C M : ℝ), 0 ≤ C ∧ 0 ≤ M ∧ (∀ i, p i ∈ A) ∧ (∀ i, ∀ x ∉ A, ContDiffAt ℝ 1 (φ i) x) ∧ (∀ i, ∀ x ∉ A, 0 ≤ φ i x) ∧ (∀ x ∉ A, ∃ s : Finset ι, ∃ V ∈ 𝓝 x, ∀ i ∉ s, ∀ y ∈ V, φ i y = 0) ∧ (∀ x ∉ A, ∑ᶠ i, φ i x = 1) ∧ (∀ i, ∀ x ∉ A, φ i x ≠ 0 → ‖x - p i‖ ≤ C * Metric.infDist x A) ∧ (∀ x ∉ A, Metric.infDist x A ≤ 1 → ∑ᶠ i, ‖fderiv ℝ (φ i) x‖ ≤ M / Metric.infDist x A)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
