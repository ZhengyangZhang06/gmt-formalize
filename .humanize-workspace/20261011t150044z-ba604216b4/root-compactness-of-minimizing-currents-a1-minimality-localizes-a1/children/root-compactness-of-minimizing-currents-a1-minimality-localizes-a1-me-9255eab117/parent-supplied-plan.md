# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.minimality_localizes-a1.measure_agree_on_borel-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-minimality-localizes-a1-me-9255eab117/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.minimality_localizes-a1`
- Child key: `measure_agree_on_borel`
- Declaration: `Submission.cmc_ml_measure_eq_of_eq_on_open_subsets`
- Exact Lean type: `∀ (P : ℕ) (O : Set (Euclid P)) (μ ν : Measure (Euclid P)), IsOpen O → (∀ C : Set (Euclid P), IsCompact C → C ⊆ O → μ C ≠ ∞) → (∀ G : Set (Euclid P), IsOpen G → G ⊆ O → μ G = ν G) → ∀ A : Set (Euclid P), MeasurableSet A → A ⊆ O → μ A = ν A`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
