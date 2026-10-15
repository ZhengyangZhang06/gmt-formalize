# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.local_comparison-a1.compact_outer_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1-compac-a4168491cb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.local_comparison-a1`
- Child key: `compact_outer_bound`
- Declaration: `Submission.lcmp_measure_le_add_of_open_nhds`
- Exact Lean type: `∀ (P : ℕ) (U E : Set (Euclid P)) (μ ν : Measure (Euclid P)) (c : ℝ≥0∞), IsOpen U → IsCompact E → E ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ν K < ∞) → (∀ G : Set (Euclid P), IsOpen G → E ⊆ G → CompactlyContained G U → μ G ≤ ν G + c) → μ E ≤ ν E + c`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
