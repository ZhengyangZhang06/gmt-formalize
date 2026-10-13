# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.mass_representation-a1.null_sets-a1.compact_to_general-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-nul-64c4d53245/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.null_sets-a1`
- Child key: `compact_to_general`
- Declaration: `Submission.cmr_null_of_compact_null`
- Exact Lean type: `∀ (P : ℕ) (U : Set (Euclid P)) (μ ν : Measure (Euclid P)), IsOpen U → μ Uᶜ = 0 → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ C : Set (Euclid P), IsCompact C → C ⊆ U → ν C = 0 → μ C = 0) → ∀ E : Set (Euclid P), ν E = 0 → μ E = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
