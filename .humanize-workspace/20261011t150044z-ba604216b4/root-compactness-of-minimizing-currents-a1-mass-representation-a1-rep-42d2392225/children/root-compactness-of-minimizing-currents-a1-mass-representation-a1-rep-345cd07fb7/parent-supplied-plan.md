# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.mass_representation-a1.representation_core-a1.open_exhaustion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-rep-345cd07fb7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.representation_core-a1`
- Child key: `open_exhaustion`
- Declaration: `Submission.cmrc_measure_le_of_compactlyContained`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)) (U W : Set (Euclid P)) (m : ℝ≥0∞), IsOpen U → IsOpen W → μ Uᶜ = 0 → (∀ W' : Set (Euclid P), IsOpen W' → CompactlyContained W' U → W' ⊆ W → μ W' ≤ m) → μ W ≤ m`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
