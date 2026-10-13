# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gauss_green-a1.variation_formula-a1.compact_inner_approx-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-gauss-green-a1-variation-formula-a1-compact-inner-approx-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.gauss_green-a1.variation_formula-a1`
- Child key: `compact_inner_approx`
- Declaration: `Submission.gaussGreenVar_measure_isOpen_le_of_isCompact`
- Exact Lean type: `∀ (N : ℕ) (O : Set (Rn N)) (μ : Measure (Rn N)) (c : ℝ≥0∞), IsOpen O → (∀ K : Set (Rn N), IsCompact K → K ⊆ O → μ K ≤ c) → μ O ≤ c`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
