# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gauss_green-a1.variation_formula-a1.open_outer_approx-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-gauss-green-a1-variation-formula-a1-open-outer-approx-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.gauss_green-a1.variation_formula-a1`
- Child key: `open_outer_approx`
- Declaration: `Submission.gaussGreenVar_exists_isOpen_superset_measure_sdiff_lt`
- Exact Lean type: `∀ (N : ℕ) (O K : Set (Rn N)) (μ : Measure (Rn N)), IsOpen O → IsCompact K → K ⊆ O → (∀ L : Set (Rn N), IsCompact L → L ⊆ O → μ L < ∞) → ∀ ε : ℝ≥0∞, 0 < ε → ∃ V : Set (Rn N), IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ μ V < ∞ ∧ μ (V \ K) < ε`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
