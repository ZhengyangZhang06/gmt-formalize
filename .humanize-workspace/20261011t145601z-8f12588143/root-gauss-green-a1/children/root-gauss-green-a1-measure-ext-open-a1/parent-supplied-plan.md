# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gauss_green-a1.measure_ext_open-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-gauss-green-a1-measure-ext-open-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.gauss_green-a1`
- Child key: `measure_ext_open`
- Declaration: `Submission.gaussGreenRep_measure_eq_of_open_eq`
- Exact Lean type: `∀ (N : ℕ) (U : Set (Rn N)) (μ μ' : Measure (Rn N)), IsOpen U → μ Uᶜ = 0 → μ' Uᶜ = 0 → (∀ K : Set (Rn N), IsCompact K → K ⊆ U → μ K < ∞) → (∀ O : Set (Rn N), IsOpen O → O ⊆ U → μ O = μ' O) → μ = μ'`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
