# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1.measurable_chart_differential-a1.countable_glue-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-me-37e9d69edf/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1.measurable_chart_differential-a1`
- Child key: `countable_glue`
- Declaration: `Submission.lpf_tde_mcd_countable_glue`
- Exact Lean type: `∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] [Zero Y] (S : ℕ → Set X) (G : ℕ → X → Y), (∀ j, MeasurableSet (S j)) → (∀ j, Measurable (G j)) → ∃ L : X → Y, Measurable L ∧ (∀ x, x ∉ (⋃ j, S j) → L x = 0) ∧ ∀ x ∈ (⋃ j, S j), ∃ j, x ∈ S j ∧ L x = G j x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
