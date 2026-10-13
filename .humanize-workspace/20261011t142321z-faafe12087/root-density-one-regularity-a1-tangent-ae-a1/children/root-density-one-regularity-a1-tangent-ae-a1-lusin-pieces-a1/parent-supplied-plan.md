# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_regularity-a1.tangent_ae-a1.lusin_pieces-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1-tangent-ae-a1-lusin-pieces-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_regularity-a1.tangent_ae-a1`
- Child key: `lusin_pieces`
- Declaration: `Submission.tae_mult_lusin_compact_pieces`
- Exact Lean type: `∀ {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U), IsOpen U → ∃ C : ℕ → Set (Amb n ℓ), (∀ i, IsCompact (C i) ∧ C i ⊆ V.carrier ∧ ContinuousOn V.mult (C i)) ∧ (μHE[n] : Measure (Amb n ℓ)) (V.carrier \ ⋃ i, C i) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
