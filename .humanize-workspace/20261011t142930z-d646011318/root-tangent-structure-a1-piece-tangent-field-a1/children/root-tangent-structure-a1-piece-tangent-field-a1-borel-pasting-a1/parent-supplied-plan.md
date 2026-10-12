# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_structure-a1.piece_tangent_field-a1.borel_pasting-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-tangent-field-a1-borel-pasting-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_structure-a1.piece_tangent_field-a1`
- Child key: `borel_pasting`
- Declaration: `Submission.ts_stronglyMeasurable_paste_continuousOn`
- Exact Lean type: `∀ (n ℓ : ℕ) (N : ℕ → Set (Ambient n ℓ)) (G : ℕ → Ambient n ℓ → (Ambient n ℓ →L[ℝ] Ambient n ℓ)), (∀ i, MeasurableSet (N i)) → (∀ i, ContinuousOn (G i) (N i)) → ∃ g : Ambient n ℓ → (Ambient n ℓ →L[ℝ] Ambient n ℓ), StronglyMeasurable g ∧ ∀ i, ∀ y ∈ N i, (∀ j < i, y ∉ N j) → g y = G i y`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
