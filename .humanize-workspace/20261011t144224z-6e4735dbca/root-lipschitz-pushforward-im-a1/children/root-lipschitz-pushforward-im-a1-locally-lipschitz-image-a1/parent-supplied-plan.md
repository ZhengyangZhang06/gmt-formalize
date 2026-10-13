# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.locally_lipschitz_image-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-locally-lipschitz-image-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1`
- Child key: `locally_lipschitz_image`
- Declaration: `Submission.lpf_locally_lipschitz_image`
- Exact Lean type: `∀ (P Q n : ℕ) (U : Set (Eucl P)) (f : Eucl P → Eucl Q), LocallyLipschitzOn U f → (∀ Z ⊆ U, (μHE[n] : Measure (Eucl P)) Z = 0 → (μHE[n] : Measure (Eucl Q)) (f '' Z) = 0) ∧ ∀ A ⊆ U, NullMeasurableSet A (μHE[n] : Measure (Eucl P)) → SigmaFinite ((μHE[n] : Measure (Eucl P)).restrict A) → NullMeasurableSet (f '' A) (μHE[n] : Measure (Eucl Q))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
