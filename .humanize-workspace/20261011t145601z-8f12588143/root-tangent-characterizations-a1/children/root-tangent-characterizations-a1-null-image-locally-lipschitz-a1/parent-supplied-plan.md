# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_characterizations-a1.null_image_locally_lipschitz-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-tangent-characterizations-a1-null-image-locally-lipschitz-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_characterizations-a1`
- Child key: `null_image_locally_lipschitz`
- Declaration: `Submission.hausdorffMeasure_image_null_of_locallyLipschitzOn`
- Exact Lean type: `∀ (n N : ℕ) (V Z : Set (Rn n)) (ψ : Rn n → Rn N), IsOpen V → LocallyLipschitzOn V ψ → Z ⊆ V → volume Z = 0 → μHE[n] (ψ '' Z) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
