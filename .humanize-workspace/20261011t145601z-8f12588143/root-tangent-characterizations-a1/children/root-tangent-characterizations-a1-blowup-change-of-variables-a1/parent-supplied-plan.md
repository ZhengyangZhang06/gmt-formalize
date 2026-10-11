# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_characterizations-a1.blowup_change_of_variables-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-tangent-characterizations-a1-blowup-change-of-variables-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_characterizations-a1`
- Child key: `blowup_change_of_variables`
- Declaration: `Submission.setIntegral_blowUpMap_image`
- Exact Lean type: `∀ (n N : ℕ) (x : Rn N) (r : ℝ) (A : Set (Rn N)) (g : Rn N → ℝ), 0 < r → ∫ y in blowUpMap x r '' A, g y ∂μHE[n] = (r ^ n)⁻¹ * ∫ z in A, g (blowUpMap x r z) ∂μHE[n]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
