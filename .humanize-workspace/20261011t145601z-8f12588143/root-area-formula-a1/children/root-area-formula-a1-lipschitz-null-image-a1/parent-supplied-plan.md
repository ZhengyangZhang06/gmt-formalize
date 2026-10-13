# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.area_formula-a1.lipschitz_null_image-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-area-formula-a1-lipschitz-null-image-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.area_formula-a1`
- Child key: `lipschitz_null_image`
- Declaration: `Submission.areaFormula_image_null_of_locallyLipschitzOn`
- Exact Lean type: `∀ (N P n : ℕ) (U Z : Set (Rn N)) (f : Rn N → Rn P), LocallyLipschitzOn U f → Z ⊆ U → μHE[n] Z = 0 → μHE[n] (f '' Z) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
