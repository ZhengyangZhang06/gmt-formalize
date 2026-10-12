# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_combination-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-combination-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1`
- Child key: `im_combination`
- Declaration: `Submission.deformation_im_combination`
- Exact Lean type: `∀ (N k : ℕ) (X Y Z : GeometricCurrentOn (univ : Set (Eucl N)) k) (a b : ℤ), IsIntegerMultiplicity X → IsIntegerMultiplicity Y → (∀ ω, Z ω = a * X ω + b * Y ω) → IsIntegerMultiplicity Z`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
