# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.canonical_representatives-a1.canonical_pair_weight-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-canonical-representatives-a1-canonical-pair-weight-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.canonical_representatives-a1`
- Child key: `canonical_pair_weight`
- Declaration: `Submission.canonicalCarrier_rectifiablePair_weight`
- Exact Lean type: `ApproxTangentAE → ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)), 0 < n → IsOpen U → IsFiniteMeasureOnCompacts V.weight → (∀ ξ ∈ U, V.HasDensityAt ξ (V.density ξ)) → IsRectifiablePair n (V.canonicalCarrier U) V.density ∧ pairWeight n (V.canonicalCarrier U) V.density = V.weight.restrict U`

## Sibling prerequisites

- `root.canonical_representatives-a1.hausdorff_null_density-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
