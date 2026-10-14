# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_support-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-support-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1`
- Child key: `slice_support`
- Declaration: `Submission.slicing_support_subset`
- Exact Lean type: `∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1), ∀ (f : Eucl P → ℝ) (L : ℝ≥0), LipschitzOnWith L f U → ∀ (t : ℝ) (S : GeometricCurrentOn U m), IsSlice T f t S → S.support ⊆ T.support ∩ {x | f x = t}`

## Sibling prerequisites

- `root.slicing-a1.representation_unique-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
