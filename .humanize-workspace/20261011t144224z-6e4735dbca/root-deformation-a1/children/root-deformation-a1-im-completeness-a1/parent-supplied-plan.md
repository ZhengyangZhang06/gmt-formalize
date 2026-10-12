# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_completeness-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-completeness-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1`
- Child key: `im_completeness`
- Declaration: `Submission.deformation_im_completeness`
- Exact Lean type: `∀ (N k : ℕ) (T : GeometricCurrentOn (univ : Set (Eucl N)) k) (Tj : ℕ → GeometricCurrentOn (univ : Set (Eucl N)) k), (∀ j, IsIntegerMultiplicity (Tj j)) → (∀ ε : ℝ≥0∞, 0 < ε → ∃ J : ℕ, ∀ j, J ≤ j → ∀ D : GeometricCurrentOn (univ : Set (Eucl N)) k, (∀ ω, D ω = T ω - Tj j ω) → D.mass < ε) → IsIntegerMultiplicity T`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
