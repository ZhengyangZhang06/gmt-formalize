# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.im_lincomb-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-lincomb-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1`
- Child key: `im_lincomb`
- Declaration: `Submission.fiw_im_lincomb`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T₁ T₂ S : GeometricCurrentOn U n) (a b : ℤ), IsIntegerMultiplicity T₁ → IsIntegerMultiplicity T₂ → (∀ ω, S ω = (a : ℝ) * T₁ ω + (b : ℝ) * T₂ ω) → IsIntegerMultiplicity S`

## Sibling prerequisites

- `root.flat_iff_weak-a1.im_series-a1`
- `root.flat_iff_weak-a1.im_mass_formula-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
