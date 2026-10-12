# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_semicontinuity-a1.lower_density_ae-a1.thickening_rel_compact-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-density-semicontinuity-a1-lower-density-ae-a1-thickening-rel-compact-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_semicontinuity-a1.lower_density_ae-a1`
- Child key: `thickening_rel_compact`
- Declaration: `Submission.exists_thickening_isRelCompactOpenIn`
- Exact Lean type: `∀ (N : ℕ) (U W : Set (Euclidean N)), IsOpen U → IsRelCompactOpenIn W U → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ IsRelCompactOpenIn (thickening ρ₀ W) U`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
