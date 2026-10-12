# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiability-a1.projection_null-a1.mass_off_compact-a1.nvector_pairing_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1-mass-off-compact-a1-nvector-921e87f034/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiability-a1.projection_null-a1.mass_off_compact-a1`
- Child key: `nvector_pairing_bound`
- Declaration: `Submission.rpn_moc_abs_nvector_apply_le`
- Exact Lean type: `∀ (P n : ℕ) (w : NVector (Eucl P) n) (θ : Covector (Eucl P) n), ∑ β : SimonMultiIndex n P, (euclideanNVectorCoordinate w β) ^ 2 = 1 → |w θ| ≤ ∑ β : SimonMultiIndex n P, |euclideanCovectorCoordinate θ β|`

## Sibling prerequisites

- `root.compactness_mass_bounds-a1.covector_expansion-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
